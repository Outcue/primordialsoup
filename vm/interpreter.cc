// Copyright (c) 2016, the Newspeak project authors. Please see the AUTHORS file
// for details. All rights reserved. Use of this source code is governed by a
// BSD-style license that can be found in the LICENSE file.

#include "vm/interpreter.h"

#include "vm/heap.h"
#include "vm/isolate.h"
#include "vm/math.h"
#include "vm/os.h"
#include "vm/primitives.h"

#define H heap_
#define nil nil_

namespace psoup {

// Frame layout:
//
// | ...                       | (high addresses / stack base)
// | message receiver          |
// | argument 1                |
// | ...                       |
// | argument N                |
// | ------------------------- |
// | saved IP / base sender    |
// | saved FP / 0              |  <= fp
// | flags                     |
// | method                    |
// | activation / 0            |
// | method receiver           |
// | temporary 1               |
// | ...                       |
// | temporary N               |  <= sp
// | ...                       | (low addresses / stack limit)
//
// Note the message receiver is different from the method receiver in the case
// of closure activations. The message receiver is the closure, and the method
// receiver is the receiver of the closure's home activation (i.e., the binding
// of `self`).
//
// With saved FPs and frame flags being SmallIntegers, the only GC-unsafe values
// on the stack are the saved IPs. Before GC, we swap the saved IPs with BCIs,
// and after GC we swap back. This allows the GC to simply visit the whole
// stack, and also accounts for bytecode arrays moving during GC.

static intptr_t FlagsNumArgs(SmallInteger flags) {
  return flags->value() >> 1;
}
static bool FlagsIsClosure(SmallInteger flags) {
  return (flags->value() & 1) != 0;
}
static SmallInteger MakeFlags(intptr_t num_args, bool is_closure) {
  return SmallInteger::New((num_args << 1) | (is_closure ? 1 : 0));
}

static const uint8_t* FrameSavedIP(Object* fp) {
  return reinterpret_cast<const uint8_t*>(static_cast<uword>(fp[1]));
}
static const uint8_t** FrameSavedIPSlot(Object* fp) {
  return reinterpret_cast<const uint8_t**>((uword)&fp[1]);
}

static Object* FrameSavedFP(Object* fp) {
  return reinterpret_cast<Object*>(static_cast<uword>(fp[0]));
}

static SmallInteger FrameFlags(Object* fp) {
  return static_cast<SmallInteger>(fp[-1]);
}

static Method FrameMethod(Object* fp) { return static_cast<Method>(fp[-2]); }

static Activation FrameActivation(Object* fp) {
  return static_cast<Activation>(fp[-3]);
}
static void FrameActivationPut(Object* fp, Activation activation) {
  fp[-3] = activation;
}

static Object FrameReceiver(Object* fp) { return fp[-4]; }

static Object FrameTemp(Object* fp, intptr_t index) {
  intptr_t num_args = FlagsNumArgs(FrameFlags(fp));
  if (index < num_args) {
    return fp[1 + num_args - index];
  } else {
    return fp[-5 - (index - num_args)];
  }
}
static void FrameTempPut(Object* fp, intptr_t index, Object value) {
  intptr_t num_args = FlagsNumArgs(FrameFlags(fp));
  if (index < num_args) {
    FATAL("Assignment to parameter");
  } else {
    fp[-5 - (index - num_args)] = value;
  }
}

static Object* FrameSavedSP(Object* fp) {
  intptr_t num_args = FlagsNumArgs(FrameFlags(fp));
  return fp + 3 + num_args;
}

static intptr_t FrameNumLocals(Object* fp, Object* sp) {
  return &fp[-4] - sp;
}

static Activation FrameBaseSender(Object* fp) {
  ASSERT(FrameSavedFP(fp) == 0);
  return static_cast<Activation>(fp[1]);
}

Interpreter::Interpreter(Heap* heap, Isolate* isolate) :
    ip_(nullptr),
    sp_(nullptr),
    fp_(nullptr),
    stack_base_(nullptr),
    stack_limit_(nullptr),
    nil_(nullptr),
    false_(nullptr),
    true_(nullptr),
    object_store_(nullptr),
    heap_(heap),
    isolate_(isolate),
    environment_(nullptr) {
  heap->InitializeInterpreter(this);

  stack_limit_ = reinterpret_cast<Object*>(malloc(kStackSize));
  stack_base_ = stack_limit_ + kStackSlots;
  sp_ = stack_base_;
  checked_stack_limit_ =
      stack_limit_ + (sizeof(Activation::Layout) / sizeof(Object));

     PopulateFunctionTable();

#if defined(DEBUG)
  for (intptr_t i = 0; i < kStackSlots; i++) {
    stack_limit_[i] = static_cast<Object>(kUninitializedWord);
  }
#endif
}


Interpreter::~Interpreter() {
  free(stack_limit_);
}

void Interpreter::PushLiteralVariable(intptr_t offset) {
  // Not used in Newspeak, except by the implementation of eventual sends.
  // TODO(rmacnak): Add proper eventual send bytecode.
  Push(object_store()->message_loop());
}

void Interpreter::PushTemporary(intptr_t offset) {
  Object temp = FrameTemp(fp_, offset);
  Push(temp);
}

void Interpreter::PushRemoteTemp(intptr_t vector_offset, intptr_t offset) {
  Object vector = FrameTemp(fp_, vector_offset);
  ASSERT(vector->IsArray());
  Object temp = static_cast<Array>(vector)->element(offset);
  Push(temp);
}


void Interpreter::StoreIntoTemporary(intptr_t offset) {
  Object top = Stack(0);
  FrameTempPut(fp_, offset, top);
}


void Interpreter::StoreIntoRemoteTemp(intptr_t vector_offset, intptr_t offset) {
  Object top = Stack(0);
  Object vector = FrameTemp(fp_, vector_offset);
  ASSERT(vector->IsArray());
  static_cast<Array>(vector)->set_element(offset, top);
}


void Interpreter::PopIntoTemporary(intptr_t offset) {
  Object top = Pop();
  FrameTempPut(fp_, offset, top);
}


void Interpreter::PopIntoRemoteTemp(intptr_t vector_offset, intptr_t offset) {
  Object top = Pop();
  Object vector = FrameTemp(fp_, vector_offset);
  ASSERT(vector->IsArray());
  static_cast<Array>(vector)->set_element(offset, top);
}


void Interpreter::PushLiteral(intptr_t offset) {
  Method method = FrameMethod(fp_);
  Object literal;
  if (offset == method->literals()->Size() + 1) {
    // Hack. When transforming from Squeak CompiledMethod, we drop
    // the last two literals (the selector/AdditionalMethodState and
    // the mixin class association) because we put them in the Method
    // instead of the literal array. The mixin class associtation is
    // accessed by nested class accessors.
    literal = method->mixin();
  } else {
    ASSERT((offset >= 0) && (offset < method->literals()->Size()));
    literal = method->literals()->element(offset);
  }
  Push(literal);
}

void Interpreter::PushEnclosingObject(intptr_t depth) {
  ASSERT(depth > 0);  // Compiler should have used push receiver.

  Object enclosing_object = FrameReceiver(fp_);
  AbstractMixin target_mixin = FrameMethod(fp_)->mixin();
  intptr_t count = 0;
  while (count < depth) {
    count++;
    Behavior mixin_app = FindApplicationOf(target_mixin,
                                            enclosing_object->Klass(H));
    enclosing_object = mixin_app->enclosing_object();
    target_mixin = target_mixin->enclosing_mixin();
  }
  Push(enclosing_object);
}


void Interpreter::PushNewArrayWithElements(intptr_t size) {
  Array result = H->AllocateArray(size);  // SAFEPOINT
  for (intptr_t i = 0; i < size; i++) {
    Object e = Stack(size - i - 1);
    result->set_element(i, e);
  }
  PopNAndPush(size, result);
}


void Interpreter::PushNewArray(intptr_t size) {
  Array result = H->AllocateArray(size);  // SAFEPOINT
  for (intptr_t i = 0; i < size; i++) {
    result->set_element(i, nil, kNoBarrier);
  }
  Push(result);
}


void Interpreter::PushClosure(intptr_t num_copied,
                              intptr_t num_args,
                              intptr_t block_size) {
  EnsureActivation(fp_);  // SAFEPOINT

  Closure result = H->AllocateClosure(num_copied);  // SAFEPOINT
  result->set_defining_activation(FrameActivation(fp_));
  result->set_initial_bci(FrameMethod(fp_)->BCI(ip_));
  result->set_num_args(SmallInteger::New(num_args));
  for (intptr_t i = 0; i < num_copied; i++) {
    Object e = Stack(num_copied - i - 1);
    result->set_copied(i, e);
  }

  ip_ += block_size;
  PopNAndPush(num_copied, result);
}


void Interpreter::Perform(String selector, intptr_t num_args) {
  OrdinarySend(selector, num_args);  // SAFEPOINT
}


void Interpreter::CommonSend(intptr_t offset) {
  Array common_selectors = object_store()->common_selectors();
  String selector =
      static_cast<String>(common_selectors->element(offset * 2));
  ASSERT(selector->is_canonical());
  SmallInteger arity =
      static_cast<SmallInteger>(common_selectors->element(offset * 2 + 1));
  ASSERT(arity->IsSmallInteger());
  OrdinarySend(selector, arity->value());  // SAFEPOINT
}


Method Interpreter::MethodAt(Behavior cls, String selector) {
  ASSERT(selector->IsString());
  ASSERT(selector->is_canonical());
  Array methods = cls->methods();
  ASSERT(methods->IsArray());
  intptr_t length = methods->Size();
  for (intptr_t i = 0; i < length; i++) {
    Method method = static_cast<Method>(methods->element(i));
    ASSERT(method->selector()->IsString());
    ASSERT(method->selector()->is_canonical());
    if (method->selector() == selector) {
      return method;
    }
  }
  return static_cast<Method>(nil);
}


bool Interpreter::HasMethod(Behavior cls, String selector) {
  return MethodAt(cls, selector) != nil;
}


void Interpreter::OrdinarySend(intptr_t selector_index,
                               intptr_t num_args) {
    String selector = SelectorAt(selector_index);
    OrdinarySend(selector, num_args);  // SAFEPOINT
}


void Interpreter::OrdinarySend(String selector,
                               intptr_t num_args) {
#if LOOKUP_CACHE
  Object receiver = Stack(num_args);
  Method target;
  if (lookup_cache_.LookupOrdinary(receiver->ClassId(), selector, &target)) {
    Activate(target, num_args);  // SAFEPOINT
    return;
  }
#endif

  OrdinarySendMiss(selector, num_args);  // SAFEPOINT
}


void Interpreter::OrdinarySendMiss(String selector,
                                   intptr_t num_args) {
  Object receiver = Stack(num_args);
  Behavior receiver_class = receiver->Klass(H);
  Behavior lookup_class = receiver_class;
  while (lookup_class != nil) {
    Method method = MethodAt(lookup_class, selector);
    if (method != nil) {
      if (method->IsPublic()) {
#if LOOKUP_CACHE
        lookup_cache_.InsertOrdinary(receiver->ClassId(), selector, method);
#endif
        Activate(method, num_args);  // SAFEPOINT
        return;
      } else if (method->IsProtected()) {
        bool present_receiver = true;
        DNUSend(selector, num_args, receiver,
                receiver_class, present_receiver);  // SAFEPOINT
        return;
      }
    }
    lookup_class = lookup_class->superclass();
  }
  bool present_receiver = true;
  DNUSend(selector, num_args, receiver,
          receiver_class, present_receiver);  // SAFEPOINT
}


Behavior Interpreter::FindApplicationOf(AbstractMixin mixin,
                                        Behavior klass) {
  while (klass->mixin() != mixin) {
    klass = klass->superclass();
    if (klass == nil) {
      FATAL("Cannot find mixin application");
    }
  }
  return klass;
}


void Interpreter::SuperSend(intptr_t selector_index,
                            intptr_t num_args) {
  String selector = SelectorAt(selector_index);

#if LOOKUP_CACHE
  Object receiver = FrameReceiver(fp_);
  Object absent_receiver;
  Method target;
  if (lookup_cache_.LookupNS(receiver->ClassId(),
                             selector,
                             FrameMethod(fp_),
                             kSuper,
                             &absent_receiver,
                             &target)) {
    ASSERT(absent_receiver == nullptr);
    absent_receiver = receiver;
    ActivateAbsent(target, receiver, num_args);  // SAFEPOINT
    return;
  }
#endif

  SuperSendMiss(selector, num_args);  // SAFEPOINT
}


void Interpreter::SuperSendMiss(String selector,
                                intptr_t num_args) {
  Object receiver = FrameReceiver(fp_);
  AbstractMixin method_mixin = FrameMethod(fp_)->mixin();
  Behavior receiver_class = receiver->Klass(H);
  Behavior method_mixin_app = FindApplicationOf(method_mixin,
                                                 receiver_class);
  ProtectedSend(selector,
                num_args,
                receiver,
                method_mixin_app->superclass(),
                kSuper);  // SAFEPOINT
}


void Interpreter::ImplicitReceiverSend(intptr_t selector_index,
                                       intptr_t num_args) {
  String selector = SelectorAt(selector_index);

#if LOOKUP_CACHE
  Object method_receiver = FrameReceiver(fp_);
  Object absent_receiver;
  Method target;
  if (lookup_cache_.LookupNS(method_receiver->ClassId(),
                             selector,
                             FrameMethod(fp_),
                             kImplicitReceiver,
                             &absent_receiver,
                             &target)) {
    if (absent_receiver == nullptr) {
      absent_receiver = method_receiver;
    }
    ActivateAbsent(target, absent_receiver, num_args);  // SAFEPOINT
    return;
  }
#endif

  return ImplicitReceiverSendMiss(selector, num_args);  // SAFEPOINT
}


void Interpreter::ImplicitReceiverSendMiss(String selector,
                                           intptr_t num_args) {
  Object method_receiver = FrameReceiver(fp_);

  Object candidate_receiver = method_receiver;
  AbstractMixin candidate_mixin = FrameMethod(fp_)->mixin();

  for (;;) {
    Behavior candidateMixinApplication =
        FindApplicationOf(candidate_mixin,
                          candidate_receiver->Klass(H));
    if (HasMethod(candidateMixinApplication, selector)) {
      LexicalSend(selector,
                  num_args,
                  candidate_receiver,
                  candidate_mixin,
                  kImplicitReceiver);  // SAFEPOINT
      return;
    }
    candidate_mixin = candidate_mixin->enclosing_mixin();
    if (candidate_mixin == nil) break;
    candidate_receiver = candidateMixinApplication->enclosing_object();
  }
  ProtectedSend(selector,
                num_args,
                method_receiver,
                method_receiver->Klass(H),
                kImplicitReceiver);  // SAFEPOINT
}


void Interpreter::OuterSend(intptr_t selector_index,
                            intptr_t num_args,
                            intptr_t depth) {
  String selector = SelectorAt(selector_index);

#if LOOKUP_CACHE
  Object receiver = FrameReceiver(fp_);
  Object absent_receiver;
  Method target;
  if (lookup_cache_.LookupNS(receiver->ClassId(),
                             selector,
                             FrameMethod(fp_),
                             depth,
                             &absent_receiver,
                             &target)) {
    ASSERT(absent_receiver != nullptr);
    ActivateAbsent(target, absent_receiver, num_args);  // SAFEPOINT
    return;
  }
#endif

  OuterSendMiss(selector, num_args, depth);  // SAFEPOINT
}


void Interpreter::OuterSendMiss(String selector,
                                intptr_t num_args,
                                intptr_t depth) {
  Object receiver = FrameReceiver(fp_);
  AbstractMixin target_mixin = FrameMethod(fp_)->mixin();
  intptr_t count = 0;
  while (count < depth) {
    count++;
    Behavior mixin_app = FindApplicationOf(target_mixin,
                                            receiver->Klass(H));
    receiver = mixin_app->enclosing_object();
    target_mixin = target_mixin->enclosing_mixin();
  }
  LexicalSend(selector, num_args, receiver, target_mixin, depth);  // SAFEPOINT
}


void Interpreter::SelfSend(intptr_t selector_index,
                           intptr_t num_args) {
  String selector = SelectorAt(selector_index);

#if LOOKUP_CACHE
  Object receiver = FrameReceiver(fp_);
  Object absent_receiver;
  Method target;
  if (lookup_cache_.LookupNS(receiver->ClassId(),
                             selector,
                             FrameMethod(fp_),
                             kSelf,
                             &absent_receiver,
                             &target)) {
    ASSERT(absent_receiver == nullptr);
    ActivateAbsent(target, receiver, num_args);  // SAFEPOINT
    return;
  }
#endif

  SelfSendMiss(selector, num_args);  // SAFEPOINT
}


void Interpreter::SelfSendMiss(String selector,
                               intptr_t num_args) {
  Object receiver = FrameReceiver(fp_);
  AbstractMixin method_mixin = FrameMethod(fp_)->mixin();
  LexicalSend(selector, num_args, receiver, method_mixin, kSelf);  // SAFEPOINT
}


void Interpreter::LexicalSend(String selector,
                              intptr_t num_args,
                              Object receiver,
                              AbstractMixin mixin,
                              intptr_t rule) {
  Behavior receiver_class = receiver->Klass(H);
  Behavior mixin_application = FindApplicationOf(mixin, receiver_class);
  Method method = MethodAt(mixin_application, selector);
  if (method != nil && method->IsPrivate()) {
#if LOOKUP_CACHE
    Object method_receiver = FrameReceiver(fp_);
    lookup_cache_.InsertNS(method_receiver->ClassId(),
                           selector,
                           FrameMethod(fp_),
                           rule,
                           receiver == method_receiver ? Object() : receiver,
                           method);
#endif
    ActivateAbsent(method, receiver, num_args);  // SAFEPOINT
    return;
  }
  ProtectedSend(selector, num_args, receiver,
                receiver_class, rule);  // SAFEPOINT
}


void Interpreter::ProtectedSend(String selector,
                                intptr_t num_args,
                                Object receiver,
                                Behavior mixin_application,
                                intptr_t rule) {
  Behavior lookup_class = mixin_application;
  while (lookup_class != nil) {
    Method method = MethodAt(lookup_class, selector);
    if (method != nil && !method->IsPrivate()) {
#if LOOKUP_CACHE
      Object method_receiver = FrameReceiver(fp_);
      lookup_cache_.InsertNS(method_receiver->ClassId(),
                             selector,
                             FrameMethod(fp_),
                             rule,
                             receiver == method_receiver ? Object() : receiver,
                             method);
#endif
      ActivateAbsent(method, receiver, num_args);  // SAFEPOINT
      return;
    }
    lookup_class = lookup_class->superclass();
  }
  bool present_receiver = false;
  DNUSend(selector, num_args, receiver, mixin_application,
          present_receiver);  // SAFEPOINT
}


void Interpreter::DNUSend(String selector,
                          intptr_t num_args,
                          Object receiver,
                          Behavior lookup_class,
                          bool present_receiver) {
  if (TRACE_DNU) {
    char* c1 = receiver->ToCString(H);
    char* c2 = selector->ToCString(H);
    char* c3 = FrameMethod(fp_)->selector()->ToCString(H);
    OS::PrintErr("DNU %s %s from %s\n", c1, c2, c3);
    free(c1);
    free(c2);
    free(c3);
  }

  Behavior cls = lookup_class;
  Method method;
  do {
    method = MethodAt(cls, object_store()->does_not_understand());
    if (method != nil) {
      break;
    }
    cls = cls->superclass();
  } while (cls != nil);

  if (method == nil) {
    FATAL("Recursive #doesNotUnderstand:");
  }

  Array arguments;
  {
    HandleScope h1(H, reinterpret_cast<Object*>(&selector));
    HandleScope h2(H, &receiver);
    HandleScope h3(H, reinterpret_cast<Object*>(&method));
    arguments = H->AllocateArray(num_args);  // SAFEPOINT
  }
  for (intptr_t i = 0; i < num_args; i++) {
    Object e = Stack(num_args - i - 1);
    arguments->set_element(i, e);
  }
  Message message;
  {
    HandleScope h1(H, reinterpret_cast<Object*>(&selector));
    HandleScope h2(H, &receiver);
    HandleScope h3(H, reinterpret_cast<Object*>(&method));
    HandleScope h4(H, reinterpret_cast<Object*>(&arguments));
    message = H->AllocateMessage();  // SAFEPOINT
  }

  message->set_selector(selector);
  message->set_arguments(arguments);

  Drop(num_args);
  if (!present_receiver) {
    Push(receiver);
  }
  Push(message);
  Activate(method, 1);  // SAFEPOINT
}


void Interpreter::SendCannotReturn(Object result) {
  if (TRACE_SPECIAL_CONTROL) {
    OS::PrintErr("#cannotReturn:\n");
  }

  Activation top;
  {
    HandleScope h1(H, &result);
    top = EnsureActivation(fp_);  // SAFEPOINT
  }

  Behavior receiver_class = top->Klass(H);
  Behavior cls = receiver_class;
  Method method;
  do {
    method = MethodAt(cls, object_store()->cannot_return());
    if (method != nil) {
      break;
    }
    cls = cls->superclass();
  } while (cls != nil);

  if (method == nil) {
    FATAL("Missing #cannotReturn:");
  }

  Push(top);
  Push(result);
  Activate(method, 1);  // SAFEPOINT
}


void Interpreter::SendAboutToReturnThrough(Object result,
                                           Activation unwind) {
  if (TRACE_SPECIAL_CONTROL) {
    OS::PrintErr("#aboutToReturn:through:\n");
  }

  Activation top;
  {
    HandleScope h1(H, &result);
    HandleScope h2(H, reinterpret_cast<Object*>(&unwind));
    top = EnsureActivation(fp_);  // SAFEPOINT
  }

  Behavior receiver_class = top->Klass(H);
  Behavior cls = receiver_class;
  Method method;
  do {
    method = MethodAt(cls, object_store()->about_to_return_through());
    if (method != nil) {
      break;
    }
    cls = cls->superclass();
  } while (cls != nil);

  if (method == nil) {
    FATAL("Missing #aboutToReturn:through:");
  }

  Push(top);
  Push(result);
  Push(unwind);
  Activate(method, 2);  // SAFEPOINT
}


void Interpreter::SendNonBooleanReceiver(Object non_boolean) {
  // Note that Squeak instead sends #mustBeBoolean to the non-boolean.
  if (TRACE_SPECIAL_CONTROL) {
    OS::PrintErr("#nonBooleanReceiver:\n");
  }

  Activation top;
  {
    HandleScope h1(H, &non_boolean);
    top = EnsureActivation(fp_);  // SAFEPOINT
  }

  Behavior receiver_class = top->Klass(H);
  Behavior cls = receiver_class;
  Method method;
  do {
    method = MethodAt(cls, object_store()->non_boolean_receiver());
    if (method != nil) {
      break;
    }
    cls = cls->superclass();
  } while (cls != nil);

  if (method == nil) {
    FATAL("Missing #nonBooleanReceiver:");
  }

  Push(top);
  Push(non_boolean);
  Activate(method, 1);  // SAFEPOINT
}


void Interpreter::InsertAbsentReceiver(Object receiver, intptr_t num_args) {
  ASSERT(num_args >= 0);
  ASSERT(num_args < 255);

  ASSERT(StackDepth() >= num_args);
  Grow(1);
  for (intptr_t i = 0; i < num_args; i++) {
    StackPut(i, Stack(i + 1));
  }
  StackPut(num_args, receiver);
}


void Interpreter::ActivateAbsent(Method& method,
                                 Object receiver,
                                 intptr_t num_args) {
  InsertAbsentReceiver(receiver, num_args);
  Activate(method, num_args);  // SAFEPOINT
}


void Interpreter::Activate(Method& method, intptr_t num_args) {
  ASSERT(num_args == method->NumArgs());    
  const auto prim = method->Primitive();
  if (prim != 0) {
    if (TRACE_PRIMITIVES) {
      OS::PrintErr("Primitive %" Pd "\n", prim);
    }
    if ((prim & 256) != 0) {
      // Getter
      const auto offset = prim & 255;
      ASSERT(num_args == 0);
      const auto& receiver = Stack(0);
      ASSERT(receiver.IsRegularObject() || receiver.IsEphemeron());
      const auto& value = static_cast<RegularObject>(receiver)->slot(offset);
      PopNAndPush(1, value);
      return;
    } else if ((prim & 512) != 0) {
      // Setter
      const auto offset = prim & 255;
      ASSERT(num_args == 1);
      const auto& receiver = Stack(1);
      const auto& value = Stack(0);
      ASSERT(receiver.IsRegularObject() || receiver.IsEphemeron());
      static_cast<RegularObject>(receiver)->set_slot(offset, value);
      PopNAndPush(2, receiver);
      return;
    } else {
      HandleScope h1(H, reinterpret_cast<Object*>(&method));
      if (Primitives::Invoke(prim, num_args, H, this)) {  // SAFEPOINT
        ASSERT(StackDepth() >= 0);
        return;
      }
    }
  }

  // Create frame.
  const auto& receiver = Stack(num_args);
  Push(static_cast<SmallInteger>(reinterpret_cast<uword>(ip_)));
  Push(static_cast<SmallInteger>(reinterpret_cast<uword>(fp_)));
  fp_ = sp_;
  Push(MakeFlags(num_args, false));
  Push(method);
  Push(Object(static_cast<uword>(0)));  // Activation.
  Push(receiver);

  ip_ = method->IP(SmallInteger::New(1));
  const auto num_temps = method->NumTemps();
  for (auto i = num_args; i < num_temps; i++) {
    Push(nil);
  }

  if (sp_ < checked_stack_limit_) {
    StackOverflow();
  }
}


void Interpreter::ActivateClosure(intptr_t num_args) {
  Closure closure = static_cast<Closure>(Stack(num_args));
  ASSERT(closure->IsClosure());
  ASSERT(closure->num_args() == SmallInteger::New(num_args));

  Activation home = closure->defining_activation();

  // Create frame.
  Push(static_cast<SmallInteger>(reinterpret_cast<uword>(ip_)));
  Push(static_cast<SmallInteger>(reinterpret_cast<uword>(fp_)));
  fp_ = sp_;
  Push(MakeFlags(num_args, true));
  Push(home->method());
  Push(Object(static_cast<uword>(0)));  // Activation.
  Push(home->receiver());

  ip_ = home->method()->IP(closure->initial_bci());

  intptr_t num_copied = closure->NumCopied();
  for (intptr_t i = 0; i < num_copied; i++) {
    Push(closure->copied(i));
  }

  // Temps allocated by bytecodes

  if (sp_ < checked_stack_limit_) {
    StackOverflow();
  }
}


void Interpreter::CreateBaseFrame(Activation activation) {
  ASSERT(activation->IsActivation());
  ASSERT(activation->bci()->IsSmallInteger());

  ASSERT(ip_ == 0);
  ASSERT(sp_ == stack_base_);
  ASSERT(fp_ == 0);

  bool is_closure;
  intptr_t num_args;
  if (activation->closure() == nil) {
    is_closure = false;
    num_args = activation->method()->NumArgs();
    Push(activation->receiver());  // Message receiver.
  } else {
    Closure closure = activation->closure();
    ASSERT(closure->IsClosure());
    is_closure = true;
    num_args = closure->num_args()->value();
    Push(closure);                // Message receiver.
  }
  for (intptr_t i = 0; i < num_args; i++) {
    Push(activation->temp(i));
  }

  ASSERT(!activation->sender()->IsSmallInteger());

  // Create frame.
  Push(activation->sender());           // Base sender.
  Push(Object(static_cast<uword>(0)));  // Saved FP.
  fp_ = sp_;
  Push(MakeFlags(num_args, is_closure));
  Push(activation->method());
  Push(activation);
  Push(activation->receiver());

  intptr_t num_temps = activation->StackDepth();
  for (intptr_t i = num_args; i < num_temps; i++) {
    Push(activation->temp(i));
  }
  // Drop temps. We don't update the activation as we store into the frame, so
  // the stale references in the activation may create leaks.
  activation->set_stack_depth(SmallInteger::New(num_args));

  ip_ = activation->method()->IP(activation->bci());

  ASSERT(FrameBaseSender(fp_) == activation->sender());
  activation->set_sender_fp(fp_);
  ASSERT(FrameSavedFP(fp_) == 0);
  ASSERT(FrameMethod(fp_) == activation->method());
  ASSERT(FrameActivation(fp_) == activation);
  ASSERT(FrameReceiver(fp_) == activation->receiver());
}


void Interpreter::StackOverflow() {
  if (checked_stack_limit_ == reinterpret_cast<Object*>(-1)) {
    // Interrupt.
    isolate_->PrintStack();
    Exit();
  }

  // True overflow: reclaim stack space by moving all frames except the top
  // frame to the heap.
  CreateBaseFrame(FlushAllFrames());  // SAFEPOINT
}


String Interpreter::SelectorAt(intptr_t index) {
  Array literals = FrameMethod(fp_)->literals();
  ASSERT((index >= 0) && (index < literals->Size()));
  Object selector = literals->element(index);
  ASSERT(selector->IsString());
  ASSERT(static_cast<String>(selector)->is_canonical());
  return static_cast<String>(selector);
}


void Interpreter::LocalReturn(Object result) {
  Object* saved_fp = FrameSavedFP(fp_);
  if (saved_fp == 0) {
    LocalBaseReturn(result);  // SAFEPOINT
    return;
  }

  ip_ = FrameSavedIP(fp_);
  sp_ = FrameSavedSP(fp_);
  fp_ = saved_fp;
  Push(result);
}


void Interpreter::LocalBaseReturn(Object result) {
  // Returning from the base frame.
  Activation top;
  {
    HandleScope h(H, reinterpret_cast<Object*>(&result));
    top = FlushAllFrames();  // SAFEPOINT
  }

  Activation sender = top->sender();
  if (!sender->IsActivation() ||
      !sender->bci()->IsSmallInteger()) {
    CreateBaseFrame(top);
    SendCannotReturn(result);  // SAFEPOINT
    return;
  }

  top->set_sender(static_cast<Activation>(nil), kNoBarrier);
  top->set_bci(static_cast<SmallInteger>(nil));

  CreateBaseFrame(sender);
  Push(result);
}


void Interpreter::NonLocalReturn(Object result) {
  // Search the static chain for the enclosing method activation.
  ASSERT(FlagsIsClosure(FrameFlags(fp_)));
  Closure c = static_cast<Closure>(FrameTemp(fp_, -1));
  ASSERT(c->IsClosure());
  Activation home = c->defining_activation();
  ASSERT(home->IsActivation());
  c = home->closure();
  while (c != nil) {
    home = c->defining_activation();
    ASSERT(home->IsActivation());
    c = home->closure();
  }

  for (Object* fp = FrameSavedFP(fp_); fp != 0; fp = FrameSavedFP(fp)) {
    if (FrameActivation(fp) == home) {
      if (FrameSavedFP(fp) == 0) {
        break;  // Return crosses base frame.
      }

      // Note this implicitly zaps every activation on the dynamic chain.
      ip_ = FrameSavedIP(fp);
      sp_ = FrameSavedSP(fp);
      fp_ = FrameSavedFP(fp);
      Push(result);
      return;
    }

    intptr_t prim = FrameMethod(fp)->Primitive();
    if (Primitives::IsUnwindProtect(prim)) {
      break;
    }
    if (Primitives::IsSimulationRoot(prim)) {
      break;
    }
  }

  // A more complicated case: crossing the base frame, #cannotReturn:, or
  // #aboutToReturn:to:. These cares are very rare, so we simply flush to
  // activations instead of dealing with a mixture of frames and activations.

  Activation top;
  {
    HandleScope h1(H, reinterpret_cast<Object*>(&home));
    HandleScope h2(H, reinterpret_cast<Object*>(&result));
    top = FlushAllFrames();  // SAFEPOINT
  }

  // Search the dynamic chain for a dead activation or an unwind-protect
  // activation that would block the return.
  for (Activation unwind = top->sender();
       unwind != home;
       unwind = unwind->sender()) {
    if (!unwind->IsActivation()) {
      ASSERT(unwind == nil);
      CreateBaseFrame(top);
      SendCannotReturn(result);  // SAFEPOINT
      return;
    }

    intptr_t prim = unwind->method()->Primitive();
    if (Primitives::IsUnwindProtect(prim)) {
      CreateBaseFrame(top);
      SendAboutToReturnThrough(result, unwind);  // SAFEPOINT
      return;
    }
    if (Primitives::IsSimulationRoot(prim)) {
      CreateBaseFrame(top);
      SendCannotReturn(result);  // SAFEPOINT
      return;
    }
  }

  Activation sender = home->sender();
  if (!sender->IsActivation() ||
      !sender->bci()->IsSmallInteger()) {
    CreateBaseFrame(top);
    SendCannotReturn(result);  // SAFEPOINT
    return;
  }

  // Mark activations on the dynamic chain up to the return target as dead.
  // Note this follows the behavior of Squeak instead of the blue book, which
  // only zaps A.
  Activation zap = top;
  do {
    Activation next = zap->sender();
    zap->set_sender(static_cast<Activation>(nil), kNoBarrier);
    zap->set_bci(static_cast<SmallInteger>(nil));
    zap = next;
  } while (zap != sender);

  CreateBaseFrame(sender);
  Push(result);
}


void Interpreter::MethodReturn(Object result) {
  // TODO(rmacnak): Squeak groups the syntactically similar method return and
  // non-local return into the same bytecode. Change the bytecodes to group the
  // functionally similar method return with closure local return instead.
  if (!FlagsIsClosure(FrameFlags(fp_))) {
    LocalReturn(result);
  } else {
    NonLocalReturn(result);
  }
}


void Interpreter::Enter() {
  intptr_t saved_handles = H->handles();
  jmp_buf* saved_environment = environment_;

  jmp_buf environment;
  environment_ = &environment;

  if (setjmp(environment) == 0) {
    Interpret();
    UNREACHABLE();
  }

  environment_ = saved_environment;
  H->set_handles(saved_handles);
}


void Interpreter::Exit() {
  ASSERT(environment_ != nullptr);
  longjmp(*environment_, 1);
}

void Interpreter::ActivateDispatch(Method& method, intptr_t num_args) {
  ASSERT(method->Primitive() == 0);
  Interpreter::Activate(method, num_args);
}

void Interpreter::ReturnFromDispatch() {
  Object* saved_fp = FrameSavedFP(fp_);
  if (saved_fp == 0) {
    // Base frame.
    Activation sender = FrameBaseSender(fp_);
    if (sender != nil) {
      ip_ = 0;
      sp_ = FrameSavedSP(fp_);
      fp_ = saved_fp;
      CreateBaseFrame(sender);
      return;
    }
  }

  ip_ = FrameSavedIP(fp_);
  sp_ = FrameSavedSP(fp_);
  fp_ = saved_fp;
}

void Interpreter::PrintStack() {
  Activation top = FlushAllFrames();  // SAFEPOINT
  top->PrintStack(H);
  CreateBaseFrame(top);
}

void Interpreter::PopulateFunctionTable() {
    
    // V4: push receiver variable
    for (auto op = 0; op < 16; ++op) {
        funcTable_.push_back([](Context& context) {
            FATAL("Unused bytecode");
        });
    }
    
    for (auto op = 16; op < 32; ++op) {
        funcTable_.push_back([](Context& context) {
            context.i->PushLiteralVariable(context.op - 16);
        });
    }
    
    for (auto op = 32; op < 64; ++op) {
        funcTable_.push_back([](Context& context) {
            context.i->PushLiteral(context.op - 32);
        });
    }
    
    for (auto op = 64; op < 76; ++op) {
        funcTable_.push_back([](Context& context) {
            context.i->PushTemporary(context.op - 64);
        });
    }
    
    // 76
    funcTable_.push_back([](Context& context) {
        context.i->Push(FrameReceiver(context.i->fp_));
    });
    
    // 77
    funcTable_.push_back([](Context& context) {
        switch (context.extB) {
            case 0:
                context.i->Push(context.i->false_);
                break;
            case 1:
                context.i->Push(context.i->true_);
                break;
            case 2:
                context.i->Push(context.i->nil_);
                break;
            case 3:
                FATAL("Unused bytecode");  // V4: push thisContext
                break;
            default:
                context.i->PushEnclosingObject(-context.extB);
                break;
        }
        context.extB = 0;
    });
    
    // 78
    funcTable_.push_back([](Context& context) {
        context.i->Push(SmallInteger::New(0));
    });
    
    // 79
    funcTable_.push_back([](Context& context) {
        context.i->Push(SmallInteger::New(1));
    });
    
    // 80
    funcTable_.push_back([](Context& context) {
        // +
        const auto& left = context.i->Stack(1);
        const auto& right = context.i->Stack(0);
        if (left.IsSmallInteger() && right.IsSmallInteger()) {
            const auto raw_left = static_cast<SmallInteger>(left).value();
            const auto raw_right = static_cast<SmallInteger>(right).value();
            const auto raw_result = raw_left + raw_right;
            if (SmallInteger::IsSmiValue(raw_result)) {
                context.i->PopNAndPush(2, SmallInteger::New(raw_result));
                return;
            }
        }
        context.i->CommonSend(context.op - 80);
    });
    
    // 81
    funcTable_.push_back([](Context& context) {

        // -
        const auto& left = context.i->Stack(1);
        const auto& right = context.i->Stack(0);
        if (left.IsSmallInteger() && right.IsSmallInteger()) {
            const auto raw_left = static_cast<SmallInteger>(left).value();
            const auto raw_right = static_cast<SmallInteger>(right).value();
            const auto raw_result = raw_left - raw_right;
            if (SmallInteger::IsSmiValue(raw_result)) {
                context.i->PopNAndPush(2, SmallInteger::New(raw_result));
                return;
            }
        }
        context.i->CommonSend(context.op - 80);
    });
    
    // 82
    funcTable_.push_back([](Context& context) {
        // <
        const auto& left = context.i->Stack(1);
        const auto& right = context.i->Stack(0);
        if (left.IsSmallInteger() && right.IsSmallInteger()) {
            if (static_cast<intptr_t>(left) <
                static_cast<intptr_t>(right)) {
                context.i->PopNAndPush(2, context.i->true_);
            } else {
                context.i->PopNAndPush(2, context.i->false_);
            }
            return;
        }
        context.i->CommonSend(context.op - 80);
    });

    // 83
    funcTable_.push_back([](Context& context) {
        // >
        const auto& left = context.i->Stack(1);
        const auto& right = context.i->Stack(0);
        if (left.IsSmallInteger() && right.IsSmallInteger()) {
            if (static_cast<intptr_t>(left) >
                static_cast<intptr_t>(right)) {
                context.i->PopNAndPush(2, context.i->true_);
            } else {
                context.i->PopNAndPush(2, context.i->false_);
            }
            return;
        }
        context.i->CommonSend(context.op - 80);
    });
    
    // 84
    funcTable_.push_back([](Context& context) {
        // <=
        const auto& left = context.i->Stack(1);
        const auto& right = context.i->Stack(0);
        if (left.IsSmallInteger() && right.IsSmallInteger()) {
            if (static_cast<intptr_t>(left) <=
                static_cast<intptr_t>(right)) {
                context.i->PopNAndPush(2, context.i->true_);
            } else {
                context.i->PopNAndPush(2, context.i->false_);
            }
            return;
        }
        context.i->CommonSend(context.op - 80);
    });

    // 85
    funcTable_.push_back([](Context& context) {
        // >=
        const auto& left = context.i->Stack(1);
        const auto& right = context.i->Stack(0);
        if (left.IsSmallInteger() && right.IsSmallInteger()) {
            if (static_cast<intptr_t>(left) >=
                static_cast<intptr_t>(right)) {
                context.i->PopNAndPush(2, context.i->true_);
            } else {
                context.i->PopNAndPush(2, context.i->false_);
            }
            return;
        }
        context.i->CommonSend(context.op - 80);
    });

    // 86
    funcTable_.push_back([](Context& context) {
        // =
        const auto& left = context.i->Stack(1);
        const auto& right = context.i->Stack(0);
        if (left.IsSmallInteger() && right.IsSmallInteger()) {
            if (static_cast<intptr_t>(left) ==
                static_cast<intptr_t>(right)) {
                context.i->PopNAndPush(2, context.i->true_);
            } else {
                context.i->PopNAndPush(2, context.i->false_);
            }
            return;
        }
        context.i->CommonSend(context.op - 80);
    });

    // 87
    funcTable_.push_back([](Context& context) {
        // ~=
        context.i->CommonSend(context.op - 80);
    });

    // 88
    funcTable_.push_back([](Context& context) {
        // *
        context.i->CommonSend(context.op - 80);
    });

    // 89
    funcTable_.push_back([](Context& context) {
        // /
        context.i->CommonSend(context.op - 80);
    });
    
    
    // 90
    funcTable_.push_back([](Context& context) {
        /* \\ */
        const auto& left = context.i->Stack(1);
        const auto& right = context.i->Stack(0);
        if (left.IsSmallInteger() && right.IsSmallInteger()) {
            const auto raw_left = static_cast<SmallInteger>(left).value();
            const auto raw_right = static_cast<SmallInteger>(right).value();
            if (raw_right != 0) {
                const auto raw_result = Math::FloorMod(raw_left, raw_right);
                ASSERT(SmallInteger::IsSmiValue(raw_result));
                context.i->PopNAndPush(2, SmallInteger::New(raw_result));
                return;
            }
        }
        context.i->CommonSend(context.op - 80);
    });

    // 91
    funcTable_.push_back([](Context& context) {
        // @
        context.i->CommonSend(context.op - 80);
    });

    // 92
    funcTable_.push_back([](Context& context) {
        // bitShift:
        context.i->CommonSend(context.op - 80);
    });

    // 93
    funcTable_.push_back([](Context& context) {
        // //
        context.i->CommonSend(context.op - 80);
    });

    // 94
    funcTable_.push_back([](Context& context) {
        // bitAnd:
        const auto& left = context.i->Stack(1);
        const auto& right = context.i->Stack(0);
        if (left.IsSmallInteger() && right.IsSmallInteger()) {
            const auto raw_left = static_cast<SmallInteger>(left).value();
            const auto raw_right = static_cast<SmallInteger>(right).value();
            const auto raw_result = raw_left & raw_right;
            context.i->PopNAndPush(2, SmallInteger::New(raw_result));
            return;
        }
        context.i->CommonSend(context.op - 80);
    });

    // 95
    funcTable_.push_back([](Context& context) {
        // bitOr:
        const auto& left = context.i->Stack(1);
        const auto& right = context.i->Stack(0);
        if (left.IsSmallInteger() && right.IsSmallInteger()) {
            const auto raw_left = static_cast<SmallInteger>(left).value();
            const auto raw_right = static_cast<SmallInteger>(right).value();
            const auto raw_result = raw_left | raw_right;
            context.i->PopNAndPush(2, SmallInteger::New(raw_result));
            return;
        }
        context.i->CommonSend(context.op - 80);
    });
    
    
    // 96
    funcTable_.push_back([](Context& context) {
        // at:
        const auto& array = context.i->Stack(1);
        SmallInteger index = static_cast<SmallInteger>(context.i->Stack(0));
        if (index->IsSmallInteger()) {
            intptr_t raw_index = index->value() - 1;
            if (array.IsArray()) {
                if ((raw_index >= 0) &&
                    (raw_index < static_cast<Array>(array)->Size())) {
                    Object value = static_cast<Array>(array)->element(raw_index);
                    context.i->PopNAndPush(2, value);
                    return;
                }
            } else if (array.IsBytes()) {
                if ((raw_index >= 0) &&
                    (raw_index < static_cast<Bytes>(array)->Size())) {
                    const auto raw_value = static_cast<Bytes>(array)->element(raw_index);
                    context.i->PopNAndPush(2, SmallInteger::New(raw_value));
                    return;
                }
            }
        }
        context.i->CommonSend(context.op - 80);
    });

    // 97
    funcTable_.push_back([](Context& context) {
        // at:put:
        const auto& array = context.i->Stack(2);
        SmallInteger index = static_cast<SmallInteger>(context.i->Stack(1));
        if (index->IsSmallInteger()) {
            intptr_t raw_index = index->value() - 1;
            if (array.IsArray()) {
                if ((raw_index >= 0) &&
                    (raw_index < static_cast<Array>(array)->Size())) {
                    Object value = context.i->Stack(0);
                    static_cast<Array>(array)->set_element(raw_index, value);
                    context.i->PopNAndPush(3, value);
                    return;
                }
            } else if (array.IsByteArray()) {
                SmallInteger value = static_cast<SmallInteger>(context.i->Stack(0));
                if ((raw_index >= 0) &&
                    (raw_index < static_cast<ByteArray>(array)->Size()) &&
                    static_cast<uword>(value) <= 255) {
                    static_cast<ByteArray>(array)->set_element(raw_index,
                                                               value->value());
                    context.i->PopNAndPush(3, value);
                    return;
                }
            }
        }
        context.i->CommonSend(context.op - 80);
    });

    // 98
    funcTable_.push_back([](Context& context) {
        // size
        const auto& array = context.i->Stack(0);
        if (array.IsArray()) {
            context.i->PopNAndPush(1, static_cast<Array>(array)->size());
            return;
        } else if (array.IsBytes()) {
            context.i->PopNAndPush(1, static_cast<Bytes>(array)->size());
            return;
        }
        context.i->CommonSend(context.op - 80);
    });

    for (auto op = 99; op < 112; ++op) {
        funcTable_.push_back([](Context& context) {
            context.i->CommonSend(context.op - 80);
        });
    }

    for (auto op = 112; op < 128; ++op) {
        funcTable_.push_back([](Context& context) {
            context.i->OrdinarySend(context.op & 15, 0);
        });
    }
    
    for (auto op = 128; op < 144; ++op) {
        funcTable_.push_back([](Context& context) {
            context.i->OrdinarySend(context.op & 15, 1);
        });
    }
    
    for (auto op = 144; op < 160; ++op) {
        funcTable_.push_back([](Context& context) {
            context.i->OrdinarySend(context.op & 15, 2);
        });
    }

    for (auto op = 160; op < 176; ++op) {
        funcTable_.push_back([](Context& context) {
            context.i->ImplicitReceiverSend(context.op & 15, 0);
        });
    }

    for (auto op = 176; op < 184; ++op) {
        funcTable_.push_back([](Context& context) {
            // V4: pop into receiver variable
            FATAL("Unused bytecode");
        });
    }
    
    for (auto op = 184; op < 192; ++op) {
        funcTable_.push_back([](Context& context) {
            context.i->PopIntoTemporary(context.op & 7);
        });
    }

    for (auto op = 192; op < 216; ++op) {
        funcTable_.push_back([](Context& context) {
            FATAL("Unused bytecode");
        });
    }

    // 216
    funcTable_.push_back([](Context& context) {
        context.i->MethodReturn(FrameReceiver(context.i->fp_));
    });
    
    // 217
    funcTable_.push_back([](Context& context) {
        context.i->MethodReturn(context.i->Pop());
    });
    
    // 218
    funcTable_.push_back([](Context& context) {
        ASSERT(FlagsIsClosure(FrameFlags(context.i->fp_)));
        context.i->LocalReturn(context.i->Pop());
    });
    
    // 219
    funcTable_.push_back([](Context& context) {
        context.i->Push(context.i->Stack(0));
    });
    
    // 220
    funcTable_.push_back([](Context& context) {
        context.i->Drop(1);
    });

    // 221
    funcTable_.push_back([](Context& context) {
        // V4: nop
        FATAL("Unused bytecode");
    });

    // 222
    funcTable_.push_back([](Context& context) {
        // V4: break
        FATAL("Unused bytecode");
    });

    // 223
    funcTable_.push_back([](Context& context) {
        // V4: not assigned
        FATAL("Unused bytecode");
    });

    // 224
    funcTable_.push_back([](Context& context) {
        const auto byte2 = context.i->GetAndIncrementIP();
        context.extA = (context.extA << 8) + byte2;
    });

    // 225
    funcTable_.push_back([](Context& context) {
        const auto byte2 = context.i->GetAndIncrementIP();
        if (context.extB == 0 && byte2 > 127) {
            context.extB = byte2 - 256;
        } else {
            context.extB = (context.extB << 8) + byte2;
        }
    });

    // 226
    funcTable_.push_back([](Context& context) {
        // V4: push receiver variable
        FATAL("Unused bytecode");
    });

    // 227
    funcTable_.push_back([](Context& context) {
        uint8_t byte2 = context.i->GetAndIncrementIP();
        context.i->PushLiteralVariable((context.extA << 8) + byte2);
        context.extA = 0;
    });

    // 228
    funcTable_.push_back([](Context& context) {
        uint8_t byte2 = context.i->GetAndIncrementIP();
        context.i->PushLiteral(byte2 + context.extA * 256);
        context.extA = 0;
    });

    // 229
    funcTable_.push_back([](Context& context) {
        uint8_t byte2 = context.i->GetAndIncrementIP();
        context.i->Push(SmallInteger::New((context.extB << 8) + byte2));
        context.extB = 0;
    });

    // 230
    funcTable_.push_back([](Context& context) {
        uint8_t byte2 = context.i->GetAndIncrementIP();
        context.i->PushTemporary(byte2);
    });

    // 231
    funcTable_.push_back([](Context& context) {
        uint8_t byte2 = context.i->GetAndIncrementIP();
        if (byte2 < 128) {
            context.i->PushNewArray(byte2);
        } else {
            context.i->PushNewArrayWithElements(byte2 - 128);
        }
    });

    // 232
    funcTable_.push_back([](Context& context) {
        // V4: store into receiver variable
        FATAL("Unused bytecode");
    });

    // 233
    funcTable_.push_back([](Context& context) {
        // V4: store into literal variable
        FATAL("Unused bytecode");
    });

    // 234
    funcTable_.push_back([](Context& context) {
        uint8_t byte2 = context.i->GetAndIncrementIP();
        context.i->StoreIntoTemporary(byte2);
    });

    // 235
    funcTable_.push_back([](Context& context) {
        // V4: pop into receiver variable
        FATAL("Unused bytecode");
    });

    // 236
    funcTable_.push_back([](Context& context) {
        // V4: pop into literal variable
        FATAL("Unused bytecode");
    });

    // 237
    funcTable_.push_back([](Context& context) {
        uint8_t byte2 = context.i->GetAndIncrementIP();
        context.i->PopIntoTemporary(byte2);

    });

    // 238
    funcTable_.push_back([](Context& context) {
        uint8_t byte2 = context.i->GetAndIncrementIP();
        intptr_t selector_index = (context.extA << 5) + (byte2 >> 3);
        intptr_t num_args = (context.extB << 3) | (byte2 & 7);
        context.extA = context.extB = 0;
        context.i->OrdinarySend(selector_index, num_args);
    });

    // 239
    funcTable_.push_back([](Context& context) {
        // V4: static super send
        FATAL("Unused bytecode");
    });

    // 240
    funcTable_.push_back([](Context& context) {
        uint8_t byte2 = context.i->GetAndIncrementIP();
        intptr_t selector_index = (context.extA << 5) + (byte2 >> 3);
        intptr_t num_args = (context.extB << 3) | (byte2 & 7);
        context.extA = context.extB = 0;
        context.i->ImplicitReceiverSend(selector_index, num_args);
    });

    // 241
    funcTable_.push_back([](Context& context) {
        uint8_t byte2 = context.i->GetAndIncrementIP();
        intptr_t selector_index = (context.extA << 5) + (byte2 >> 3);
        intptr_t num_args = (context.extB << 3) | (byte2 & 7);
        context.extA = context.extB = 0;
        context.i->SuperSend(selector_index, num_args);
    });

    // 242
    funcTable_.push_back([](Context& context) {
        uint8_t byte2 = context.i->GetAndIncrementIP();
        intptr_t delta = (context.extB << 8) + byte2;
        context.extB = 0;
        context.i->ip_ += delta;
    });

    // 243
    funcTable_.push_back([](Context& context) {
        uint8_t byte2 = context.i->GetAndIncrementIP();
        intptr_t delta = (context.extB << 8) + byte2;
        context.extB = 0;
        Object top = context.i->Pop();
        if (top == context.i->false_) {
        } else if (top == context.i->true_) {
            context.i->ip_ += delta;
        } else {
            context.i->SendNonBooleanReceiver(top);
        }
    });

    // 244
    funcTable_.push_back([](Context& context) {
        uint8_t byte2 = context.i->GetAndIncrementIP();
        intptr_t delta = (context.extB << 8) + byte2;
        context.extB = 0;
        Object top = context.i->Pop();
        if (top == context.i->true_) {
        } else if (top == context.i->false_) {
            context.i->ip_ += delta;
        } else {
            context.i->SendNonBooleanReceiver(top);
        }
    });

    // 245
    funcTable_.push_back([](Context& context) {
        uint8_t byte2 = context.i->GetAndIncrementIP();
        intptr_t selector_index = (context.extA << 5) + (byte2 >> 3);
        intptr_t num_args = (context.extB << 3) | (byte2 & 7);
        context.extA = context.extB = 0;
        context.i->SelfSend(selector_index, num_args);
    });
        
    // 246
    funcTable_.push_back([](Context& context) {
        // V4: unassigned
        FATAL("Unused bytecode");
    });

    // 247
    funcTable_.push_back([](Context& context) {
        // V4: unassigned
        FATAL("Unused bytecode");
    });

    // 248
    funcTable_.push_back([](Context& context) {
        // V4: unassigned
        FATAL("Unused bytecode");
    });

    // 249
    funcTable_.push_back([](Context& context) {
        // V4: call primitive
        FATAL("Unused bytecode");
    });
    
    // 250
    funcTable_.push_back([](Context& context) {
        uint8_t byte2 = context.i->GetAndIncrementIP();
        uint8_t byte3 = context.i->GetAndIncrementIP();
        context.i->PushRemoteTemp(byte3, byte2);
    });

    // 251
    funcTable_.push_back([](Context& context) {
        uint8_t byte2 = context.i->GetAndIncrementIP();
        uint8_t byte3 = context.i->GetAndIncrementIP();
        context.i->StoreIntoRemoteTemp(byte3, byte2);
    });

    // 252
    funcTable_.push_back([](Context& context) {
        uint8_t byte2 = context.i->GetAndIncrementIP();
        uint8_t byte3 = context.i->GetAndIncrementIP();
        context.i->PopIntoRemoteTemp(byte3, byte2);
    });

    // 253
    funcTable_.push_back([](Context& context) {
        uint8_t byte2 = context.i->GetAndIncrementIP();
        uint8_t byte3 = context.i->GetAndIncrementIP();
        intptr_t num_copied = (byte2 >> 3 & 7) + ((context.extA / 16) << 3);
        intptr_t num_args = (byte2 & 7) + ((context.extA % 16) << 3);
        intptr_t block_size = byte3 + (context.extB << 8);
        context.extA = context.extB = 0;
        context.i->PushClosure(num_copied, num_args, block_size);
    });

    // 254
    funcTable_.push_back([](Context& context) {
        uint8_t byte2 = context.i->GetAndIncrementIP();
        uint8_t byte3 = context.i->GetAndIncrementIP();
        intptr_t selector_index = (context.extA << 5) + (byte2 >> 3);
        intptr_t num_args = (context.extB << 3) | (byte2 & 7);
        intptr_t depth = byte3;
        context.extA = context.extB = 0;
        context.i->OuterSend(selector_index, num_args, depth);
    });

    // 255
    funcTable_.push_back([](Context& context) {
        FATAL("Unused bytecode");  // V4: unassigned
    });
}

void Interpreter::Interpret() {
    
    Context context;
    context.i = this;

    for (;;) {
        ASSERT(ip_ != 0);
        ASSERT(sp_ != 0);
        ASSERT(fp_ != 0);
        
        context.op = *ip_++;
        funcTable_[context.op](context);
    }
}

Activation Interpreter::EnsureActivation(Object* fp) {
    Activation activation = FrameActivation(fp);
    if (activation == nullptr) {
        activation = H->AllocateActivation();  // SAFEPOINT
        activation->set_sender_fp(fp);
        activation->set_bci(static_cast<SmallInteger>(nil));
        activation->set_method(FrameMethod(fp));
        if (FlagsIsClosure(FrameFlags(fp))) {
            Closure closure = static_cast<Closure>(FrameTemp(fp, -1));
            ASSERT(closure->IsClosure());
            activation->set_closure(closure);
        } else {
            activation->set_closure(static_cast<Closure>(nil), kNoBarrier);
        }
        activation->set_receiver(FrameReceiver(fp));
        // Note this differs from Cog, which also copies the parameters. It may help
        // some debugging cases if parameters remain available in returned-from
        // activations, but for now it is slightly simpler to treat all locals
        // uniformly.
        activation->set_stack_depth(SmallInteger::New(0));
        
        FrameActivationPut(fp, activation);
    }
    return activation;
}


Activation Interpreter::FlushAllFrames() {
    Activation top = EnsureActivation(fp_);  // SAFEPOINT
    HandleScope h1(H, reinterpret_cast<Object*>(&top));
    
    while (fp_ != 0) {
        EnsureActivation(fp_);  // SAFEPOINT
        
        Object* saved_fp = FrameSavedFP(fp_);
        Activation sender;
        if (saved_fp != 0) {
            sender = EnsureActivation(saved_fp);  // SAFEPOINT
        } else {
            sender = FrameBaseSender(fp_);
            ASSERT((sender == nil) || sender->IsActivation());
        }
        ASSERT((sender == nil) || sender->IsActivation());
        
        Activation activation = FrameActivation(fp_);
        activation->set_sender(sender);
        activation->set_bci(activation->method()->BCI(ip_));
        
        intptr_t num_args = FlagsNumArgs(FrameFlags(fp_));
        intptr_t num_temps = num_args + FrameNumLocals(fp_, sp_);
        for (intptr_t i = 0; i < num_temps; i++) {
            activation->set_temp(i, FrameTemp(fp_, i));
        }
        activation->set_stack_depth(SmallInteger::New(num_temps));
        
        ip_ = FrameSavedIP(fp_);
        sp_ = FrameSavedSP(fp_);
        fp_ = saved_fp;
    }
    
    ip_ = 0;  // Was base sender.
    ASSERT(sp_ == stack_base_);
    ASSERT(fp_ == 0);
#if defined(DEBUG)
    for (intptr_t i = 0; i < kStackSlots; i++) {
        stack_limit_[i] = static_cast<Object>(kUninitializedWord);
    }
#endif
    
    return top;
}


bool Interpreter::HasLivingFrame(Activation activation) {
  if (!activation->sender()->IsSmallInteger()) {
    return false;
  }

  Object* activation_fp = activation->sender_fp();
  Object* fp = fp_;
  while (fp != 0) {
    if (fp == activation_fp) {
      if (FrameActivation(fp) == activation) {
        return true;
      }
      break;
    }
    fp = FrameSavedFP(fp);
  }

  // Frame is gone.
  activation->set_sender(static_cast<Activation>(nil), kNoBarrier);
  activation->set_bci(static_cast<SmallInteger>(nil));
  return false;
}


Activation Interpreter::CurrentActivation() {
  return EnsureActivation(fp_);  // SAFEPOINT
}


void Interpreter::SetCurrentActivation(Activation new_activation) {
  ASSERT(new_activation->IsActivation());

  if (fp_ != 0) {
    HandleScope h1(H, reinterpret_cast<Object*>(&new_activation));
    FlushAllFrames();  // SAFEPOINT
  }

  CreateBaseFrame(new_activation);
}


Object Interpreter::ActivationSender(Activation activation) {
  if (HasLivingFrame(activation)) {
    Object* fp = activation->sender_fp();
    Object* sender_fp = FrameSavedFP(fp);
    if (sender_fp == 0) {
      return FrameBaseSender(fp);
    }
    return EnsureActivation(sender_fp);  // SAFEPOINT
  } else {
    return activation->sender();
  }
}


void Interpreter::ActivationSenderPut(Activation activation,
                                      Activation new_sender) {
  ASSERT(!new_sender->IsSmallInteger());
  ASSERT((new_sender == nil) || new_sender->IsActivation());
  if (HasLivingFrame(activation)) {
    Activation top;
    {
      HandleScope h1(H, reinterpret_cast<Object*>(&activation));
      HandleScope h2(H, reinterpret_cast<Object*>(&new_sender));
      top = FlushAllFrames();  // SAFEPOINT
    }
    activation->set_sender(new_sender);
    CreateBaseFrame(top);
  } else {
    activation->set_sender(new_sender);
  }
}


Object Interpreter::ActivationBCI(Activation activation) {
  if (activation->sender()->IsSmallInteger()) {
    Object* activation_fp = activation->sender_fp();
    Object* fp = fp_;
    const uint8_t* ip = ip_;
    while (fp != 0) {
      if (fp == activation_fp) {
        if (FrameActivation(fp) == activation) {
          return FrameMethod(fp)->BCI(ip);
        }
        break;
      }
      ip = FrameSavedIP(fp);
      fp = FrameSavedFP(fp);
    }
    // Frame is gone.
    activation->set_sender(static_cast<Activation>(nil), kNoBarrier);
    activation->set_bci(static_cast<SmallInteger>(nil));
  }

  return activation->bci();
}


void Interpreter::ActivationBCIPut(Activation activation,
                                   SmallInteger new_bci) {
  if (HasLivingFrame(activation)) {
    Activation top;
    {
      HandleScope h1(H, reinterpret_cast<Object*>(&activation));
      HandleScope h2(H, reinterpret_cast<Object*>(&new_bci));
      top = FlushAllFrames();  // SAFEPOINT
    }
    activation->set_bci(new_bci);
    CreateBaseFrame(top);
  } else {
    return activation->set_bci(new_bci);
  }
}


void Interpreter::ActivationMethodPut(Activation activation,
                                      Method new_method) {
  if (HasLivingFrame(activation)) {
    Activation top;
    {
      HandleScope h1(H, reinterpret_cast<Object*>(&activation));
      HandleScope h2(H, reinterpret_cast<Object*>(&new_method));
      top = FlushAllFrames();  // SAFEPOINT
    }
    activation->set_method(new_method);
    CreateBaseFrame(top);
  } else {
    activation->set_method(new_method);
  }
}


void Interpreter::ActivationClosurePut(Activation activation,
                                       Closure new_closure) {
  if (HasLivingFrame(activation)) {
    Activation top;
    {
      HandleScope h1(H, reinterpret_cast<Object*>(&activation));
      HandleScope h2(H, reinterpret_cast<Object*>(&new_closure));
      top = FlushAllFrames();  // SAFEPOINT
    }
    activation->set_closure(new_closure);
    CreateBaseFrame(top);
  } else {
    activation->set_closure(new_closure);
  }
}


void Interpreter::ActivationReceiverPut(Activation activation,
                                        Object new_receiver) {
  if (HasLivingFrame(activation)) {
    Activation top;
    {
      HandleScope h1(H, reinterpret_cast<Object*>(&activation));
      HandleScope h2(H, reinterpret_cast<Object*>(&new_receiver));
      top = FlushAllFrames();  // SAFEPOINT
    }
    activation->set_receiver(new_receiver);
    CreateBaseFrame(top);
  } else {
    activation->set_receiver(new_receiver);
  }
}


Object Interpreter::ActivationTempAt(Activation activation, intptr_t index) {
  if (HasLivingFrame(activation)) {
    Object* fp = activation->sender_fp();
    return FrameTemp(fp, index);
  } else {
    return activation->temp(index);
  }
}


void Interpreter::ActivationTempAtPut(Activation activation,
                                      intptr_t index,
                                      Object value) {
  if (HasLivingFrame(activation)) {
    Object* fp = activation->sender_fp();
    return FrameTempPut(fp, index, value);
  } else {
    return activation->set_temp(index, value);
  }
}



intptr_t Interpreter::ActivationTempSize(Activation activation) {
  if (activation->sender()->IsSmallInteger()) {
    Object* activation_fp = activation->sender_fp();
    Object* sp = sp_;
    Object* fp = fp_;
    while (fp != 0) {
      if (fp == activation_fp) {
        if (FrameActivation(fp) == activation) {
          return FlagsNumArgs(FrameFlags(fp)) + FrameNumLocals(fp, sp);
        }
        break;
      }
      sp = FrameSavedSP(fp);
      fp = FrameSavedFP(fp);
    }

    // Frame is gone.
    activation->set_sender(static_cast<Activation>(nil), kNoBarrier);
    activation->set_bci(static_cast<SmallInteger>(nil));
  }

  return activation->stack_depth()->value();
}


void Interpreter::ActivationTempSizePut(Activation activation,
                                        intptr_t new_size) {
  if (HasLivingFrame(activation)) {
    Activation top;
    {
      HandleScope h1(H, reinterpret_cast<Object*>(&activation));
      HandleScope h2(H, reinterpret_cast<Object*>(&new_size));
      top = FlushAllFrames();  // SAFEPOINT
    }
    intptr_t old_size = activation->StackDepth();
    for (intptr_t i = old_size; i < new_size; i++) {
      activation->set_temp(i, nil, kNoBarrier);
    }
    activation->set_stack_depth(SmallInteger::New(new_size));
    CreateBaseFrame(top);
  } else {
    intptr_t old_size = activation->StackDepth();
    for (intptr_t i = old_size; i < new_size; i++) {
      activation->set_temp(i, nil, kNoBarrier);
    }
    activation->set_stack_depth(SmallInteger::New(new_size));
  }
}


void Interpreter::GCPrologue() {
  // Convert IPs to BCIs. The makes every slot on the stack a valid object
  // pointer. Frame flags and saved FPs are valid as SmallIntegers.

  Object* fp = fp_;
  const uint8_t** ip_slot = &ip_;

  while (fp != 0) {
    SmallInteger bci = FrameMethod(fp)->BCI(*ip_slot);
    *ip_slot = reinterpret_cast<const uint8_t*>(static_cast<uword>(bci));

    ip_slot = FrameSavedIPSlot(fp);
    fp = FrameSavedFP(fp);
  }
}


void Interpreter::GCEpilogue() {
  // Convert BCIs to IPs. Invalidate lookup caches.

  Object* fp = fp_;
  const uint8_t** ip_slot = &ip_;

  while (fp != 0) {
    const SmallInteger bci =
        static_cast<const SmallInteger>(reinterpret_cast<uword>(*ip_slot));
    *ip_slot = FrameMethod(fp)->IP(bci);

    ip_slot = FrameSavedIPSlot(fp);
    fp = FrameSavedFP(fp);
  }

#if LOOKUP_CACHE
  lookup_cache_.Clear();
#endif
}

}  // namespace psoup
