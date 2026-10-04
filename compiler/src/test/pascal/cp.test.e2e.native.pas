{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.native;

{ E2E tests for the native code-generation backend (--backend native).

  These compile a program with TCodeGenNative (no QBE), link with cc, and run.
  The correctness oracle is parity with the QBE path on the same source; as the
  backend grows, tests here mirror the behaviour the QBE e2e suites already
  cover, run through the native path.

  Milestone coverage:
    M1 — empty program compiles, links, and exits 0.
    M2 — integer arithmetic (+ - * div mod, nesting, precedence) and
         Write/WriteLn of integers.
    M3 — control flow: if/else, while, repeat, and the comparison operators
         (= <> < > <= >=).
    M4 — program-global integer variables (declare, assign, read) and the for
         loop (to / downto, nesting, end-expression evaluated once), plus
         counter-driven while/repeat.
    M5 — user procedures/functions: integer value parameters, integer/void
         return via Result, locals in a stack frame, direct calls (including
         in expressions and nested), recursion, and for loops over a local.
         Also: the wider integer family — Byte, Word, SmallInt, Int64 (and
         signed/unsigned cousins) as globals, locals, parameters and return
         values; mixed-width arithmetic (Int64 promotion); and explicit
         type-cast conversions Byte(X) / Word(X) / Int64(X) that
         truncate/extend correctly.
         Also: var/out parameters — pass by reference (pointer passing),
         read/write through the pointer, pass-through to another var param,
         and wider-int var params (Int64, Byte). }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2ENativeTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_Native_EmptyProgram_ExitsZero;
    procedure TestRun_Native_IntArithmetic_WriteLn;
    procedure TestRun_Native_DivModAndNesting;
    procedure TestRun_Native_WriteNoNewline;
    procedure TestRun_Native_IfElse;
    procedure TestRun_Native_ComparisonsAndNestedIf;
    procedure TestRun_Native_Repeat;
    procedure TestRun_Native_VarsAndForLoop;
    procedure TestRun_Native_DownToAndNestedFor;
    procedure TestRun_Native_CounterLoops;
    procedure TestRun_Native_ForEndEvaluatedOnce;
    procedure TestRun_Native_FunctionsAndCalls;
    procedure TestRun_Native_Recursion;
    { Stage-1 register promotion: mixed-width promoted scalars (Byte
      param in %r14b forms, Int64 Result) must compute exactly as the
      slot-resident lowering did. }
    procedure TestRun_Native_PromotedWidthMix;
    { An exception raised INSIDE a promoted function longjmps past its
      epilogue; the catcher's setjmp must restore %r14/%r15 so an OUTER
      promoted frame's register-resident local survives the unwind. }
    procedure TestRun_Native_RaiseThroughPromotedFrame;
    { The except path parks the exception in %r15 across handler bodies;
      the catching function must preserve its CALLER's %r15 (a promoted
      local).  Latent ABI hole before promotion — pinned here. }
    procedure TestRun_Native_CatcherPreservesR15Local;
    { A nested procedure calling a method on a CAPTURED class-typed outer
      local: the native receiver path fell through to a global-symbol
      load (garbage pointer) instead of dereferencing the _cap_ pointer. }
    procedure TestRun_Native_NestedProcMethodOnCapturedLocal;
    { Phase-1 inlining behaviour: early-Exit chains, two inlined sites
      combined in one expression (the shared-scratch-area + argument
      staging shape that regressed during bring-up), an inline site
      inside an argument of another inline site, and a callee param
      shadowing a caller local's name. }
    procedure TestRun_Native_InlineLeafShapes;
    procedure TestRun_Native_ForLoopOverLocal;
    procedure TestRun_Native_WiderIntGlobals;
    procedure TestRun_Native_Int64Arithmetic;
    procedure TestRun_Native_WiderIntParamsAndReturn;
    procedure TestRun_Native_TypeCastConversions;
    procedure TestRun_Native_SignednessAndWraparound;
    procedure TestRun_Native_WriteUnsigned32;
    procedure TestRun_Native_VarParamSwap;
    procedure TestRun_Native_VarParamPassThrough;
    procedure TestRun_Native_VarParamWiderInt;
    procedure TestRun_Native_OutParam;
    procedure TestRun_Native_ForBreak;
    procedure TestRun_Native_WhileContinue;
    procedure TestRun_Native_ExitFromFunction;
    procedure TestRun_Native_ExitValueShorthand;
    procedure TestRun_Native_SevenArgs;
    procedure TestRun_Native_EightArgs;
    procedure TestRun_Native_TenArgs;
    procedure TestRun_Native_OverflowFloatArgs;
    { Regression: an implicit-Self method call in statement position with more
      argument slots than fit in registers (Self + 6 args = 7 > 6).  The
      statement-call fast path indexed SysVArgRegs64 past %r9, reading adjacent
      data as a garbage string pointer and crashing _StringConcat during a
      later native self-compile.  Must spill the surplus to the stack. }
    procedure TestRun_Native_ImplicitSelfMethod_SixArgs;
    procedure TestRun_Native_ImplicitSelfMethod_SevenArgs;
    procedure TestRun_Native_IndirectCall_BareProc;
    procedure TestRun_Native_IndirectCall_BareFunc;
    procedure TestRun_Native_Record_GlobalReadWrite;
    procedure TestRun_Native_Record_LocalReadWrite;
    procedure TestRun_Native_Record_AsParam;
    procedure TestRun_Native_StaticArray_GlobalReadWrite;
    procedure TestRun_Native_StaticArray_LocalReadWrite;
    procedure TestRun_Native_StaticArray_NonZeroLow;
    { TODO M7: method-pointer calls require class support }
    procedure TestRun_Native_IndirectCall_MethodPtr;
    procedure TestRun_Native_MethodAddress_VarString;
    { TODO M7: record-returning function — deferred until sret/aggregate support }
    procedure TestRun_Native_RecordReturnFunction;
    procedure TestRun_Native_Record_NestedFieldAssign;
    { M6 — floats }
    procedure TestRun_Native_Double_GlobalReadWrite;
    procedure TestRun_Native_Double_LocalReadWrite;
    procedure TestRun_Native_Double_Arithmetic;
    procedure TestRun_Native_Double_Comparison;
    procedure TestRun_Native_Double_WriteLn;
    procedure TestRun_Native_Single_GlobalReadWrite;
    procedure TestRun_Native_Double_FuncParam;
    procedure TestRun_Native_Double_FuncReturn;
    procedure TestRun_Native_FloatCompareInOrAnd;
    procedure TestRun_Native_LocalFloatConst;

    { M7c — string operations }
    procedure TestRun_Native_String_WriteLnLiteral;
    procedure TestRun_Native_String_AssignAndWrite;
    procedure TestRun_Native_String_Concat;
    procedure TestRun_Native_String_Length;
    procedure TestRun_Native_String_Pos;
    procedure TestRun_Native_String_Copy;
    procedure TestRun_Native_String_UpperCase;
    procedure TestRun_Native_String_IntToStr;
    procedure TestRun_Native_String_StrToInt;
    procedure TestRun_Native_String_Param;
    procedure TestRun_Native_String_FuncReturn;
    procedure TestRun_Native_String_Delete;
    procedure TestRun_Native_String_SetLength;
    procedure TestRun_Native_String_Subscript;
    procedure TestRun_Native_String_SameText;
    procedure TestRun_Native_String_Format_IntArg;
    procedure TestRun_Native_String_Format_StrArg;
    procedure TestRun_Native_String_Format_MixedArgs;
    procedure TestRun_Native_String_Format_FuncCallArg;
    procedure TestRun_Native_String_ConcatWithInt;
    procedure TestRun_Native_String_ChrConcat;

    { Local dynamic-array variables must start nil: SetLength reads the old
      pointer and the epilogue releases it.  The dirty-stack helper makes the
      uninitialised slot hold garbage rather than lucky zeros. }
    procedure TestRun_Native_LocalDynArray_DirtyStack;

    { M7d — exception handling }
    procedure TestRun_Native_TryFinally_Normal;
    procedure TestRun_Native_TryFinally_NestedNormal;
    procedure TestRun_Native_TryFinally_ExitUnwind;
    procedure TestRun_Native_TryFinally_BreakUnwind;
    procedure TestRun_Native_TryExcept_Bare;
    procedure TestRun_Native_TryExcept_TypedHandler;
    procedure TestRun_Native_TryExcept_SubclassMatch;
    procedure TestRun_Native_TryExcept_BareRaisePropagate;
    procedure TestRun_Native_TryExcept_ElseBody;
    procedure TestRun_Native_ExitThroughNestedFinally;

    { M7e — open arrays and dynamic arrays }
    procedure TestRun_Native_OpenArray_Sum;
    procedure TestRun_Native_OpenArray_HighLow;
    procedure TestRun_Native_OpenArray_Length;
    procedure TestRun_Native_StaticToOpen_Length;
    procedure TestRun_Native_StaticToOpen_Sum;
    procedure TestRun_Native_StaticToOpen_PassToNested;
    procedure TestRun_Native_DynArray_SetLengthAndAccess;
    procedure TestRun_Native_DynArray_LengthAndHigh;

    { M7f — interface dispatch through itab }
    procedure TestRun_Native_Interface_ZeroArgDispatch;
    procedure TestRun_Native_Interface_ArgDispatch;
    procedure TestRun_Native_Interface_ProcDispatch;
    procedure TestRun_Native_Interface_IntfToIntfCopy;
    procedure TestRun_Native_Interface_AsCast;
    procedure TestRun_Native_Interface_NilClear;
    { Regression (issue #64): interface-typed field with same name as a
      program-level global of a different type }
    procedure TestRun_Native_InterfaceField_ShadowsGlobal;
    { Interface parameters — fat pointer passing through all call sites }
    procedure TestRun_Native_IntfParam_Proc;
    procedure TestRun_Native_IntfParam_Method;
    procedure TestRun_Native_IntfParam_Constructor;
    procedure TestRun_Native_IntfParam_Inherited;
    procedure TestRun_Native_IntfParam_ClassExpr;

    { M8 — inherited calls }
    procedure TestRun_Native_Inherited_Proc;
    procedure TestRun_Native_Inherited_FuncSetsResult;
    { M8 — var/out params to a method call }
    procedure TestRun_Native_MethodVarParam_Mutates;
    procedure TestRun_Native_MethodVarParam_Swap;

    { Array field access }
    procedure TestRun_Native_RecordArrayField_StaticRead;

    { ARC on class fields }
    procedure TestRun_Native_ArcClassField_StoreAndRead;
    procedure TestRun_Native_ArcStringField_StoreAndRead;
    procedure TestRun_Native_ArcClassAssignNil_Destroys;
    { ARC for dyn-array / interface / nested-record fields, owned-return stores,
      and implicit-Self managed-field stores (native-backend parity with QBE). }
    procedure TestRun_Native_ArcDynArrayField_StoreAndRead;
    procedure TestRun_Native_ArcInterfaceField_AssignAndDispatch;
    procedure TestRun_Native_IntfFieldDispatch;
    procedure TestRun_Native_IntfFieldReadIntoLocal;
    procedure TestRun_Native_RetValSurvivesArcRelease;
    procedure TestRun_Native_IntfArgToMethod;
    procedure TestRun_Native_ArcNestedRecordField_FullCleanup;
    procedure TestRun_Native_ArcStringReturnToField_NoDoubleRetain;
    procedure TestRun_Native_ArcImplicitSelfStringField_Reassign;

    { ARC value param retain/release }
    procedure TestRun_Native_ArcValueParam_String;
    procedure TestRun_Native_ArcValueParam_Class;

    { Address-of expressions }
    procedure TestRun_Native_AddrOf_LocalVariable;
    procedure TestRun_Native_AddrOf_StaticArrayElement;
    procedure TestRun_Native_AddrOf_DynArrayElement;
    procedure TestRun_Native_AddrOf_RecordFieldArrayElem;
    procedure TestRun_Native_AddrOf_MethodPointer;

    { Bitwise NOT }
    procedure TestRun_Native_BitwiseNot_Integer;
    procedure TestRun_Native_BitwiseNot_Bitmask;

    { SizeOf }
    procedure TestRun_Native_SizeOf_Record;
    procedure TestRun_Native_SizeOf_GenericRecord;

    { Generics }
    procedure TestRun_Native_GenericRecord_Method;
    procedure TestRun_Native_GenericClass_Method;
    procedure TestRun_Native_GenericFunc_Standalone;
    procedure TestRun_Native_GenericClass_Interface;

    { Multi-unit whole-program native path (TX86_64Backend.EmitUnit/AppendProgram). }
    procedure TestRun_Native_MultiUnit_PlainFunction;
    procedure TestRun_Native_MultiUnit_StringFunction;
    procedure TestRun_Native_MultiUnit_Class;
    procedure TestRun_Native_MultiUnit_Interface;
    procedure TestRun_Native_MultiUnit_GlobalsAndInit;

    { By-value record params (memcpy + ARC on managed leaves). }
    procedure TestRun_Native_RecordParam_ReadOnly;
    procedure TestRun_Native_RecordParam_Mutate;
    procedure TestRun_Native_RecordParam_ThreeStrings;
    procedure TestRun_Native_RecordParam_IntOnly;
    procedure TestRun_Native_RecordParam_InlineSretArg;
    procedure TestRun_Native_RecordParam_ConstSkipsArc;
    procedure TestRun_Native_ShortCircuit_AndSkipsRhs;
    procedure TestRun_Native_ShortCircuit_OrSkipsRhs;
    procedure TestRun_Native_ShortCircuit_AndNilGuard;
    procedure TestRun_Native_ProceduralParam;
    procedure TestRun_Native_IsExpr_Class;
    procedure TestRun_Native_AsExpr_Class;
    procedure TestRun_Native_SupportsExpr;
    procedure TestRun_Native_IndirectFuncCallExpr;

    { Gap #6 — builtins }
    procedure TestRun_Native_Builtin_Ord;
    procedure TestRun_Native_Builtin_Assigned;
    procedure TestRun_Native_Builtin_Abs;
    procedure TestRun_Native_Builtin_Halt;
    procedure TestRun_Native_Builtin_RoundTrunc;
    procedure TestRun_Native_Builtin_CompareStr;
    procedure TestRun_Native_Builtin_UpCase;
    procedure TestRun_Native_Builtin_Int64ToStr;

    { Gap #5 — nested (local) procedures }
    procedure TestRun_Native_NestedProc_ReadCapture;
    procedure TestRun_Native_NestedProc_WriteCapture;
    { leg 17 — a captured STRING var written inside a nested proc runs the ARC
      store through the capture pointer; must stay leak-free (retain-new /
      release-old).  Two locals captured (the compiler's own PromoRewrite
      shape) plus repeated reassignment to exercise release-old. }
    procedure TestRun_Native_NestedProc_CaptureString_LeakFree;
    procedure TestRun_Native_NestedProc_CaptureTwoLocals;
    { leg 17 Finding-1 regression: captures + register args exceed 8, forcing
      stack-passed args.  The outgoing stack area must be reserved (the capture
      pointer args are counted), else the overflow args clobber the caller's
      frame.  Runs on both backends. }
    procedure TestRun_Native_NestedProc_CaptureArgsOverflowToStack;
    { BUG-20260720-grandparent-capture: a routine nested 3+ levels deep can
      capture a variable owned two-or-more levels up.  The intermediate levels
      forward the capture pointer.  Read, write, 4-level chain. }
    procedure TestRun_Native_NestedProc_GrandparentCapture_Read;
    procedure TestRun_Native_NestedProc_GrandparentCapture_Write;
    procedure TestRun_Native_NestedProc_GreatGrandparentCapture;
    { leg 19: a nested proc captures an enclosing routine's CLASS or RECORD
      variable and uses it as a field-access base / method receiver. }
    procedure TestRun_Native_NestedProc_CaptureClassBase_ReadWriteCall;
    procedure TestRun_Native_NestedProc_CaptureRecordBase;
    { leg 19 review regression: a captured VAR-PARAM class base needs a second
      deref on the WRITE path too (its slot holds the caller's address). }
    procedure TestRun_Native_NestedProc_CaptureVarParamClass_FieldWrite;
    { BUG-20260720-method-nested-proc-mangle: two classes each with a method
      DoIt containing a nested Inner must link (distinct symbols) and each DoIt
      must call its OWN Inner.  Plus a multi-level chain.  All backends. }
    procedure TestRun_Native_NestedProc_MethodMangle_NoCollision;
    procedure TestRun_Native_NestedProc_MultiLevelMangle;

    { Trig / math builtins with Single dispatch }
    procedure TestRun_Native_Builtin_SinCos;
    procedure TestRun_Native_Builtin_SqrtDouble;

    { Typed-pointer float writes }
    procedure TestRun_Native_DoublePtrWrite;
    procedure TestRun_Native_SinglePtrWrite_NoAdjacentClobber;

    { Inc/Dec on non-simple-variable arguments }
    procedure TestRun_Native_IncDec_RecordField;
    procedure TestRun_Native_IncDec_PtrDeref;

    { Type-cast on pointer-sized types }
    procedure TestRun_Native_TypeCast_PointerClass;

    { Property reads via getter methods }
    procedure TestRun_Native_PropertyRead_Simple;
    procedure TestRun_Native_PropertyRead_Indexed;

    { Property writes via setter methods }
    procedure TestRun_Native_PropertyWrite_Simple;
    procedure TestRun_Native_PropertyWrite_Indexed;

    { Built-in class access }
    procedure TestRun_Native_ClassName;

    { Method call >5 user args }
    procedure TestRun_Native_MethodCall_ManyArgs;

    { Implicit-Self class field access — FInner.FVal inside a method }
    procedure TestRun_Native_ImplicitSelf_ClassField;

    { Implicit-Self property getter call inside a method }
    procedure TestRun_Native_ImplicitSelf_PropertyGetter;

    { Const array data emission + ConstArraySymbol reference }
    procedure TestRun_Native_ConstArray_StringElements;

    { Virtual method dispatch in expression context }
    procedure TestRun_Native_VirtualDispatch_Expr;

    { String content equality via _StringEquals (not pointer cmp) }
    procedure TestRun_Native_StringEquality;

    { var/out string params: assignment must write through indirection pointer }
    procedure TestRun_Native_OutParam_String;
    procedure TestRun_Native_VarParam_String;

    { Constructor with args that require function calls must not lose Self }
    procedure TestRun_Native_Constructor_CallArg;

    { Method call returning a record (sret convention) }
    procedure TestRun_Native_MethodSretReturn;
    procedure TestRun_Native_FieldSretReturn;
    procedure TestRun_Native_ImplicitSelfMethodCall;
    procedure TestRun_Native_RecordFieldCopy;
    procedure TestRun_Native_SretFieldARC;

    { M8b — method call on a var-param class receiver (double dereference). }
    procedure TestRun_Native_VarParam_MethodCall;

    { M8b — named string constant used in assignment and as argument. }
    procedure TestRun_Native_StringConst;

    { M8b — sret forwarding: outer function assigns Result from inner sret call. }
    procedure TestRun_Native_SretForward;
    { M8b — for-loop with recursive call in body (end-bound must be frame-local). }
    procedure TestRun_Native_ForLoop_RecursiveBody;
    { M8b — open-array literal as method argument. }
    procedure TestRun_Native_MethodCall_OpenArray;
    { M8b — passing an interface-typed field as argument to a function. }
    procedure TestRun_Native_IntfFieldAsArg;
    { M8b — nil assignment to interface-typed fields (implicit-Self and non-Self). }
    procedure TestRun_Native_IntfFieldNilAssign;
    { M8b — dynarray element ARC: A[I] := 'new' releases old string at A[I]. }
    procedure TestRun_Native_DynArrayElemArc_String;
    { M8b — function returning interface: sret convention, obj+itab propagated. }
    procedure TestRun_Native_IntfFuncReturn;
    { Class-receiver method call returning an interface (Obj.Make()) into
      local/global vars, sret Result, and an implicit-Self field. }
    procedure TestRun_Native_IntfFromClassMethod;
    { Virtual method returning a record must dispatch through the vtable —
      a static call would bind the base-class body. }
    procedure TestRun_Native_RecReturnVirtualOverride;
    { M8b — interface-field := function-returning-interface (sret into field). }
    procedure TestRun_Native_IntfFieldFromFunc;
    procedure TestRun_Native_IntfVarParamAndChainedReceiver;
    procedure TestRun_Native_VarOpenArray_ElemReadWrite;
    { M8b — weak interface variable: _WeakAssign/_WeakClear instead of ARC. }
    procedure TestRun_Native_WeakInterfaceVar;
    { M8b — sret temp record field release: managed fields of a record
      returned by a function and passed directly as an arg are released. }
    procedure TestRun_Native_SretTempFieldRelease;

    { Record-by-value returns — all SysV ABI classification shapes }
    procedure TestRun_Native_RecReturn_RcInt2_TwoInt64;
    procedure TestRun_Native_RecReturn_RcSSE1_Double;
    procedure TestRun_Native_RecReturn_RcSSE1_Single;
    procedure TestRun_Native_RecReturn_RcSSE2_TwoDouble;
    procedure TestRun_Native_RecReturn_RcIntSSE;
    procedure TestRun_Native_RecReturn_RcSSEInt;
    procedure TestRun_Native_RecReturn_Nested_RcInt2;
    procedure TestRun_Native_RecReturn_Method_RcInt1;
    procedure TestRun_Native_RecReturn_ManagedStaysSret;
    procedure TestRun_Native_RecordSret_OutParam;
    procedure TestRun_Native_StaticArray_ComputedIndex;
    { Metaclass (class-of) values: bare class name in expression position must
      emit the typeinfo address; ClassCreate constructs through it. }
    procedure TestRun_Native_Metaclass_BareClassRef;
    procedure TestRun_Native_MultiUnit_Metaclass;
    { Open-array literal that is NOT the first argument: the literal's stack
      block must be hoisted before the argument pushes, or the popq sequence
      pops from inside the block and the callee sees shifted registers. }
    procedure TestRun_Native_OpenArrayLiteral_AfterOtherArgs;
    { var-param argument to an sret (record-returning) call must pass the
      variable's ADDRESS, not its value (regression: movslq instead of
      leaq handed the callee a garbage pointer). }
    procedure TestRun_Native_SretCall_VarParamArg;
    { Record value assigned into a record-typed field of the sret Result
      must be a full ARC-aware copy, not an 8-byte pointer store. }
    procedure TestRun_Native_SretResult_NestedRecordFieldAssign;
    { Regression: implicit-Self method calls whose Self+args exceed six integer
      registers must spill the overflow to the stack (the expression path used
      to abort codegen with 'arg register index 6 out of range'). }
    procedure TestRun_Native_ImplicitSelfCall_RegisterOverflow;
    { Subscripting a string-typed FIELD (Rec.S[I] / Obj.Data[I]) must be
      0-based like every other Blaise subscript (regression: QBE
      subtracted 1, native read garbage through the unhandled path). }
    procedure TestRun_Native_StringFieldCharRead;

    { Zero-initialisation — both backends must guarantee every local variable
      starts at its zero value even on a dirty stack.  Each test category uses
      a Dirty() helper that fills the stack with 0xDEADBEEF garbage before the
      real procedure runs, proving that the zero-init comes from the prologue
      and not from lucky stack layout. }
    procedure TestRun_ZeroInit_ScalarIntegers;
    procedure TestRun_ZeroInit_FloatLocals;
    procedure TestRun_ZeroInit_BooleanAndChar;
    procedure TestRun_ZeroInit_PointerLocals;
    procedure TestRun_ZeroInit_EnumLocal;
    procedure TestRun_ZeroInit_SetLocal;
    procedure TestRun_ZeroInit_RecordWithMixedFields;
    procedure TestRun_ZeroInit_StaticArray;
    procedure TestRun_ZeroInit_ThreadVar;
    procedure TestRun_ZeroInit_GlobalVars;
  end;

implementation

procedure TE2ENativeTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-native');
end;

const
  LE = #10;

  SrcEmpty = '''
    program Prg;
    begin
    end.
    ''';

  SrcArith = '''
    program Prg;
    begin
      WriteLn(2 + 3 * 4);
      WriteLn(100 - 58)
    end.
    ''';

  SrcDivMod = '''
    program Prg;
    begin
      WriteLn(20 div 6);
      WriteLn(20 mod 6);
      WriteLn((2 + 3) * (10 - 4));
      WriteLn(7 - 10)
    end.
    ''';

  SrcWriteNoNL = '''
    program Prg;
    begin
      Write(1);
      Write(2);
      WriteLn(3)
    end.
    ''';

  SrcIfElse = '''
    program Prg;
    begin
      if 5 > 3 then WriteLn(1) else WriteLn(0);
      if 2 > 9 then WriteLn(1) else WriteLn(0);
      if 4 = 4 then WriteLn(44)
    end.
    ''';

  SrcComparisons = '''
    program Prg;
    begin
      if 3 < 5 then WriteLn(11);
      if 5 <= 5 then WriteLn(22);
      if 6 >= 9 then WriteLn(33) else WriteLn(44);
      if 7 <> 8 then WriteLn(55);
      if (2 + 2) = 4 then
        if 10 > 1 then WriteLn(66)
    end.
    ''';

  { while with a false condition never runs; repeat runs once then exits when
    the until condition is true.  (Counter-driven loops arrive with M4 locals.) }
  SrcRepeat = '''
    program Prg;
    begin
      while 3 > 5 do WriteLn(999);
      repeat WriteLn(8) until 1 = 1
    end.
    ''';

  SrcVarsForLoop = '''
    program Prg;
    var i, sum: Integer;
    begin
      sum := 0;
      for i := 1 to 5 do
        sum := sum + i;
      WriteLn(sum)
    end.
    ''';

  SrcDownToNested = '''
    program Prg;
    var i, j, total: Integer;
    begin
      for i := 5 downto 1 do Write(i);
      WriteLn(0);
      total := 0;
      for i := 1 to 3 do
        for j := 1 to 3 do
          total := total + 1;
      WriteLn(total)
    end.
    ''';

  SrcCounterLoops = '''
    program Prg;
    var n: Integer;
    begin
      n := 0;
      while n < 3 do
      begin
        Write(n);
        n := n + 1
      end;
      WriteLn(9);
      n := 0;
      repeat
        n := n + 2
      until n >= 6;
      WriteLn(n)
    end.
    ''';

  SrcForEndOnce = '''
    program Prg;
    var i, limit, count: Integer;
    begin
      limit := 3;
      count := 0;
      for i := 1 to limit do
      begin
        count := count + 1;
        limit := limit + 10
      end;
      WriteLn(count)
    end.
    ''';

  SrcFunctions = '''
    program Prg;
    function Square(x: Integer): Integer;
    begin
      Result := x * x
    end;
    function Sum3(a, b, c: Integer): Integer;
    begin
      Result := a + b + c
    end;
    procedure PrintTwice(n: Integer);
    begin
      WriteLn(n);
      WriteLn(n)
    end;
    begin
      WriteLn(Square(6));
      WriteLn(Sum3(1, 2, 3));
      PrintTwice(9);
      WriteLn(Square(Square(2)));
      WriteLn(Square(3) + Sum3(10, 20, 30))
    end.
    ''';

  SrcRecursion = '''
    program Prg;
    function Fact(n: Integer): Integer;
    begin
      if n <= 1 then
        Result := 1
      else
        Result := n * Fact(n - 1)
    end;
    begin
      WriteLn(Fact(5));
      WriteLn(Fact(1))
    end.
    ''';

  SrcForOverLocal = '''
    program Prg;
    function SumTo(n: Integer): Integer;
    var i, s: Integer;
    begin
      s := 0;
      for i := 1 to n do s := s + i;
      Result := s
    end;
    begin
      WriteLn(SumTo(10));
      WriteLn(SumTo(100))
    end.
    ''';

  { Wider integer family as program globals: declare, assign, read, and
    WriteLn each.  Byte/Word/SmallInt are stored narrow but read back to the
    full ordinal value; Int64 holds a value beyond 32 bits. }
  SrcWiderIntGlobals = '''
    program Prg;
    var
      b: Byte;
      w: Word;
      s: SmallInt;
      big: Int64;
    begin
      b := 200;
      w := 50000;
      s := -1000;
      big := 5000000000;
      WriteLn(b);
      WriteLn(w);
      WriteLn(s);
      WriteLn(big)
    end.
    ''';

  { Int64 arithmetic must use 64-bit operations: a product that overflows 32
    bits, and addition past the 32-bit boundary. }
  SrcInt64Arith = '''
    program Prg;
    var a, b, r: Int64;
    begin
      a := 100000;
      b := 100000;
      r := a * b;
      WriteLn(r);
      r := 4000000000 + 4000000000;
      WriteLn(r);
      r := r div 1000000;
      WriteLn(r)
    end.
    ''';

  { Wider-int parameters and return values across a call boundary. }
  SrcWiderIntParams = '''
    program Prg;
    function AddBytes(x, y: Byte): Integer;
    begin
      Result := x + y
    end;
    function ScaleBig(n: Int64): Int64;
    begin
      Result := n * 3
    end;
    function ClampWord(w: Word): Word;
    begin
      Result := w
    end;
    begin
      WriteLn(AddBytes(200, 100));
      WriteLn(ScaleBig(2000000000));
      WriteLn(ClampWord(40000))
    end.
    ''';

  { Explicit type-cast conversions truncate (narrowing) and extend (widening)
    exactly like the QBE backend: Byte(X) keeps the low 8 bits, Word(X) the
    low 16; Int64(X) widens a 32-bit value. }
  SrcTypeCasts = '''
    program Prg;
    var i: Integer;
    var big: Int64;
    begin
      i := 300;
      WriteLn(Byte(i));
      i := 70000;
      WriteLn(Word(i));
      i := 1000000;
      big := Int64(i) * Int64(i);
      WriteLn(big)
    end.
    ''';

  { Signedness on read-back: a SmallInt holding a value whose 16-bit pattern
    is negative reads back sign-extended; a Word with the same low-16 bits
    reads back as the large unsigned ordinal. }
  SrcSignedness = '''
    program Prg;
    var s: SmallInt;
    var w: Word;
    begin
      s := -2;
      w := 65534;
      WriteLn(s);
      WriteLn(w);
      WriteLn(s + 5)
    end.
    ''';

  { A Cardinal/UInt32 value above 2^31 must print as the large unsigned value,
    not a negative signed wrap. }
  SrcWriteUnsigned32 = '''
    program Prg;
    var c: Cardinal;
    begin
      c := 3000000000;
      WriteLn(c)
    end.
    ''';

  { Var/out parameter support (M5 continuation). }

  SrcVarParamSwap = '''
    program Prg;
    procedure Swap(var A, B: Integer);
    var T: Integer;
    begin
      T := A; A := B; B := T
    end;
    var X, Y: Integer;
    begin
      X := 3; Y := 7;
      Swap(X, Y);
      WriteLn(X);
      WriteLn(Y)
    end.
    ''';

  { Pass a var param through to another var param (pointer forwarding). }
  SrcVarParamPassThrough = '''
    program Prg;
    procedure Inc10(var N: Integer);
    begin
      N := N + 10
    end;
    procedure DoubleInc(var V: Integer);
    begin
      Inc10(V);
      Inc10(V)
    end;
    var X: Integer;
    begin
      X := 5;
      DoubleInc(X);
      WriteLn(X)
    end.
    ''';

  { Var params with wider integer types. }
  SrcVarParamWiderInt = '''
    program Prg;
    procedure SetBig(var B: Int64);
    begin
      B := 9000000000
    end;
    procedure SetByte(var V: Byte);
    begin
      V := 255
    end;
    var Big: Int64;
    var Small: Byte;
    begin
      Big := 0;
      Small := 0;
      SetBig(Big);
      SetByte(Small);
      WriteLn(Big);
      WriteLn(Small)
    end.
    ''';

  { Out parameter (same ABI as var — pointer passing). }
  SrcOutParam = '''
    program Prg;
    procedure Init(out X, Y: Integer);
    begin
      X := 42;
      Y := 99
    end;
    var A, B: Integer;
    begin
      A := 0; B := 0;
      Init(A, B);
      WriteLn(A);
      WriteLn(B)
    end.
    ''';

  { Break/continue/exit support. }

  SrcForBreak = '''
    program Prg;
    var I, Last: Integer;
    begin
      Last := 0;
      for I := 1 to 100 do
      begin
        Last := I;
        if I = 5 then break
      end;
      WriteLn(Last)
    end.
    ''';

  SrcWhileContinue = '''
    program Prg;
    var I, Sum: Integer;
    begin
      I := 0;
      Sum := 0;
      while I < 10 do
      begin
        I := I + 1;
        if I mod 2 = 0 then continue;
        Sum := Sum + I
      end;
      WriteLn(Sum)
    end.
    ''';

  SrcExitFunc = '''
    program Prg;
    function FirstPositive(X: Integer): Integer;
    begin
      if X > 0 then
      begin Result := X; exit end;
      Result := 0 - X
    end;
    begin
      WriteLn(FirstPositive(7));
      WriteLn(FirstPositive(0 - 9))
    end.
    ''';

  SrcExitValue = '''
    program Prg;
    function Clamp(X, Lo, Hi: Integer): Integer;
    begin
      if X < Lo then Exit(Lo);
      if X > Hi then Exit(Hi);
      Result := X
    end;
    begin
      WriteLn(Clamp(5, 1, 10));
      WriteLn(Clamp(0 - 3, 1, 10));
      WriteLn(Clamp(99, 1, 10))
    end.
    ''';

  { 7 integer args: first 6 in registers, 7th on the stack. }
  SrcSevenArgs = '''
    program Prg;
    function Sum7(A, B, C, D, E, F, G: Integer): Integer;
    begin
      Result := A + B + C + D + E + F + G
    end;
    begin
      WriteLn(Sum7(1, 2, 3, 4, 5, 6, 7))
    end.
    ''';

  { 8 integer args: first 6 in registers, 7th and 8th on the stack. }
  SrcEightArgs = '''
    program Prg;
    function Sum8(A, B, C, D, E, F, G, H: Integer): Integer;
    begin
      Result := A + B + C + D + E + F + G + H
    end;
    function Diff8(A, B, C, D, E, F, G, H: Integer): Integer;
    begin
      Result := A - B - C - D - E - F - G - H
    end;
    begin
      WriteLn(Sum8(1, 2, 3, 4, 5, 6, 7, 8));
      WriteLn(Diff8(100, 1, 2, 3, 4, 5, 6, 7))
    end.
    ''';

  { 10 integer args: first 6 in registers, 7th–10th on the stack. }
  SrcTenArgs = '''
    program Prg;
    function Sum10(A, B, C, D, E, F, G, H, I, J: Integer): Integer;
    begin
      Result := A + B + C + D + E + F + G + H + I + J
    end;
    begin
      WriteLn(Sum10(1, 2, 3, 4, 5, 6, 7, 8, 9, 10))
    end.
    ''';

  { Free-function call with more than 6 register slots AND interspersed float
    args: i1..i5 fill 5 integer registers, d1/d2 take xmm0/xmm1, i6 is the 6th
    integer arg (-> %r9), i7 overflows to the stack.  Regression: the native
    backend's overflow relocation assumed exactly the first six contiguous
    stack slots were register-bound, which is false once floats (which take xmm,
    not integer registers) sit among them — it placed the overflow arg at the
    wrong address and crashed the callee. }
  SrcOverflowFloatArgs = '''
    program Prg;
    procedure P(i1,i2,i3,i4,i5: Int64; d1,d2: Double; i6,i7: Int64);
    begin
      WriteLn(i1,' ',i2,' ',i3,' ',i4,' ',i5,' ',d1,' ',d2,' ',i6,' ',i7)
    end;
    begin
      P(1,2,3,4,5, 6.5, 7.5, 8, 9)
    end.
    ''';

  { Bare procedural-type (no 'of object'): assign a procedure to a variable
    and call through it.  WriteLn is not callable via a proc var in the test
    harness, so we use a user-defined Print procedure. }
  SrcIndirectBareProc = '''
    program Prg;
    type
      TProc = procedure(X: Integer);
    procedure PrintIt(X: Integer);
    begin
      WriteLn(X)
    end;
    var F: TProc;
    begin
      F := @PrintIt;
      F(42);
      F(99)
    end.
    ''';

  { Bare function pointer: assign a function to a variable and call it in
    an expression. }
  SrcIndirectBareFunc = '''
    program Prg;
    type
      TFunc = function(A, B: Integer): Integer;
    function Add(A, B: Integer): Integer;
    begin
      Result := A + B
    end;
    function Mul(A, B: Integer): Integer;
    begin
      Result := A * B
    end;
    var F: TFunc;
    begin
      F := @Add;
      WriteLn(F(3, 4));
      F := @Mul;
      WriteLn(F(3, 4))
    end.
    ''';

  { Method pointer ('of object'): the variable holds a (Code, Data) pair;
    calling it must pass Data as Self.  Uses TMethod + MethodAddress + a cast
    to bind the method pointer, matching the established e2e pattern. }
  SrcIndirectMethodPtr = '''
    program Prg;
    type
      TCounter = class
        FVal: Integer;
      published
        procedure Add(N: Integer);
        function  Get: Integer;
      end;
      TAddProc = procedure(N: Integer) of object;
    procedure TCounter.Add(N: Integer);
    begin
      Self.FVal := Self.FVal + N
    end;
    function TCounter.Get: Integer;
    begin
      Result := Self.FVal
    end;
    var
      C:  TCounter;
      M:  TMethod;
      P:  TAddProc;
    begin
      C      := TCounter.Create();
      M.Code := MethodAddress(C, 'Add');
      M.Data := C;
      P      := TAddProc(M);
      P(10);
      P(5);
      WriteLn(C.Get())
    end.
    ''';

  { MethodAddress with a variable (non-literal) string argument. }
  SrcMethodAddrVarString = '''
    program Prg;
    type
      TCounter = class
        FVal: Integer;
      published
        procedure Add(N: Integer);
        function  Get: Integer;
      end;
      TAddProc = procedure(N: Integer) of object;
    procedure TCounter.Add(N: Integer);
    begin
      Self.FVal := Self.FVal + N
    end;
    function TCounter.Get: Integer;
    begin
      Result := Self.FVal
    end;
    var
      C: TCounter;
      M: TMethod;
      P: TAddProc;
      Name: string;
    begin
      C := TCounter.Create();
      Name := 'Add';
      M.Code := MethodAddress(C, Name);
      M.Data := C;
      P := TAddProc(M);
      P(10);
      P(32);
      WriteLn(C.Get())
    end.
    ''';

  { Record global: declare a record type, write fields from main, read back. }
  SrcRecordGlobal = '''
    program Prg;
    type
      TPoint = record
        X: Integer;
        Y: Integer;
      end;
    var Pt: TPoint;
    begin
      Pt.X := 3;
      Pt.Y := 7;
      WriteLn(Pt.X);
      WriteLn(Pt.Y);
      WriteLn(Pt.X + Pt.Y)
    end.
    ''';

  { Record local inside a function. }
  SrcRecordLocal = '''
    program Prg;
    type
      TRect = record
        W: Integer;
        H: Integer;
      end;
    function Area(W, H: Integer): Integer;
    var R: TRect;
    begin
      R.W := W;
      R.H := H;
      Result := R.W * R.H
    end;
    begin
      WriteLn(Area(4, 5));
      WriteLn(Area(6, 7))
    end.
    ''';

  { Record fields passed as scalar parameters and result. }
  SrcRecordParam = '''
    program Prg;
    type
      TPoint = record
        X: Integer;
        Y: Integer;
      end;
    function ManhattanDist(X1, Y1, X2, Y2: Integer): Integer;
    var DX, DY: Integer;
    begin
      DX := X2 - X1;
      DY := Y2 - Y1;
      if DX < 0 then DX := 0 - DX;
      if DY < 0 then DY := 0 - DY;
      Result := DX + DY
    end;
    var P1, P2: TPoint;
    begin
      P1.X := 1; P1.Y := 2;
      P2.X := 4; P2.Y := 6;
      WriteLn(ManhattanDist(P1.X, P1.Y, P2.X, P2.Y))
    end.
    ''';

  { Static array global: declare at program level, write elements, read back. }
  SrcStaticArrayGlobal = '''
    program Prg;
    var A: array[0..4] of Integer;
    begin
      A[0] := 10;
      A[2] := 30;
      A[4] := 50;
      WriteLn(A[0]);
      WriteLn(A[2]);
      WriteLn(A[4]);
      WriteLn(A[0] + A[2] + A[4])
    end.
    ''';

  { Static array local inside a function. }
  SrcStaticArrayLocal = '''
    program Prg;
    function SumArray: Integer;
    var
      B: array[0..2] of Integer;
    begin
      B[0] := 1;
      B[1] := 2;
      B[2] := 3;
      Result := B[0] + B[1] + B[2]
    end;
    begin
      WriteLn(SumArray())
    end.
    ''';

  { Static array with non-zero lower bound: A[1..3]. }
  SrcStaticArrayNonZeroLow = '''
    program Prg;
    var C: array[1..3] of Integer;
    begin
      C[1] := 100;
      C[2] := 200;
      C[3] := 300;
      WriteLn(C[1] + C[2] + C[3])
    end.
    ''';

  { TODO M7: a function that returns a record value.  The QBE backend handles
    this via the sret convention (hidden first pointer param); the native backend
    must do the same once aggregate/sret support lands in M7.  Until then this
    test is expected to fail on the native path with "only integer-family or void
    return supported". }
  SrcRecordReturnFunction = '''
    program Prg;
    type TPoint = record X: Integer; Y: Integer; end;
    function MakePoint(X, Y: Integer): TPoint;
    begin
      Result.X := X;
      Result.Y := Y
    end;
    var Pt: TPoint;
    begin
      Pt := MakePoint(3, 7);
      WriteLn(Pt.X);
      WriteLn(Pt.Y)
    end.
    ''';

  SrcSizeOfRecord = '''
    program Prg;
    type
      TPoint = record
        X: Integer;
        Y: Integer;
      end;
    begin
      WriteLn(SizeOf(TPoint))
    end.
    ''';

  SrcSizeOfGenericRecord = '''
    program Prg;
    type
      TPair<T1, T2> = record
        First: T1;
        Second: T2;
      end;
    var
      A: TPair<Integer, Integer>;
      B: TPair<Integer, Int64>;
    begin
      WriteLn(SizeOf(A));
      WriteLn(SizeOf(B))
    end.
    ''';

  SrcNestedRecordFieldAssign = '''
    program Prg;
    type
      TDate = record
        Year: Integer;
        Month: Integer;
        Day: Integer;
        function Sum: Integer;
      end;
      TDateTime = record
        Date: TDate;
        Hour: Integer;
      end;
    function TDate.Sum: Integer;
    begin
      Result := Self.Year + Self.Month + Self.Day
    end;
    var
      DT: TDateTime;
      D: TDate;
    begin
      DT.Date.Year := 2026;
      DT.Date.Month := 6;
      DT.Date.Day := 5;
      DT.Hour := 14;
      D := DT.Date;
      WriteLn(D.Sum());
      WriteLn(DT.Date.Sum())
    end.
    ''';

  { M6 — float source programs }

  SrcDoubleGlobal = '''
    program Prg;
    var D: Double;
    begin
      D := 3.14;
      WriteLn(D)
    end.
    ''';

  SrcDoubleLocal = '''
    program Prg;
    procedure ShowDouble;
    var D: Double;
    begin
      D := 2.5;
      WriteLn(D)
    end;
    begin
      ShowDouble()
    end.
    ''';

  SrcDoubleArith = '''
    program Prg;
    var A, B: Double;
    begin
      A := 10.0;
      B := 3.0;
      WriteLn(A + B);
      WriteLn(A - B);
      WriteLn(A * B);
      WriteLn(A / B)
    end.
    ''';

  SrcDoubleCompare = '''
    program Prg;
    var A, B: Double;
    begin
      A := 1.5;
      B := 2.5;
      if A < B then
        WriteLn(1)
      else
        WriteLn(0);
      if A = B then
        WriteLn(1)
      else
        WriteLn(0)
    end.
    ''';

  SrcDoubleWriteLn = '''
    program Prg;
    var D: Double;
    begin
      D := 1.5;
      WriteLn(D);
      WriteLn(D + 1.0)
    end.
    ''';

  SrcSingleGlobal = '''
    program Prg;
    var S: Single;
    begin
      S := 1.5;
      WriteLn(S)
    end.
    ''';

  SrcDoubleFuncParam = '''
    program Prg;
    function Scale(V: Double; Factor: Double): Double;
    begin
      Result := V * Factor
    end;
    begin
      WriteLn(Scale(3.0, 2.0))
    end.
    ''';

  SrcDoubleFuncReturn = '''
    program Prg;
    function Half(V: Double): Double;
    begin
      Result := V / 2.0
    end;
    var D: Double;
    begin
      D := Half(7.0);
      WriteLn(D)
    end.
    ''';

  { Issue #107: a float comparison nested inside a short-circuit and/or
    reaches EmitExprToEax (not EmitCondBranch), whose integer path could
    not lower the TFloatLiteral operand — "unsupported expression form
    TFloatLiteral".  Exercise both `or` and `and`, both branches. }
  SrcFloatCompareInOrAnd = '''
    program Prg;
    procedure Check(P: Double);
    begin
      if (P > 1.0) or (P < -1.0) then WriteLn('out') else WriteLn('in')
    end;
    procedure Both(P: Double);
    begin
      if (P > 0.0) and (P < 10.0) then WriteLn('mid') else WriteLn('off')
    end;
    begin
      Check(2.0);
      Check(0.5);
      Check(-3.0);
      Both(5.0);
      Both(20.0)
    end.
    ''';

  { Issue #107: a local float `const` was emitted as a reference to an
    undefined symbol on the native backend — "undefined reference to
    precalc".  Inline its value instead. }
  SrcLocalFloatConst = '''
    program Prg;
    function Circ(R: Double): Double;
    const
      TwoPi = 6.28318530718;
    begin
      Result := R * TwoPi
    end;
    begin
      WriteLn(Circ(2.0))
    end.
    ''';

{ Every test below runs its source through BOTH backends (beQBE, beNative)
  and asserts identical stdout/exit on each — the native backend's whole
  correctness model is parity with QBE on the same source, so this exercises
  both code generators against one hand-written expected value.  As native
  gains features, more suites can adopt AssertRunsOnAll; until then this
  suite covers the integer-family subset native supports. }

const
  SrcSretVarParamArg = '''
    program Prg;
    type
      TBig = record
        A, B, C, D: Int64;
        S: string;
      end;
    function MakeBig(const AStr: string; APos: Integer;
      var AEnd: Integer): TBig;
    begin
      Result.A := APos;
      Result.S := AStr;
      AEnd := APos + 5;
    end;
    var
      R: TBig;
      E: Integer;
    begin
      E := 0;
      R := MakeBig('hi', 10, E);
      WriteLn(R.A);
      WriteLn(R.S);
      WriteLn(E);
    end.
    ''';

  SrcSretNestedRecFieldAssign = '''
    program Prg;
    type
      TOp = record
        K: Integer;
        Imm: Int64;
        S: string;
        A, B: Int64;
      end;
      TLine = record
        Kind: Integer;
        Op1: TOp;
        Op2: TOp;
        N: Integer;
      end;
    function PO(V: Integer): TOp;
    begin
      Result.K := V;
      Result.Imm := V * 10;
      Result.S := 'x';
    end;
    function PL: TLine;
    var
      T: TOp;
    begin
      Result.Kind := 1;
      T := PO(5);
      Result.Op1 := T;
      T := PO(7);
      Result.Op2 := T;
      Result.N := 9;
    end;
    var
      L: TLine;
    begin
      L := PL();
      WriteLn(L.Kind);
      WriteLn(L.Op1.K);
      WriteLn(L.Op2.K);
      WriteLn(L.Op2.Imm);
      WriteLn(L.Op1.S);
      WriteLn(L.N);
    end.
    ''';

  { Implicit-Self method calls whose register slots (Self + args) exceed the
    six System V integer registers must spill the overflow to the stack — the
    implicit-Self expression path previously aborted codegen.  Covers a
    non-virtual call (Self + 8 args = 9 slots, 3 spilled) and a virtual/vtable
    call (Self + 7 args = 8 slots, 2 spilled); the values verify that every
    arg, including the spilled ones, arrives intact. }
  SrcImplicitSelfArgOverflow = '''
    program Prg;
    type
      TWorker = class
        function Sum8(a, b, c, d, e, f, g, h: Integer): Integer;
        function VSum7(a, b, c, d, e, f, g: Integer): Integer; virtual;
        function Drive(): string;
      end;
    function TWorker.Sum8(a, b, c, d, e, f, g, h: Integer): Integer;
    begin
      Result := a + b + c + d + e + f + g + h;
    end;
    function TWorker.VSum7(a, b, c, d, e, f, g: Integer): Integer;
    begin
      Result := a * 1 + b * 2 + c * 3 + d * 4 + e * 5 + f * 6 + g * 7;
    end;
    function TWorker.Drive(): string;
    begin
      WriteLn(Sum8(1, 2, 3, 4, 5, 6, 7, 8));
      WriteLn(VSum7(1, 1, 1, 1, 1, 1, 1));
      Result := 'ok';
    end;
    var
      W: TWorker;
    begin
      W := TWorker.Create();
      WriteLn(W.Drive());
      W.Free();
    end.
    ''';

const
  SrcStringFieldCharRead = '''
    program Prg;
    type
      TRec = record
        S: string;
      end;
      TBox = class
      public
        Data: string;
        function At(I: Integer): Integer;
      end;
    function TBox.At(I: Integer): Integer;
    begin
      Result := Data[I];
    end;
    var
      R: TRec;
      B: TBox;
      I: Integer;
    begin
      R.S := 'record';
      B := TBox.Create;
      B.Data := 'ABCDEF';
      I := 2;
      WriteLn(R.S[0]);
      WriteLn(B.Data[4]);
      WriteLn(B.Data[I + 2]);
      WriteLn(B.At(1));
      B.Free();
    end.
    ''';

procedure TE2ENativeTests.TestRun_Native_StringFieldCharRead;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcStringFieldCharRead,
    IntToStr(Ord('r')) + LE + IntToStr(Ord('E')) + LE
    + IntToStr(Ord('E')) + LE + IntToStr(Ord('B')) + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_SretCall_VarParamArg;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcSretVarParamArg,
    '10' + LE + 'hi' + LE + '15' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_SretResult_NestedRecordFieldAssign;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcSretNestedRecFieldAssign,
    '1' + LE + '5' + LE + '7' + LE + '70' + LE + 'x' + LE + '9' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ImplicitSelfCall_RegisterOverflow;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcImplicitSelfArgOverflow,
    '36' + LE + '28' + LE + 'ok' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_EmptyProgram_ExitsZero;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcEmpty, '', 0);
end;

procedure TE2ENativeTests.TestRun_Native_IntArithmetic_WriteLn;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcArith, '14' + LE + '42' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_DivModAndNesting;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDivMod,
    '3' + LE + '2' + LE + '30' + LE + '-3' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_WriteNoNewline;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcWriteNoNL, '123' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IfElse;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcIfElse, '1' + LE + '0' + LE + '44' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ComparisonsAndNestedIf;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcComparisons,
    '11' + LE + '22' + LE + '44' + LE + '55' + LE + '66' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Repeat;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcRepeat, '8' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_VarsAndForLoop;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcVarsForLoop, '15' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_DownToAndNestedFor;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDownToNested, '543210' + LE + '9' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_CounterLoops;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { while writes 0,1,2 (Write, no newline), then WriteLn(9) -> "0129"; repeat
    counts 0->2->4->6 and WriteLn(n) -> "6". }
  AssertRunsOnAll(SrcCounterLoops, '0129' + LE + '6' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ForEndEvaluatedOnce;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcForEndOnce, '3' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_FunctionsAndCalls;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Square(6)=36; Sum3(1,2,3)=6; PrintTwice(9)=9,9; Square(Square(2))=16;
    Square(3)+Sum3(10,20,30)=9+60=69 }
  AssertRunsOnAll(SrcFunctions,
    '36' + LE + '6' + LE + '9' + LE + '9' + LE + '16' + LE + '69' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Recursion;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcRecursion, '120' + LE + '1' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_PromotedWidthMix;
const
  Src = '''
      program P;
      function Mix(B: Byte): Int64;
      var
        W: SmallInt;
      begin
        B := B + 200;      { wraps in byte width: 100+200 = 44 }
        W := -3;
        W := W * 100;      { -300 }
        Result := B;
        Result := Result * 1000 + W;   { 44*1000 - 300 = 43700 }
      end;
      begin
        WriteLn(Mix(100))
      end.
      ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  Self.AssertRunsOnAll(Src, '43700' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_RaiseThroughPromotedFrame;
const
  { H is promoted (K hot, in %r14).  H calls F, which owns a try/except
    (so F itself is NOT promoted, and its setjmp records %r14/%r15).  F
    calls G — promoted, clobbers its own %r14/%r15 — and G raises.  The
    longjmp lands in F's handler with the setjmp-saved registers; when F
    returns, H's K must still hold its pre-call value.  A local Exception
    class keeps the program stdlib-free (same pattern as the fiber e2e). }
  Src = '''
      program P;
      type
        Exception = class
          FMessage: string;
          constructor Create(AMsg: string);
          property Message: string read FMessage;
        end;
      constructor Exception.Create(AMsg: string);
      begin
        FMessage := AMsg
      end;
      function G(N: Integer): Integer;
      begin
        Result := N * 2;
        if N > 0 then
          raise Exception.Create('boom');
      end;
      function F(N: Integer): Integer;
      begin
        Result := 0;
        try
          Result := G(N)
        except
          on E: Exception do
            Result := 7
        end
      end;
      function H(N: Integer): Integer;
      var K: Integer;
      begin
        K := N + 40;       { K promoted; must survive the unwind below }
        Result := F(N);
        Result := Result * 1000 + K
      end;
      begin
        WriteLn(H(1))
      end.
      ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { F catches (7), K survives as 41: 7*1000 + 41. }
  Self.AssertRunsOnAll(Src, '7041' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_CatcherPreservesR15Local;
const
  { In H: N (param) takes %r14, A (local) takes %r15 — H is a procedure,
    so there is no Result competing for the second register.  F contains
    try/except whose exception path RUNS (G raises); F must restore %r15
    before returning or A is replaced by the exception pointer. }
  Src = '''
      program P;
      type
        Exception = class
          FMessage: string;
          constructor Create(AMsg: string);
          property Message: string read FMessage;
        end;
      constructor Exception.Create(AMsg: string);
      begin
        FMessage := AMsg
      end;
      function G(N: Integer): Integer;
      begin
        Result := N;
        if N > 0 then
          raise Exception.Create('boom');
      end;
      function F(N: Integer): Integer;
      begin
        Result := 0;
        try
          Result := G(N)
        except
          on E: Exception do
            Result := 5
        end
      end;
      procedure H(N: Integer);
      var A: Integer;
      begin
        A := N * 11;       { A promoted into %r15 }
        WriteLn(F(N));     { F's except path runs — must preserve %r15 }
        WriteLn(A)
      end;
      begin
        H(3)
      end.
      ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  Self.AssertRunsOnAll(Src, '5' + LE + '33' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_NestedProcMethodOnCapturedLocal;
const
  Src = '''
      program P;
      type
        TBox = class
        public
          FCount: Integer;
          procedure Bump;
        end;
      procedure TBox.Bump;
      begin
        FCount := FCount + 1
      end;
      procedure Run;
      var Box: TBox;
        procedure Consider;
        begin
          Box.Bump()
        end;
      begin
        Box := TBox.Create();
        Consider();
        Consider();
        WriteLn(Box.FCount);
        Box.Free()
      end;
      begin
        Run()
      end.
      ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  Self.AssertRunsOnAll(Src, '2' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_InlineLeafShapes;
const
  Src = '''
      program P;
      var GBase: Integer;
      function Clamp(V, Lo, Hi: Integer): Integer;
      begin
        if V < Lo then Exit(Lo);
        if V > Hi then Exit(Hi);
        Result := V
      end;
      function AddBase(N: Integer): Integer;
      begin
        Result := N + GBase
      end;
      function MixExpr(A, B: Integer): Integer;
      begin
        Result := Clamp(A + B, 0, 100) + Clamp(A - B, -10, 10)
      end;
      function Nested(A: Integer): Integer;
      begin
        Result := Clamp(Clamp(A, 0, 50), 10, 40)
      end;
      function Shadow(V: Integer): Integer;
      var Lo: Integer;
      begin
        Lo := 7;
        Result := Clamp(V, 1, 5) + Lo
      end;
      begin
        GBase := 1000;
        WriteLn(MixExpr(60, 55));
        WriteLn(Nested(75));
        WriteLn(Nested(5));
        WriteLn(Shadow(9));
        WriteLn(AddBase(23))
      end.
      ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { MixExpr: clamp(115)=100 + clamp(5)=5 = 105.  Nested(75): inner 50,
    outer 40.  Nested(5): inner 5, outer 10.  Shadow: clamp(9,1,5)=5 + 7
    = 12.  AddBase reads a program global from the inlined body: 1023. }
  Self.AssertRunsOnAll(Src,
    '105' + LE + '40' + LE + '10' + LE + '12' + LE + '1023' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ForLoopOverLocal;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcForOverLocal, '55' + LE + '5050' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_WiderIntGlobals;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcWiderIntGlobals,
    '200' + LE + '50000' + LE + '-1000' + LE + '5000000000' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Int64Arithmetic;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { 100000*100000 = 10000000000; 4e9+4e9 = 8000000000; /1e6 = 8000 }
  AssertRunsOnAll(SrcInt64Arith,
    '10000000000' + LE + '8000000000' + LE + '8000' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_WiderIntParamsAndReturn;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { AddBytes(200,100)=300; ScaleBig(2e9)*3=6000000000; ClampWord(40000)=40000 }
  AssertRunsOnAll(SrcWiderIntParams,
    '300' + LE + '6000000000' + LE + '40000' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_TypeCastConversions;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Byte(300)=44 (300 mod 256); Word(70000)=4464 (70000 mod 65536);
    Int64(1000000)^2 = 1000000000000 }
  AssertRunsOnAll(SrcTypeCasts,
    '44' + LE + '4464' + LE + '1000000000000' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_SignednessAndWraparound;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { SmallInt -2 reads back -2; Word 65534 reads back 65534; -2 + 5 = 3 }
  AssertRunsOnAll(SrcSignedness, '-2' + LE + '65534' + LE + '3' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_WriteUnsigned32;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcWriteUnsigned32, '3000000000' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_VarParamSwap;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcVarParamSwap, '7' + LE + '3' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_VarParamPassThrough;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcVarParamPassThrough, '25' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_VarParamWiderInt;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcVarParamWiderInt,
    '9000000000' + LE + '255' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_OutParam;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcOutParam, '42' + LE + '99' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ForBreak;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcForBreak, '5' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_WhileContinue;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Sum of odd numbers 1..9: 1+3+5+7+9 = 25 }
  AssertRunsOnAll(SrcWhileContinue, '25' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ExitFromFunction;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcExitFunc, '7' + LE + '9' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ExitValueShorthand;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Clamp(5,1,10)=5; Clamp(-3,1,10)=1; Clamp(99,1,10)=10 }
  AssertRunsOnAll(SrcExitValue, '5' + LE + '1' + LE + '10' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_SevenArgs;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { 1+2+3+4+5+6+7 = 28 }
  AssertRunsOnAll(SrcSevenArgs, '28' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_EightArgs;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { 1+2+3+4+5+6+7+8 = 36; 100-1-2-3-4-5-6-7 = 72 }
  AssertRunsOnAll(SrcEightArgs, '36' + LE + '72' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_TenArgs;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { 1+2+3+4+5+6+7+8+9+10 = 55 }
  AssertRunsOnAll(SrcTenArgs, '55' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_OverflowFloatArgs;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcOverflowFloatArgs, '1 2 3 4 5 6.5 7.5 8 9' + LE, 0);
end;

const
  { Implicit-Self method call (unqualified Sink(...) inside a method) with 6
    args: Self + 6 = 7 register slots, one past the 6 SysV integer registers. }
  SrcImplicitSelf6 = '''
    program Prog;
    type
      TC = class
        FSum: Integer;
        procedure Sink(a, b, c, d, e, f: Integer);
        procedure Caller;
      end;
    procedure TC.Sink(a, b, c, d, e, f: Integer);
    begin FSum := a + b + c + d + e + f end;
    procedure TC.Caller;
    begin Sink(1, 2, 3, 4, 5, 6) end;
    var t: TC;
    begin t := TC.Create; t.Caller(); WriteLn(t.FSum); t := nil end.
    ''';

  SrcImplicitSelf7 = '''
    program Prog;
    type
      TC = class
        FSum: Integer;
        procedure Sink(a, b, c, d, e, f, g: Integer);
        procedure Caller;
      end;
    procedure TC.Sink(a, b, c, d, e, f, g: Integer);
    begin FSum := a + b + c + d + e + f + g end;
    procedure TC.Caller;
    begin Sink(1, 2, 3, 4, 5, 6, 7) end;
    var t: TC;
    begin t := TC.Create; t.Caller(); WriteLn(t.FSum); t := nil end.
    ''';

procedure TE2ENativeTests.TestRun_Native_ImplicitSelfMethod_SixArgs;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcImplicitSelf6, '21' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ImplicitSelfMethod_SevenArgs;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcImplicitSelf7, '28' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IndirectCall_BareProc;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcIndirectBareProc, '42' + LE + '99' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IndirectCall_BareFunc;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { F = Add: 3+4 = 7; F = Mul: 3*4 = 12 }
  AssertRunsOnAll(SrcIndirectBareFunc, '7' + LE + '12' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Record_GlobalReadWrite;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcRecordGlobal, '3' + LE + '7' + LE + '10' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Record_LocalReadWrite;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcRecordLocal, '20' + LE + '42' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Record_AsParam;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { |4-1| + |6-2| = 3 + 4 = 7 }
  AssertRunsOnAll(SrcRecordParam, '7' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_StaticArray_GlobalReadWrite;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcStaticArrayGlobal, '10' + LE + '30' + LE + '50' + LE + '90' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_StaticArray_LocalReadWrite;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcStaticArrayLocal, '6' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_StaticArray_NonZeroLow;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { 100 + 200 + 300 = 600 }
  AssertRunsOnAll(SrcStaticArrayNonZeroLow, '600' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IndirectCall_MethodPtr;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcIndirectMethodPtr, '15' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_MethodAddress_VarString;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcMethodAddrVarString, '42' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_RecordReturnFunction;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcRecordReturnFunction, '3' + LE + '7' + LE, 0);
end;

{ ------------------------------------------------------------------ }
{ M6 — float parity                                                    }
{ ------------------------------------------------------------------ }

procedure TE2ENativeTests.TestRun_Native_Double_GlobalReadWrite;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDoubleGlobal, '3.14' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Double_LocalReadWrite;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDoubleLocal, '2.5' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Double_Arithmetic;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDoubleArith, '13' + LE + '7' + LE + '30' + LE + '3.33333333333333' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Double_Comparison;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDoubleCompare, '1' + LE + '0' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Double_WriteLn;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDoubleWriteLn, '1.5' + LE + '2.5' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Single_GlobalReadWrite;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcSingleGlobal, '1.5' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Double_FuncParam;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Scale(3.0, 2.0) = 6.0 }
  AssertRunsOnAll(SrcDoubleFuncParam, '6' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Double_FuncReturn;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Half(7.0) = 3.5 }
  AssertRunsOnAll(SrcDoubleFuncReturn, '3.5' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_FloatCompareInOrAnd;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcFloatCompareInOrAnd,
    'out' + LE + 'in' + LE + 'out' + LE + 'mid' + LE + 'off' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_LocalFloatConst;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Circ(2.0) = 2.0 * 6.28318530718 = 12.56637061436 }
  AssertRunsOnAll(SrcLocalFloatConst, '12.56637061436' + LE, 0);
end;

{ ------------------------------------------------------------------ }
{ M7c — string operations                                              }
{ ------------------------------------------------------------------ }

const
  SrcStrWriteLnLiteral = '''
    program Prg;
    begin
      WriteLn('hello')
    end.
    ''';

  SrcStrAssignAndWrite = '''
    program Prg;
    var S: string;
    begin
      S := 'world';
      WriteLn(S)
    end.
    ''';

  SrcStrConcat = '''
    program Prg;
    var A, B, C: string;
    begin
      A := 'foo';
      B := 'bar';
      C := A + B;
      WriteLn(C)
    end.
    ''';

  { Chr(N) returns a one-character heap String.  Assigning and concatenating it
    must lower to _Chr (string pointer), not treat N as the pointer itself (the
    latter crashed: a raw integer fed into _StringAddRef). }
  SrcChrConcat = '''
    program Prg;
    var
      S: string;
      I: Integer;
    begin
      S := 'A' + Chr(66) + 'C';
      WriteLn(S);
      S := '';
      I := 65;
      while I < 70 do
      begin
        S := S + Chr(I);
        I := I + 1
      end;
      WriteLn(S)
    end.
    ''';

  SrcStrLength = '''
    program Prg;
    var S: string;
    begin
      S := 'hello';
      WriteLn(Length(S))
    end.
    ''';

  SrcStrPos = '''
    program Prg;
    var S, Sub: string;
    begin
      S   := 'hello world';
      Sub := 'world';
      WriteLn(Pos(Sub, S))
    end.
    ''';

  SrcStrCopy = '''
    program Prg;
    var S, T: string;
    begin
      S := 'hello';
      T := Copy(S, 1, 3);
      WriteLn(T)
    end.
    ''';

  SrcStrUpperCase = '''
    program Prg;
    var S: string;
    begin
      S := 'hello';
      WriteLn(UpperCase(S))
    end.
    ''';

  SrcStrIntToStr = '''
    program Prg;
    var S: string;
    begin
      S := IntToStr(42);
      WriteLn(S)
    end.
    ''';

  SrcStrStrToInt = '''
    program Prg;
    var N: Integer;
    begin
      N := StrToInt('123');
      WriteLn(N)
    end.
    ''';

  SrcStrParam = '''
    program Prg;
    function Greet(Name: string): string;
    begin
      Result := 'Hello ' + Name
    end;
    begin
      WriteLn(Greet('World'))
    end.
    ''';

  SrcStrFuncReturn = '''
    program Prg;
    function Twice(S: string): string;
    begin
      Result := S + S
    end;
    begin
      WriteLn(Twice('ab'))
    end.
    ''';

  SrcStrDelete = '''
    program Prg;
    var S: string;
    begin
      S := 'Hello World';
      Delete(S, 5, 6);
      WriteLn(S)
    end.
    ''';

  SrcStrSetLength = '''
    program Prg;
    var S: string;
    begin
      S := 'Hello';
      SetLength(S, 3);
      WriteLn(S)
    end.
    ''';

  SrcStrSubscript = '''
    program Prg;
    var S: string;
    begin
      S := 'ABC';
      WriteLn(S[0]);
      WriteLn(S[1]);
      WriteLn(S[2])
    end.
    ''';

procedure TE2ENativeTests.TestRun_Native_String_WriteLnLiteral;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcStrWriteLnLiteral, 'hello' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_String_AssignAndWrite;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcStrAssignAndWrite, 'world' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_String_Concat;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcStrConcat, 'foobar' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_String_Length;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcStrLength, '5' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_String_Pos;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Pos is 0-based in Blaise: 'world' starts at index 6 }
  AssertRunsOnAll(SrcStrPos, '6' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_String_Copy;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Copy('hello', 1, 3) = 'ell' }
  AssertRunsOnAll(SrcStrCopy, 'ell' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_String_UpperCase;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcStrUpperCase, 'HELLO' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_String_IntToStr;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcStrIntToStr, '42' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_String_StrToInt;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcStrStrToInt, '123' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_String_Param;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcStrParam, 'Hello World' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_String_FuncReturn;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcStrFuncReturn, 'abab' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_String_Delete;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcStrDelete, 'Hello' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_String_SetLength;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcStrSetLength, 'Hel' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_String_Subscript;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { S[0]='A'=65, S[1]='B'=66, S[2]='C'=67 }
  AssertRunsOnAll(SrcStrSubscript,
    '65' + LE + '66' + LE + '67' + LE, 0);
end;

const
  SrcStrSameText = '''
    program Prg;
    var S, T: string;
    begin
      S := 'Hello';
      T := 'hello';
      WriteLn(SameText(S, T))
    end.
    ''';

  SrcFormatIntArg = '''
    program Prg;
    var S: string;
    begin
      S := Format('val=%d', 42);
      WriteLn(S)
    end.
    ''';

  SrcFormatStrArg = '''
    program Prg;
    var S: string;
    begin
      S := Format('hello %s', 'world');
      WriteLn(S)
    end.
    ''';

  SrcFormatMixedArgs = '''
    program Prg;
    var S: string;
    begin
      S := Format('%s=%d', 'Alice', 30);
      WriteLn(S)
    end.
    ''';

  SrcFormatFuncCallArg = '''
    program Prg;
    function GetName: string;
    begin
      Result := 'Bob'
    end;
    function GetAge: Integer;
    begin
      Result := 25
    end;
    begin
      WriteLn(Format('%s is %d', GetName(), GetAge()))
    end.
    ''';

  SrcConcatWithInt = '''
    program Prg;
    begin
      WriteLn('x=' + IntToStr(7))
    end.
    ''';

procedure TE2ENativeTests.TestRun_Native_String_SameText;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcStrSameText, 'True' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_String_Format_IntArg;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcFormatIntArg, 'val=42' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_String_Format_StrArg;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcFormatStrArg, 'hello world' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_String_Format_MixedArgs;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcFormatMixedArgs, 'Alice=30' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_String_Format_FuncCallArg;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcFormatFuncCallArg, 'Bob is 25' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_String_ConcatWithInt;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcConcatWithInt, 'x=7' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_String_ChrConcat;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcChrConcat, 'ABC' + LE + 'ABCDE' + LE, 0);
end;

const
  SrcLocalDynDirty =
    '''
    program Prg;
    procedure Dirty();
    var
      A: array[0..63] of Int64;
      I: Integer;
    begin
      for I := 0 to 63 do
        A[I] := -81985529216486896;
    end;
    procedure UseLocalDyn();
    var
      Arr: array of Integer;
    begin
      SetLength(Arr, 5);
      Arr[2] := 42;
      writeln(Arr[2]);
    end;
    begin
      Dirty();
      UseLocalDyn();
      writeln('done');
    end.
    ''';

procedure TE2ENativeTests.TestRun_Native_LocalDynArray_DirtyStack;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcLocalDynDirty, '42' + LE + 'done' + LE, 0);
end;

{ M7d — exception handling source programs }
const
  SrcExcBase =
    '''
        program Prg;
        type
          Exception = class
            FMessage: string;
            property Message: string read FMessage;
          end;
          EFoo = class(Exception) end;
          EBar = class(EFoo) end;
    ''';

  SrcTryFinallyNormal = '''
    program Prg;
    begin
      try
        WriteLn('in_try')
      finally
        WriteLn('in_finally')
      end
    end.
    ''';

  SrcTryFinallyNested = '''
    program Prg;
    begin
      try
        try
          WriteLn('inner_try')
        finally
          WriteLn('inner_fin')
        end
      finally
        WriteLn('outer_fin')
      end
    end.
    ''';

  SrcExitThroughFinally = '''
    program Prg;
    procedure Run;
    begin
      try
        WriteLn('in_try');
        Exit;
        WriteLn('unreached')
      finally
        WriteLn('in_finally')
      end
    end;
    begin
      Run();
      WriteLn('after')
    end.
    ''';

  SrcBreakThroughFinally = '''
    program Prg;
    var I: Integer;
    begin
      for I := 0 to 3 do
      begin
        try
          if I = 2 then Break;
          WriteLn('iter')
        finally
          WriteLn('fin')
        end
      end;
      WriteLn('done')
    end.
    ''';

  SrcTryExceptBare = '''
    program Prg;
    var X: Integer;
    begin
      X := 0;
      try
        X := 1
      except
        X := 99
      end;
      WriteLn(X)
    end.
    ''';

  SrcTypedExcept =
    SrcExcBase +
    '''
        var X: Integer;
        begin
          X := 0;
          try
            raise EFoo.Create()
          except
            on E: EFoo do X := 42;
            on E: Exception do X := 1
          end;
          WriteLn(X)
        end.
    ''';

  SrcSubclassMatch =
    SrcExcBase +
    '''
        var X: Integer;
        begin
          X := 0;
          try
            raise EBar.Create()
          except
            on E: EFoo do X := 7
          end;
          WriteLn(X)
        end.
    ''';

  SrcBareRaisePropagate =
    SrcExcBase +
    '''
        var X: Integer;
        begin
          X := 0;
          try
            try
              raise EFoo.Create()
            except
              on E: EFoo do begin X := 1; raise end
            end
          except
            on E: EFoo do X := 2
          end;
          WriteLn(X)
        end.
    ''';

  SrcElseBody =
    SrcExcBase +
    '''
        var X: Integer;
        begin
          X := 0;
          try
            raise EFoo.Create()
          except
            on E: EBar do X := 9
            else X := 5
          end;
          WriteLn(X)
        end.
    ''';

  SrcExitNestedFinally = '''
    program Prg;
    procedure Run;
    begin
      try
        try
          Exit
        finally
          WriteLn('inner_fin')
        end
      finally
        WriteLn('outer_fin')
      end
    end;
    begin
      Run();
      WriteLn('after')
    end.
    ''';

procedure TE2ENativeTests.TestRun_Native_TryFinally_Normal;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcTryFinallyNormal, 'in_try' + LE + 'in_finally' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_TryFinally_NestedNormal;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcTryFinallyNested,
    'inner_try' + LE + 'inner_fin' + LE + 'outer_fin' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_TryFinally_ExitUnwind;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcExitThroughFinally,
    'in_try' + LE + 'in_finally' + LE + 'after' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_TryFinally_BreakUnwind;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcBreakThroughFinally,
    'iter' + LE + 'fin' + LE +
    'iter' + LE + 'fin' + LE +
    'fin' + LE + 'done' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_TryExcept_Bare;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcTryExceptBare, '1' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_TryExcept_TypedHandler;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcTypedExcept, '42' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_TryExcept_SubclassMatch;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcSubclassMatch, '7' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_TryExcept_BareRaisePropagate;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcBareRaisePropagate, '2' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_TryExcept_ElseBody;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcElseBody, '5' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ExitThroughNestedFinally;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcExitNestedFinally,
    'inner_fin' + LE + 'outer_fin' + LE + 'after' + LE, 0);
end;

{ M7e — open arrays and dynamic arrays }

const
  SrcOASum =
    '''
    program Prg;
    function Sum(const A: array of Integer): Integer;
    var I: Integer;
    begin
      Result := 0;
      for I := 0 to High(A) do
        Result := Result + A[I]
    end;
    begin
      WriteLn(Sum([1, 2, 3, 4, 5]))
    end.
    ''';

  SrcOAHighLow =
    '''
    program Prg;
    procedure PrintBounds(const A: array of Integer);
    begin
      WriteLn(Low(A));
      WriteLn(High(A))
    end;
    begin
      PrintBounds([10, 20, 30])
    end.
    ''';

  SrcOALength =
    '''
    program Prg;
    function Count(const A: array of Integer): Integer;
    begin
      Result := Length(A)
    end;
    begin
      WriteLn(Count([10, 20, 30]))
    end.
    ''';

  SrcStaticToOpenLen =
    '''
    program Prg;
    procedure PrintLen(const A: array of Integer);
    begin
      WriteLn(Length(A))
    end;
    var B: array[0..4] of Integer;
    begin
      PrintLen(B)
    end.
    ''';

  SrcStaticToOpenSum =
    '''
    program Prg;
    function Sum(const A: array of Integer): Integer;
    var I: Integer;
    begin
      Result := 0;
      for I := 0 to High(A) do
        Result := Result + A[I]
    end;
    var B: array[0..2] of Integer;
    begin
      B[0] := 10;
      B[1] := 20;
      B[2] := 30;
      WriteLn(Sum(B))
    end.
    ''';

  SrcStaticToOpenNested =
    '''
    program Prg;
    function Sum(const A: array of Integer): Integer;
    var I: Integer;
    begin
      Result := 0;
      for I := 0 to High(A) do
        Result := Result + A[I]
    end;
    procedure Process(const A: array of Integer);
    begin
      WriteLn(Sum(A))
    end;
    var B: array[0..2] of Integer;
    begin
      B[0] := 5;
      B[1] := 10;
      B[2] := 15;
      Process(B)
    end.
    ''';

  SrcDynArrayBasic =
    '''
    program Prg;
    var A: array of Integer;
        I: Integer;
    begin
      SetLength(A, 3);
      A[0] := 10;
      A[1] := 20;
      A[2] := 30;
      for I := 0 to High(A) do
        WriteLn(A[I])
    end.
    ''';

  SrcDynArrayLenHigh =
    '''
    program Prg;
    var A: array of Integer;
    begin
      SetLength(A, 5);
      WriteLn(Length(A));
      WriteLn(High(A))
    end.
    ''';

  { M7f — interface dispatch.  Each program assigns a class instance to an
    interface variable (class->interface, via the static itab) and dispatches a
    method through the fat pointer; the native backend must match the QBE
    oracle. }
  SrcIntfZeroArg =
    '''
    program Prg;
    type
      IGreeter = interface
        function Greet: Integer;
      end;
      TGreeter = class(TObject, IGreeter)
        function Greet: Integer;
      end;
    function TGreeter.Greet: Integer;
    begin Result := 42 end;
    var
      G: IGreeter;
      T: TGreeter;
    begin
      T := TGreeter.Create();
      G := T;
      WriteLn(G.Greet())
    end.
    ''';

  SrcIntfArg =
    '''
    program Prg;
    type
      IShape = interface
        function Area(Scale: Integer): Integer;
      end;
      TBox = class(TObject, IShape)
        function Area(Scale: Integer): Integer;
      end;
    function TBox.Area(Scale: Integer): Integer;
    begin Result := 10 * Scale end;
    var
      S: IShape;
      B: TBox;
    begin
      B := TBox.Create();
      S := B;
      WriteLn(S.Area(3))
    end.
    ''';

  SrcIntfProc =
    '''
    program Prg;
    type
      IShape = interface
        procedure Describe;
      end;
      TBox = class(TObject, IShape)
        procedure Describe;
      end;
    procedure TBox.Describe;
    begin WriteLn('box') end;
    var
      S: IShape;
      B: TBox;
    begin
      B := TBox.Create();
      S := B;
      S.Describe()
    end.
    ''';

  SrcIntfCopy =
    '''
    program Prg;
    type
      IShape = interface
        function Area: Integer;
      end;
      TBox = class(TObject, IShape)
        function Area: Integer;
      end;
    function TBox.Area: Integer;
    begin Result := 21 end;
    var
      S, S2: IShape;
      B: TBox;
    begin
      B := TBox.Create();
      S := B;
      S2 := S;
      WriteLn(S2.Area)
    end.
    ''';

  SrcIntfAsCast =
    '''
    program Prg;
    type
      IShape = interface
        function Area: Integer;
      end;
      IColor = interface
        function Code: Integer;
      end;
      TBox = class(TObject, IShape, IColor)
        function Area: Integer;
        function Code: Integer;
      end;
    function TBox.Area: Integer;
    begin Result := 7 end;
    function TBox.Code: Integer;
    begin Result := 99 end;
    var
      S: IShape;
      C: IColor;
      B: TBox;
    begin
      B := TBox.Create();
      S := B;
      C := B as IColor;
      WriteLn(S.Area());
      WriteLn(C.Code())
    end.
    ''';

  SrcIntfNilClear =
    '''
    program Prg;
    type
      IGreeter = interface
        function Greet: Integer;
      end;
      TGreeter = class(TObject, IGreeter)
        function Greet: Integer;
      end;
    function TGreeter.Greet: Integer;
    begin Result := 5 end;
    var
      G: IGreeter;
      T: TGreeter;
    begin
      T := TGreeter.Create();
      G := T;
      WriteLn(G.Greet());
      G := nil;
      WriteLn(13)
    end.
    ''';

  { Regression (issue #64): interface-typed field 'im' in a class with a
    same-named global of a different type. }
  SrcNativeIntfFieldShadowsGlobal = '''
    program Prg;
    type
      Iprinter = interface
        procedure print;
      end;
      Toutput = class(TObject, Iprinter)
        procedure print;
      end;
      Tmi = class
        im: Iprinter;
        constructor create(am: Iprinter);
        procedure use;
      end;
    procedure Toutput.print;
    begin
      WriteLn('printed');
    end;
    constructor Tmi.Create(am: Iprinter);
    begin
      im := am;
    end;
    procedure Tmi.use;
    begin
      im.print();
    end;
    var
      im: Tmi;
    begin
      im := Tmi.Create(Toutput.Create());
      im.use();
    end.
    ''';

  { Interface params: passing interface fat pointers to procedures, methods,
    constructors, and inherited calls.  Each program passes an interface value
    as an argument and verifies correct dispatch through the received fat pointer. }

  { 1. Interface arg to a standalone procedure. }
  SrcNativeIntfParamProc = '''
    program Prg;
    type
      IPrinter = interface
        procedure Print;
      end;
      TDoc = class(TObject, IPrinter)
        procedure Print;
      end;
    procedure TDoc.Print;
    begin WriteLn('doc') end;
    procedure UsePrinter(P: IPrinter);
    begin P.Print() end;
    var
      D: TDoc;
      I: IPrinter;
    begin
      D := TDoc.Create();
      I := D;
      UsePrinter(I)
    end.
    ''';

  { 2. Interface arg to a class method. }
  SrcNativeIntfParamMethod = '''
    program Prg;
    type
      IPrinter = interface
        procedure Print;
      end;
      TDoc = class(TObject, IPrinter)
        procedure Print;
      end;
      TRunner = class
        procedure Run(P: IPrinter);
      end;
    procedure TDoc.Print;
    begin WriteLn('method') end;
    procedure TRunner.Run(P: IPrinter);
    begin P.Print() end;
    var
      D: TDoc;
      I: IPrinter;
      R: TRunner;
    begin
      D := TDoc.Create();
      I := D;
      R := TRunner.Create();
      R.Run(I)
    end.
    ''';

  { 3. Interface arg to a constructor. }
  SrcNativeIntfParamCtor = '''
    program Prg;
    type
      IPrinter = interface
        procedure Print;
      end;
      TDoc = class(TObject, IPrinter)
        procedure Print;
      end;
      THolder = class
        FP: IPrinter;
        constructor Create(P: IPrinter);
        procedure Use;
      end;
    procedure TDoc.Print;
    begin WriteLn('ctor') end;
    constructor THolder.Create(P: IPrinter);
    begin FP := P end;
    procedure THolder.Use;
    begin FP.Print() end;
    var
      D: TDoc;
      I: IPrinter;
      H: THolder;
    begin
      D := TDoc.Create();
      I := D;
      H := THolder.Create(I);
      H.Use()
    end.
    ''';

  { 4. Interface arg to an inherited call. }
  SrcNativeIntfParamInherited = '''
    program Prg;
    type
      IPrinter = interface
        procedure Print;
      end;
      TDoc = class(TObject, IPrinter)
        procedure Print;
      end;
      TBase = class
        procedure Use(P: IPrinter); virtual;
      end;
      TChild = class(TBase)
        procedure Use(P: IPrinter); override;
      end;
    procedure TDoc.Print;
    begin WriteLn('inherited') end;
    procedure TBase.Use(P: IPrinter);
    begin P.Print() end;
    procedure TChild.Use(P: IPrinter);
    begin inherited Use(P) end;
    var
      D: TDoc;
      I: IPrinter;
      C: TChild;
    begin
      D := TDoc.Create();
      I := D;
      C := TChild.Create();
      C.Use(I)
    end.
    ''';

  { 5. Passing a class expression directly as an interface parameter. }
  SrcNativeIntfParamClassExpr = '''
    program Prg;
    type
      IPrinter = interface
        procedure Print;
      end;
      TDoc = class(TObject, IPrinter)
        procedure Print;
      end;
    procedure TDoc.Print;
    begin WriteLn('class-expr') end;
    procedure UsePrinter(P: IPrinter);
    begin P.Print() end;
    begin
      UsePrinter(TDoc.Create())
    end.
    ''';

  { M8 — inherited calls.  An override that chains to the parent body via
    `inherited` must dispatch statically to the parent method. }
  SrcInheritedProc = '''
    program Prg;
    type
      TBase = class
        procedure Hello; virtual;
      end;
      TDer = class(TBase)
        procedure Hello; override;
      end;
    procedure TBase.Hello;
    begin WriteLn('base') end;
    procedure TDer.Hello;
    begin
      inherited Hello();
      WriteLn('derived')
    end;
    var D: TDer;
    begin
      D := TDer.Create();
      D.Hello()
    end.
    ''';

  { A value-returning `inherited Calc(N)` statement seeds Result with the
    parent's return value (which the override then adjusts). }
  SrcInheritedFunc = '''
    program Prg;
    type
      TBase = class
        function Calc(N: Integer): Integer; virtual;
      end;
      TDer = class(TBase)
        function Calc(N: Integer): Integer; override;
      end;
    function TBase.Calc(N: Integer): Integer;
    begin Result := N * 2 end;
    function TDer.Calc(N: Integer): Integer;
    begin
      inherited Calc(N);
      Result := Result + 1
    end;
    var D: TDer;
    begin
      D := TDer.Create();
      WriteLn(D.Calc(10))
    end.
    ''';

  { M8 — a var/out parameter to a method call must pass the caller's address so
    the mutation is visible after the call. }
  SrcMethodVarParam = '''
    program Prg;
    type
      TFoo = class
        procedure Bump(var X: Integer);
      end;
    procedure TFoo.Bump(var X: Integer);
    begin X := X + 1 end;
    var
      F: TFoo;
      N: Integer;
    begin
      F := TFoo.Create();
      N := 5;
      F.Bump(N);
      WriteLn(N)
    end.
    ''';

  SrcMethodVarSwap = '''
    program Prg;
    type
      TSwapper = class
        procedure Swap(var A, B: Integer);
      end;
    procedure TSwapper.Swap(var A, B: Integer);
    var T: Integer;
    begin T := A; A := B; B := T end;
    var
      S: TSwapper;
      X, Y: Integer;
    begin
      S := TSwapper.Create();
      X := 3; Y := 7;
      S.Swap(X, Y);
      WriteLn(X);
      WriteLn(Y)
    end.
    ''';

  SrcRecordStaticArrayField = '''
    program Prg;
    type
      TRec = record
        X: Integer;
        Arr: array[0..1] of Integer;
      end;
    function MakeRec: TRec;
    begin
      Result.X := 99
    end;
    function ReadAt(var R: TRec; I: Integer): Integer;
    begin
      Result := R.Arr[I]
    end;
    var R: TRec;
    begin
      R := MakeRec();
      WriteLn(R.X);
      WriteLn(ReadAt(R, 0));
      WriteLn(ReadAt(R, 1))
    end.
    ''';

  SrcArcClassField = '''
    program Prg;
    type
      TChild = class
        X: Integer;
      end;
      TParent = class
        Child: TChild;
      end;
    var
      Pa: TParent;
      C: TChild;
    begin
      Pa := TParent.Create();
      C := TChild.Create();
      C.X := 42;
      Pa.Child := C;
      C := Pa.Child;
      WriteLn(C.X)
    end.
    ''';

  SrcArcStringField = '''
    program Prg;
    type
      THolder = class
        S: string;
      end;
    var H: THolder;
    begin
      H := THolder.Create();
      H.S := 'hello';
      WriteLn(H.S)
    end.
    ''';

  SrcArcClassAssignNil = '''
    program Prg;
    type
      TThing = class
        destructor Destroy; override;
      end;
    destructor TThing.Destroy;
    begin
      WriteLn('destroyed');
      inherited Destroy()
    end;
    var O: TThing;
    begin
      O := TThing.Create();
      O := nil;
      WriteLn('done')
    end.
    ''';

  SrcArcValueParamString = '''
    program Prg;
    procedure PrintIt(S: string);
    begin
      WriteLn(S)
    end;
    var Msg: string;
    begin
      Msg := 'arc-ok';
      PrintIt(Msg);
      WriteLn(Msg)
    end.
    ''';

  SrcArcValueParamClass = '''
    program Prg;
    type
      TObj = class
        X: Integer;
      end;
    procedure PrintX(O: TObj);
    begin
      WriteLn(O.X)
    end;
    var Obj: TObj;
    begin
      Obj := TObj.Create();
      Obj.X := 7;
      PrintX(Obj);
      WriteLn(Obj.X)
    end.
    ''';

  { Value-returning function whose return value must survive the epilogue ARC
    release pass.  A function returning Integer but taking an ARC (class) value
    param releases that param on exit (_ClassRelease clobbers %rax); the Result
    must be loaded into %rax AFTER that release, not before.  Previously the
    native backend loaded Result first and returned garbage (e.g. 3 not 55). }
  SrcRetValSurvivesArcRelease = '''
    program Prg;
    type
      TGreeter = class
        function Greet: Integer;
      end;
      TUser = class
        function Use(O: TGreeter): Integer;
      end;
    function TGreeter.Greet: Integer; begin Result := 55 end;
    function TUser.Use(O: TGreeter): Integer;
    begin
      Result := O.Greet()
    end;
    var T: TGreeter; U: TUser;
    begin
      T := TGreeter.Create();
      U := TUser.Create();
      WriteLn(U.Use(T))
    end.
    ''';

  { Interface value argument passed to a method, dispatched inside the callee.
    Exercises the fat-pointer arg ABI at a method call site AND the
    return-value-survives-release fix (the callee releases the interface param). }
  SrcIntfArgToMethod = '''
    program Prg;
    type
      IGreeter = interface
        function Greet: Integer;
      end;
      TGreeter = class(TObject, IGreeter)
        function Greet: Integer;
      end;
      TUser = class
        function Use(G: IGreeter): Integer;
      end;
    function TGreeter.Greet: Integer; begin Result := 55 end;
    function TUser.Use(G: IGreeter): Integer;
    begin
      Result := G.Greet()
    end;
    var T: TGreeter; I: IGreeter; U: TUser;
    begin
      T := TGreeter.Create();
      I := T;
      U := TUser.Create();
      WriteLn(U.Use(I))
    end.
    ''';

  SrcIntfFieldAsArg = '''
    program Prg;
    type
      IVal = interface
        function Get: Integer;
      end;
      TVal = class(TObject, IVal)
        V: Integer;
        function Get: Integer;
      end;
      THolder = class
        F: IVal;
      end;
    function TVal.Get: Integer; begin Result := V end;
    function ReadIntf(X: IVal): Integer;
    begin
      Result := X.Get()
    end;
    var H: THolder; T: TVal;
    begin
      T := TVal.Create();
      T.V := 77;
      H := THolder.Create();
      H.F := T;
      WriteLn(ReadIntf(H.F))
    end.
    ''';

  SrcIntfFieldNilAssign = '''
    program Prg;
    type
      IVal = interface
        function Get: Integer;
      end;
      TVal = class(TObject, IVal)
        V: Integer;
        function Get: Integer;
      end;
      THolder = class
        F: IVal;
        procedure ClearField;
      end;
    function TVal.Get: Integer; begin Result := V end;
    procedure THolder.ClearField;
    begin
      F := nil
    end;
    var H: THolder; T: TVal;
    begin
      T := TVal.Create();
      T.V := 99;
      H := THolder.Create();
      H.F := T;
      WriteLn(H.F.Get());
      H.ClearField();
      if not Assigned(H.F) then
        WriteLn('cleared')
    end.
    ''';

  SrcDynArrayElemArcString = '''
    program Prg;
    var A: array of String;
    begin
      SetLength(A, 2);
      A[0] := 'first';
      A[1] := 'second';
      WriteLn(A[0]);
      WriteLn(A[1]);
      A[0] := 'replaced';
      WriteLn(A[0]);
      WriteLn(A[1])
    end.
    ''';

  SrcIntfFuncReturn = '''
    program Prg;
    type
      IVal = interface
        function Get(): Integer;
      end;
      TVal = class(TObject, IVal)
        V: Integer;
        function Get(): Integer;
      end;
    function TVal.Get(): Integer;
    begin
      Result := V
    end;
    function MakeVal(N: Integer): IVal;
    var T: TVal;
    begin
      T := TVal.Create();
      T.V := N;
      Result := T
    end;
    var I: IVal;
    begin
      I := MakeVal(42);
      WriteLn(I.Get())
    end.
    ''';

  { Class-receiver method calls returning an interface (Obj.Make()) —
    sret protocol with the receiver in %rsi.  Covers all three LHS
    shapes of EmitInterfaceAssign (local/global var, sret Result,
    implicit-Self field) plus static and virtual dispatch. }
  SrcIntfFromClassMethod = '''
    program Prg;
    type
      IThing = interface
        function Tag(): Integer;
      end;
      TThing = class(TObject, IThing)
        V: Integer;
        function Tag(): Integer;
      end;
      TFactory = class
        F: IThing;
        function Make(N: Integer): IThing;
        function MakeVirt(N: Integer): IThing; virtual;
        procedure Fill(N: Integer);
      end;
      TSubFactory = class(TFactory)
        function MakeVirt(N: Integer): IThing; override;
      end;
    function TThing.Tag(): Integer;
    begin
      Result := V
    end;
    function TFactory.Make(N: Integer): IThing;
    var T: TThing;
    begin
      T := TThing.Create();
      T.V := N;
      Result := T
    end;
    function TFactory.MakeVirt(N: Integer): IThing;
    begin
      Result := Self.Make(N + 100)
    end;
    function TSubFactory.MakeVirt(N: Integer): IThing;
    begin
      Result := Self.Make(N + 200)
    end;
    procedure TFactory.Fill(N: Integer);
    begin
      F := Self.Make(N)
    end;
    var
      Fac: TFactory;
      G: IThing;
    procedure RunLocal;
    var L: IThing;
    begin
      L := Fac.Make(1);
      WriteLn(L.Tag())
    end;
    begin
      Fac := TFactory.Create();
      RunLocal();
      G := Fac.Make(2);
      WriteLn(G.Tag());
      G := Fac.MakeVirt(3);
      WriteLn(G.Tag());
      Fac.Fill(5);
      WriteLn(Fac.F.Tag());
      Fac := TSubFactory.Create();
      G := Fac.MakeVirt(3);
      WriteLn(G.Tag())
    end.
    ''';

  SrcIntfFieldFromFunc = '''
    program Prg;
    type
      IVal = interface
        function Get(): Integer;
      end;
      TVal = class(TObject, IVal)
        V: Integer;
        function Get(): Integer;
      end;
      THolder = class
        F: IVal;
        procedure SetVal(N: Integer);
      end;
    function TVal.Get(): Integer;
    begin
      Result := V
    end;
    function MakeVal(N: Integer): IVal;
    var T: TVal;
    begin
      T := TVal.Create();
      T.V := N;
      Result := T
    end;
    procedure THolder.SetVal(N: Integer);
    begin
      F := MakeVal(N)
    end;
    var H: THolder;
    begin
      H := THolder.Create();
      H.F := MakeVal(10);
      WriteLn(H.F.Get());
      H.SetVal(20);
      WriteLn(H.F.Get())
    end.
    ''';

  SrcWeakInterfaceVar = '''
    program Prg;
    type
      IVal = interface
        function Get(): Integer;
      end;
      TVal = class(TObject, IVal)
        V: Integer;
        function Get(): Integer;
        destructor Destroy; override;
      end;
    function TVal.Get(): Integer;
    begin
      Result := V
    end;
    destructor TVal.Destroy;
    begin
      WriteLn('destroyed');
      inherited Destroy()
    end;
    var
      S: IVal;
      [Weak] W: IVal;
    begin
      S := TVal.Create();
      TVal(S).V := 77;
      W := S;
      WriteLn(W.Get());
      S := nil;
      WriteLn('done')
    end.
    ''';

  SrcSretTempFieldRelease = '''
    program Prg;
    type
      TRec = record
        S: String;
      end;
    function MakeRec(V: String): TRec;
    begin
      Result.S := V
    end;
    procedure Consume(R: TRec);
    begin
      WriteLn(R.S)
    end;
    begin
      Consume(MakeRec('hello'));
      WriteLn('done')
    end.
    ''';

  { Dyn-array field inside a class: the field must be ARC-refcounted on store
    and released when the holder is destroyed (f74e5cc).  Observed by reading an
    element back after the field assignment — a dropped/garbled buffer would
    diverge from the QBE backend's output. }
  SrcArcDynArrayField = '''
    program Prg;
    type
      THolder = class
        Data: array of Integer;
      end;
    var
      H: THolder;
      A: array of Integer;
    begin
      H := THolder.Create();
      SetLength(A, 3);
      A[0] := 11;
      A[1] := 22;
      A[2] := 33;
      H.Data := A;
      WriteLn(H.Data[1])
    end.
    ''';

  { Interface field inside a class: assign a class instance into the field
    (935bd52).  The fat pointer (obj+itab) must be stored whole with ARC on the
    obj slot, and released when the holder is destroyed.  Observed via the
    implementing class's destructor, which must fire exactly once when the holder
    is released — proving the field stored a refcounted obj and that field
    cleanup releases it.  (Dispatch directly through a non-Self interface field
    is a separate, pre-existing native gap not covered here.) }
  { Dispatch a method directly through an interface stored in a (non-Self)
    class field — H.G.Greet() — including a method that takes an argument.  The
    receiver's fat pointer must be loaded from the field's contiguous memory. }
  SrcIntfFieldDispatch = '''
    program Prg;
    type
      IShape = interface
        function Area(Scale: Integer): Integer;
      end;
      TBox = class(TObject, IShape)
        function Area(Scale: Integer): Integer;
      end;
      THolder = class
        S: IShape;
      end;
    function TBox.Area(Scale: Integer): Integer;
    begin Result := 10 * Scale end;
    var H: THolder;
    begin
      H := THolder.Create();
      H.S := TBox.Create();
      WriteLn(H.S.Area(3));
      WriteLn(H.S.Area(5))
    end.
    ''';

  { Read an interface OUT of a field into an interface local (G := H.G), then
    dispatch on the local.  Exercises the interface-to-interface assignment with
    a field-access source. }
  SrcIntfFieldReadIntoLocal = '''
    program Prg;
    type
      IShape = interface
        function Area(Scale: Integer): Integer;
      end;
      TBox = class(TObject, IShape)
        function Area(Scale: Integer): Integer;
      end;
      THolder = class
        S: IShape;
      end;
    function TBox.Area(Scale: Integer): Integer;
    begin Result := 10 * Scale end;
    var H: THolder; G: IShape;
    begin
      H := THolder.Create();
      H.S := TBox.Create();
      G := H.S;
      WriteLn(G.Area(4))
    end.
    ''';

  SrcArcInterfaceField = '''
    program Prg;
    type
      IGreeter = interface
        function Greet: Integer;
      end;
      TGreeter = class(TObject, IGreeter)
        function Greet: Integer;
        destructor Destroy; override;
      end;
      THolder = class
        G: IGreeter;
      end;
    function TGreeter.Greet: Integer;
    begin
      Result := 77
    end;
    destructor TGreeter.Destroy;
    begin
      WriteLn('greeter-gone');
      inherited Destroy()
    end;
    var
      H: THolder;
      G: IGreeter;
    begin
      H := THolder.Create();
      G := TGreeter.Create();
      H.G := G;
      G := nil;
      WriteLn('mid');
      H := nil;
      WriteLn('end')
    end.
    ''';

  { Nested record field whose own field is a managed class reference.  When the
    parent class is destroyed, _FieldCleanup must recurse through the record
    field and release the inner class — firing its destructor exactly once
    (f74e5cc nested-record recursion). }
  SrcArcNestedRecordField = '''
    program Prg;
    type
      TInner = class
        destructor Destroy; override;
      end;
      TRec = record
        Obj: TInner;
      end;
      THolder = class
        R: TRec;
      end;
    destructor TInner.Destroy;
    begin
      WriteLn('inner-gone');
      inherited Destroy()
    end;
    var H: THolder;
    begin
      H := THolder.Create();
      H.R.Obj := TInner.Create();
      WriteLn('before');
      H := nil;
      WriteLn('after')
    end.
    ''';

  { A function returning a String, its +1 result assigned straight into a class
    field.  The field store must consume the transferred reference (no extra
    AddRef), so the buffer is freed exactly once — observed indirectly by the
    program completing and printing the value identically on both backends
    (96514ee).  A double-retain would leak; a missing retain would free early
    and corrupt the read-back. }
  SrcArcStringReturnToField = '''
    program Prg;
    type
      THolder = class
        S: string;
      end;
    function MakeMsg: string;
    begin
      Result := 'built'
    end;
    var H: THolder;
    begin
      H := THolder.Create();
      H.S := MakeMsg();
      WriteLn(H.S);
      WriteLn(H.S)
    end.
    ''';

  { Implicit-Self string field assigned inside a method: FName := value must
    retain the new value and release the old, so reassigning the field does not
    leak or use-after-free (ARC on the ImplicitSelfField path). }
  SrcArcImplicitSelfStringField = '''
    program Prg;
    type
      THolder = class
        Name: string;
        procedure SetName(const V: string);
      end;
    procedure THolder.SetName(const V: string);
    begin
      Name := V
    end;
    var H: THolder;
    begin
      H := THolder.Create();
      H.SetName('first');
      H.SetName('second');
      WriteLn(H.Name)
    end.
    ''';

  SrcAddrOfLocalVar = '''
    program Prg;
    var
      X: Integer;
      P: ^Integer;
    begin
      X := 42;
      P := @X;
      P^ := 99;
      WriteLn(X)
    end.
    ''';

  SrcAddrOfStaticArrayElem = '''
    program Prg;
    var
      A: array[0..3] of Integer;
      P: ^Integer;
    begin
      A[0] := 10;
      A[1] := 20;
      A[2] := 30;
      A[3] := 40;
      P := @A[2];
      WriteLn(P^)
    end.
    ''';

  SrcAddrOfDynArrayElem = '''
    program Prg;
    var
      A: array of Integer;
      P: ^Integer;
    begin
      SetLength(A, 3);
      A[0] := 100;
      A[1] := 200;
      A[2] := 300;
      P := @A[1];
      WriteLn(P^)
    end.
    ''';

  SrcAddrOfRecFieldArrElem = '''
    program Prg;
    type
      TRec = record
        Items: array of Integer;
      end;
    var
      A: array of Integer;
      R: TRec;
      P: ^Integer;
    begin
      SetLength(A, 3);
      A[0] := 5;
      A[1] := 15;
      A[2] := 25;
      R.Items := A;
      P := @R.Items[2];
      WriteLn(P^)
    end.
    ''';

  SrcAddrOfMethodPtr = '''
    program Prg;
    type
      TAddProc = procedure(A, B: Integer) of object;
      TCalc = class
        procedure Add(A, B: Integer);
        begin
          WriteLn(A + B)
        end;
      end;
    var
      C: TCalc;
      F: TAddProc;
    begin
      C := TCalc.Create();
      F := @C.Add;
      F(3, 4)
    end.
    ''';

  SrcBitwiseNotInt = '''
    program Prg;
    var I: Integer;
    begin
      I := 0;
      WriteLn(not I)
    end.
    ''';

  SrcBitwiseNotBitmask = '''
    program Prg;
    const MASK = 3;
    var Flags: Integer;
    begin
      Flags := 7;
      Flags := Flags and (not MASK);
      WriteLn(Flags)
    end.
    ''';

  SrcGenericRecordMethod = '''
    program Prg;
    type
      THolder<T> = record
        Value: T;
        function GetValue: T;
        begin
          Result := Self.Value
        end;
      end;
    var
      H: THolder<Integer>;
    begin
      H.Value := 42;
      WriteLn(H.GetValue())
    end.
    ''';

  SrcGenericClassMethod = '''
    program Prg;
    type
      TBox<T> = class
        FVal: T;
        procedure SetVal(AVal: T);
        begin
          Self.FVal := AVal
        end;
        function GetVal: T;
        begin
          Result := Self.FVal
        end;
      end;
    var
      B: TBox<Integer>;
    begin
      B := TBox<Integer>.Create();
      B.SetVal(99);
      WriteLn(B.GetVal())
    end.
    ''';

  SrcGenericFuncStandalone = '''
    program Prg;
    function Identity<T>(X: T): T;
    begin
      Result := X
    end;
    begin
      WriteLn(Identity<Integer>(7))
    end.
    ''';

  SrcGenericClassInterface = '''
    program Prg;
    type
      IValue = interface
        function GetValue: Integer;
      end;
      TBox<T> = class(TObject, IValue)
        FVal: T;
        procedure SetVal(AVal: T);
        begin
          Self.FVal := AVal
        end;
        function GetValue: Integer;
        begin
          Result := Self.FVal
        end;
      end;
    var
      V: IValue;
      B: TBox<Integer>;
    begin
      B := TBox<Integer>.Create();
      B.SetVal(55);
      V := B;
      WriteLn(V.GetValue())
    end.
    ''';

procedure TE2ENativeTests.TestRun_Native_OpenArray_Sum;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcOASum, '15' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_OpenArray_HighLow;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcOAHighLow, '0' + LE + '2' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_OpenArray_Length;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcOALength, '3' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_StaticToOpen_Length;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcStaticToOpenLen, '5' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_StaticToOpen_Sum;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcStaticToOpenSum, '60' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_StaticToOpen_PassToNested;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcStaticToOpenNested, '30' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_DynArray_SetLengthAndAccess;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDynArrayBasic, '10' + LE + '20' + LE + '30' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_DynArray_LengthAndHigh;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDynArrayLenHigh, '5' + LE + '4' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Interface_ZeroArgDispatch;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcIntfZeroArg, '42' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Interface_ArgDispatch;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcIntfArg, '30' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Interface_ProcDispatch;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcIntfProc, 'box' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Interface_IntfToIntfCopy;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcIntfCopy, '21' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Interface_AsCast;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcIntfAsCast, '7' + LE + '99' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Interface_NilClear;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcIntfNilClear, '5' + LE + '13' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Inherited_Proc;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcInheritedProc, 'base' + LE + 'derived' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Inherited_FuncSetsResult;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcInheritedFunc, '21' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_MethodVarParam_Mutates;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcMethodVarParam, '6' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_MethodVarParam_Swap;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcMethodVarSwap, '7' + LE + '3' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_InterfaceField_ShadowsGlobal;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcNativeIntfFieldShadowsGlobal, 'printed' + LE, 0);
end;


procedure TE2ENativeTests.TestRun_Native_IntfParam_Proc;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcNativeIntfParamProc, 'doc' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IntfParam_Method;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcNativeIntfParamMethod, 'method' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IntfParam_Constructor;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcNativeIntfParamCtor, 'ctor' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IntfParam_Inherited;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcNativeIntfParamInherited, 'inherited' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IntfParam_ClassExpr;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcNativeIntfParamClassExpr, 'class-expr' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_RecordArrayField_StaticRead;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcRecordStaticArrayField, '99' + LE + '0' + LE + '0' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ArcClassField_StoreAndRead;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcArcClassField, '42' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ArcStringField_StoreAndRead;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcArcStringField, 'hello' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ArcClassAssignNil_Destroys;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcArcClassAssignNil, 'destroyed' + LE + 'done' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ArcDynArrayField_StoreAndRead;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcArcDynArrayField, '22' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ArcInterfaceField_AssignAndDispatch;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcArcInterfaceField,
    'mid' + LE + 'greeter-gone' + LE + 'end' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IntfFieldDispatch;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcIntfFieldDispatch, '30' + LE + '50' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IntfFieldReadIntoLocal;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcIntfFieldReadIntoLocal, '40' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_RetValSurvivesArcRelease;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcRetValSurvivesArcRelease, '55' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IntfArgToMethod;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcIntfArgToMethod, '55' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ArcNestedRecordField_FullCleanup;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcArcNestedRecordField,
    'before' + LE + 'inner-gone' + LE + 'after' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ArcStringReturnToField_NoDoubleRetain;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcArcStringReturnToField, 'built' + LE + 'built' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ArcImplicitSelfStringField_Reassign;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcArcImplicitSelfStringField, 'second' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ArcValueParam_String;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcArcValueParamString, 'arc-ok' + LE + 'arc-ok' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ArcValueParam_Class;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcArcValueParamClass, '7' + LE + '7' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_AddrOf_LocalVariable;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcAddrOfLocalVar, '99' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_AddrOf_StaticArrayElement;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcAddrOfStaticArrayElem, '30' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_AddrOf_DynArrayElement;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcAddrOfDynArrayElem, '200' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_AddrOf_RecordFieldArrayElem;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcAddrOfRecFieldArrElem, '25' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_AddrOf_MethodPointer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcAddrOfMethodPtr, '7' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_BitwiseNot_Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcBitwiseNotInt, '-1' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_BitwiseNot_Bitmask;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcBitwiseNotBitmask, '4' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_GenericRecord_Method;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcGenericRecordMethod, '42' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_GenericClass_Method;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcGenericClassMethod, '99' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_GenericFunc_Standalone;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcGenericFuncStandalone, '7' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_GenericClass_Interface;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcGenericClassInterface, '55' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_SizeOf_Record;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcSizeOfRecord, '8' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_SizeOf_GenericRecord;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcSizeOfGenericRecord, '8' + LE + '16' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Record_NestedFieldAssign;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcNestedRecordFieldAssign, '2037' + LE + '2037' + LE, 0);
end;

{ ------------------------------------------------------------------ }
{ Multi-unit whole-program native path.  Each test compiles a user unit
  plus a program that uses it on BOTH backends and asserts the native
  stdout/exit-code equal the QBE oracle's (differential testing). }
{ ------------------------------------------------------------------ }

procedure TE2ENativeTests.TestRun_Native_MultiUnit_PlainFunction;
var
  UnitSrc, ProgSrc, NOut, QOut: string;
  NCode, QCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  UnitSrc := '''
    unit mu_pf;
    interface
    function Doubled(X: Integer): Integer;
    implementation
    function Doubled(X: Integer): Integer;
    begin Result := X * 2; end;
    end.
    ''';
  ProgSrc := '''
    program Prg;
    uses mu_pf;
    begin WriteLn(Doubled(21)); end.
    ''';
  AssertTrue('native compile+run',
    CompileAndRunWithUnitNative('mu_pf', UnitSrc, ProgSrc, NOut, NCode));
  AssertTrue('qbe compile+run',
    CompileAndRunWithUnit('mu_pf', UnitSrc, ProgSrc, QOut, QCode));
  AssertEquals('stdout parity', QOut, NOut);
  AssertEquals('exit parity', QCode, NCode);
  AssertEquals('value', '42' + LE, NOut);
end;

procedure TE2ENativeTests.TestRun_Native_MultiUnit_StringFunction;
var
  UnitSrc, ProgSrc, NOut, QOut: string;
  NCode, QCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  UnitSrc := '''
    unit mu_sf;
    interface
    function Greeting(const AName: string): string;
    implementation
    function Greeting(const AName: string): string;
    begin Result := 'Hello, ' + AName + '!'; end;
    end.
    ''';
  ProgSrc := '''
    program Prg;
    uses mu_sf;
    begin WriteLn(Greeting('World')); end.
    ''';
  AssertTrue('native compile+run',
    CompileAndRunWithUnitNative('mu_sf', UnitSrc, ProgSrc, NOut, NCode));
  AssertTrue('qbe compile+run',
    CompileAndRunWithUnit('mu_sf', UnitSrc, ProgSrc, QOut, QCode));
  AssertEquals('stdout parity', QOut, NOut);
  AssertEquals('exit parity', QCode, NCode);
  AssertEquals('value', 'Hello, World!' + LE, NOut);
end;

procedure TE2ENativeTests.TestRun_Native_MultiUnit_Class;
var
  UnitSrc, ProgSrc, NOut, QOut: string;
  NCode, QCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  UnitSrc := '''
    unit mu_cl;
    interface
    type
      TCounter = class
      private FValue: Integer;
      public
        constructor Create(AStart: Integer);
        procedure Bump;
        function Value: Integer;
        function Describe: string; virtual;
      end;
    implementation
    constructor TCounter.Create(AStart: Integer); begin FValue := AStart; end;
    procedure TCounter.Bump; begin FValue := FValue + 1; end;
    function TCounter.Value: Integer; begin Result := FValue; end;
    function TCounter.Describe: string; begin Result := 'Counter'; end;
    end.
    ''';
  ProgSrc := '''
    program Prg;
    uses mu_cl;
    var C: TCounter;
    begin
      C := TCounter.Create(10);
      C.Bump(); C.Bump();
      WriteLn(C.Describe(), ' = ', C.Value());
      C.Free();
    end.
    ''';
  AssertTrue('native compile+run',
    CompileAndRunWithUnitNative('mu_cl', UnitSrc, ProgSrc, NOut, NCode));
  AssertTrue('qbe compile+run',
    CompileAndRunWithUnit('mu_cl', UnitSrc, ProgSrc, QOut, QCode));
  AssertEquals('stdout parity', QOut, NOut);
  AssertEquals('exit parity', QCode, NCode);
  AssertEquals('value', 'Counter = 12' + LE, NOut);
end;

procedure TE2ENativeTests.TestRun_Native_MultiUnit_Interface;
var
  UnitSrc, ProgSrc, NOut, QOut: string;
  NCode, QCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  UnitSrc := '''
    unit mu_if;
    interface
    type
      ISpeaker = interface
        function Speak: string;
      end;
      TDog = class(TObject, ISpeaker) public function Speak: string; end;
      TCat = class(TObject, ISpeaker) public function Speak: string; end;
    implementation
    function TDog.Speak: string; begin Result := 'Woof'; end;
    function TCat.Speak: string; begin Result := 'Meow'; end;
    end.
    ''';
  ProgSrc := '''
    program Prg;
    uses mu_if;
    var S: ISpeaker;
    begin
      S := TDog.Create(); WriteLn(S.Speak());
      S := TCat.Create(); WriteLn(S.Speak());
    end.
    ''';
  AssertTrue('native compile+run',
    CompileAndRunWithUnitNative('mu_if', UnitSrc, ProgSrc, NOut, NCode));
  AssertTrue('qbe compile+run',
    CompileAndRunWithUnit('mu_if', UnitSrc, ProgSrc, QOut, QCode));
  AssertEquals('stdout parity', QOut, NOut);
  AssertEquals('exit parity', QCode, NCode);
  AssertEquals('value', 'Woof' + LE + 'Meow' + LE, NOut);
end;

procedure TE2ENativeTests.TestRun_Native_MultiUnit_GlobalsAndInit;
var
  UnitSrc, ProgSrc, NOut, QOut: string;
  NCode, QCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  UnitSrc := '''
    unit mu_gi;
    interface
    var GCounter: Integer; GLabel: string;
    procedure Increment;
    implementation
    procedure Increment; begin GCounter := GCounter + 1; end;
    initialization
      GCounter := 100;
      GLabel := 'configured';
    end.
    ''';
  ProgSrc := '''
    program Prg;
    uses mu_gi;
    begin
      WriteLn(GLabel, ' ', GCounter);
      Increment(); Increment();
      WriteLn(GCounter);
    end.
    ''';
  AssertTrue('native compile+run',
    CompileAndRunWithUnitNative('mu_gi', UnitSrc, ProgSrc, NOut, NCode));
  AssertTrue('qbe compile+run',
    CompileAndRunWithUnit('mu_gi', UnitSrc, ProgSrc, QOut, QCode));
  AssertEquals('stdout parity', QOut, NOut);
  AssertEquals('exit parity', QCode, NCode);
  AssertEquals('value', 'configured 100' + LE + '102' + LE, NOut);
end;

{ --- By-value record param tests ------------------------------------------ }

procedure TE2ENativeTests.TestRun_Native_RecordParam_ReadOnly;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    type TRec = record S: string; end;
    procedure Show(R: TRec);
    begin WriteLn('in: ', R.S) end;
    var W: TRec;
    begin
      W.S := 'heap-' + 'allocated';
      Show(W);
      WriteLn('out: ', W.S)
    end.
    ''',
    'in: heap-allocated' + LE + 'out: heap-allocated' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_RecordParam_Mutate;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    type TR = record S: string; end;
    procedure Mutate(R: TR); begin R.S := 'new' end;
    var W: TR;
    begin
      W.S := 'heap-' + 'allocated';
      Mutate(W);
      WriteLn(W.S)
    end.
    ''',
    'heap-allocated' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_RecordParam_ThreeStrings;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    type TR = record A: string; B: string; C: string; end;
    procedure Mutate(R: TR); begin R.A := 'changed' end;
    var W: TR;
    begin
      W.A := 'heap-' + 'one';
      W.B := 'heap-' + 'two';
      W.C := 'heap-' + 'three';
      Mutate(W);
      WriteLn(W.A)
    end.
    ''',
    'heap-one' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_RecordParam_IntOnly;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    type TR = record A: Integer; B: Integer; end;
    procedure Show(R: TR); begin WriteLn(R.A + R.B) end;
    var W: TR;
    begin W.A := 40; W.B := 2; Show(W) end.
    ''',
    '42' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_RecordParam_InlineSretArg;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    type TInner = record N: string; end;
         TOuter = record S: string; Inner: TInner; end;
    function MakeOuter: TOuter;
    begin Result.S := 'outer-' + 'heap'; Result.Inner.N := 'inner-' + 'heap' end;
    procedure Consume(R: TOuter);
    begin WriteLn(R.S, '|', R.Inner.N) end;
    begin
      Consume(MakeOuter())
    end.
    ''',
    'outer-heap|inner-heap' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_RecordParam_ConstSkipsArc;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    type TR = record S: string; end;
    procedure Show(const R: TR);
    begin WriteLn(R.S) end;
    var W: TR;
    begin
      W.S := 'heap-' + 'text';
      Show(W);
      WriteLn(W.S)
    end.
    ''',
    'heap-text' + LE + 'heap-text' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ShortCircuit_AndSkipsRhs;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    var X: Integer;
    begin
      X := 5;
      if (X > 3) and (X < 10) then
        WriteLn('both')
      else
        WriteLn('nope');
      if (X > 100) and (X < 200) then
        WriteLn('bad')
      else
        WriteLn('skipped')
    end.
    ''',
    'both' + LE + 'skipped' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ShortCircuit_OrSkipsRhs;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    var X: Integer;
    begin
      X := 5;
      if (X = 5) or (X = 99) then
        WriteLn('first-true')
      else
        WriteLn('nope');
      if (X = 99) or (X = 5) then
        WriteLn('second-true')
      else
        WriteLn('nope')
    end.
    ''',
    'first-true' + LE + 'second-true' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ShortCircuit_AndNilGuard;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    type TFoo = class
      public
        N: Integer;
        constructor Create(AVal: Integer);
      end;
    constructor TFoo.Create(AVal: Integer);
    begin N := AVal end;
    var Obj: TFoo;
    begin
      Obj := nil;
      if (Obj <> nil) and (Obj.N = 42) then
        WriteLn('bad')
      else
        WriteLn('nil-guarded');
      Obj := TFoo.Create(42);
      if (Obj <> nil) and (Obj.N = 42) then
        WriteLn('found')
      else
        WriteLn('bad')
    end.
    ''',
    'nil-guarded' + LE + 'found' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ProceduralParam;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    type TIntFunc = function(X: Integer): Integer;
    function Twice(X: Integer): Integer;
    begin Result := X * 2 end;
    function Apply(F: TIntFunc; V: Integer): Integer;
    begin Result := F(V) end;
    begin
      WriteLn(Apply(@Twice, 21))
    end.
    ''',
    '42' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IsExpr_Class;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    type
      TBase = class public N: Integer; end;
      TChild = class(TBase) public S: string; end;
    var Obj: TBase;
    begin
      Obj := TChild.Create();
      if Obj is TChild then WriteLn('child-yes') else WriteLn('child-no');
      if Obj is TBase then WriteLn('base-yes') else WriteLn('base-no');
      Obj := TBase.Create();
      if Obj is TChild then WriteLn('child-yes') else WriteLn('child-no')
    end.
    ''',
    'child-yes' + LE + 'base-yes' + LE + 'child-no' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_AsExpr_Class;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    type
      TBase = class public N: Integer; end;
      TChild = class(TBase) public S: string; end;
    var B: TBase; C: TChild;
    begin
      B := TChild.Create();
      TChild(B).S := 'hello';
      C := TChild(B as TChild);
      WriteLn(C.S)
    end.
    ''',
    'hello' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_SupportsExpr;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    type
      IGreet = interface procedure Greet; end;
      TFoo = class(IGreet) public procedure Greet; end;
    procedure TFoo.Greet; begin WriteLn('hi') end;
    var Obj: TFoo;
    begin
      Obj := TFoo.Create();
      if Supports(Obj, IGreet) then WriteLn('supports') else WriteLn('no')
    end.
    ''',
    'supports' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IndirectFuncCallExpr;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    type TMapper = function(X: Integer): Integer;
    function Triple(X: Integer): Integer;
    begin Result := X * 3 end;
    var Fns: array[0..0] of TMapper;
    begin
      Fns[0] := @Triple;
      WriteLn(Fns[0](7))
    end.
    ''',
    '21' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Builtin_Ord;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    type TColor = (Red, Green, Blue);
    var C: TColor;
    begin
      C := Blue;
      WriteLn(Ord(C));
      WriteLn(Ord('A'))
    end.
    ''',
    '2' + LE + '65' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Builtin_Assigned;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    type TObj = class end;
    var O: TObj;
    begin
      O := nil;
      if Assigned(O) then WriteLn('yes') else WriteLn('no');
      O := TObj.Create();
      if Assigned(O) then WriteLn('yes') else WriteLn('no')
    end.
    ''',
    'no' + LE + 'yes' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Builtin_Abs;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    begin
      WriteLn(Abs(-42));
      WriteLn(Abs(7));
      WriteLn(Abs(0))
    end.
    ''',
    '42' + LE + '7' + LE + '0' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Builtin_Halt;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    begin
      WriteLn('before');
      Halt(42);
      WriteLn('after')
    end.
    ''',
    'before' + LE, 42);
end;

procedure TE2ENativeTests.TestRun_Native_Builtin_RoundTrunc;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    var D: Double;
    begin
      D := 3.7;
      WriteLn(Round(D));
      WriteLn(Trunc(D))
    end.
    ''',
    '4' + LE + '3' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Builtin_CompareStr;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    begin
      if CompareStr('abc', 'abc') = 0 then WriteLn('eq') else WriteLn('ne');
      if CompareStr('abc', 'abd') < 0 then WriteLn('lt') else WriteLn('ge')
    end.
    ''',
    'eq' + LE + 'lt' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Builtin_UpCase;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    begin
      WriteLn(UpCase(97));
      WriteLn(UpCase(90))
    end.
    ''',
    'A' + LE + 'Z' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Builtin_Int64ToStr;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    var N: Int64;
    begin
      N := 9876543210;
      WriteLn(Int64ToStr(N))
    end.
    ''',
    '9876543210' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_NestedProc_ReadCapture;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    procedure Outer;
    var X: Integer;
      procedure Inner;
      begin WriteLn(X) end;
    begin
      X := 42;
      Inner()
    end;
    begin
      Outer()
    end.
    ''',
    '42' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_NestedProc_WriteCapture;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    procedure Outer;
    var X: Integer;
      procedure Inner;
      begin X := 99 end;
    begin
      X := 0;
      Inner();
      WriteLn(X)
    end;
    begin
      Outer()
    end.
    ''',
    '99' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_NestedProc_CaptureString_LeakFree;
begin
  { A captured string local written inside a nested proc, then read by the
    outer.  The nested store retains the new value and releases the old through
    the capture pointer — must be leak-free on both backends. }
  AssertLeakFreeOnAll('''
    program Prg;
    procedure Outer;
    var S: string;
      procedure SetIt;
      begin S := 'hello ' + 'world' end;
    begin
      S := 'initial';
      SetIt();
      WriteLn(S)
    end;
    begin
      Outer()
    end.
    ''', 'hello world');
end;

procedure TE2ENativeTests.TestRun_Native_NestedProc_CaptureTwoLocals;
begin
  { Two outer vars captured by a nested proc that both reads (base) and writes
    (acc) them — the PromoRewrite shape from the compiler's own backend that
    leg 17 unblocks.  Repeated calls exercise write-back accumulation. }
  AssertRunsOnAll('''
    program Prg;
    function Outer(base: Integer): Integer;
    var acc: Integer;
      procedure Add;
      begin acc := acc + base end;
    begin
      acc := 0;
      Add(); Add(); Add();
      Result := acc
    end;
    begin
      WriteLn(Outer(10))
    end.
    ''', '30' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_NestedProc_CaptureArgsOverflowToStack;
begin
  { Inner captures 2 outer locals AND takes 8 int params — captures take the
    first two int registers, so two params spill to the outgoing stack area.
    The area must be reserved (Finding 1): if the capture args were not counted
    in the sizing walk, the overflow stores would corrupt the caller's frame
    and the sum would be wrong (or crash). Expect 10+20+(1..8)=66. }
  AssertRunsOnAll('''
    program Prg;
    procedure Outer;
    var A, B: Integer;
      procedure Inner(p1, p2, p3, p4, p5, p6, p7, p8: Integer);
      begin
        WriteLn(A + B + p1 + p2 + p3 + p4 + p5 + p6 + p7 + p8)
      end;
    begin
      A := 10; B := 20;
      Inner(1, 2, 3, 4, 5, 6, 7, 8)
    end;
    begin
      Outer()
    end.
    ''', '66' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_NestedProc_GrandparentCapture_Read;
begin
  { L3 (nested in L2, nested in L1) reads V, which is L1's local — two levels
    up.  L2 must forward the capture pointer down to L3.  Expect 17. }
  AssertRunsOnAll('''
    program Prg;
    procedure L1;
    var V: Integer;
      procedure L2;
        procedure L3;
        begin WriteLn(V) end;
      begin L3() end;
    begin V := 17; L2() end;
    begin L1() end.
    ''', '17' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_NestedProc_GrandparentCapture_Write;
begin
  { L3 WRITES the grandparent's V; the outermost reads it after.  The write
    must reach L1's storage through the forwarded capture pointer.  Expect 55. }
  AssertRunsOnAll('''
    program Prg;
    procedure L1;
    var V: Integer;
      procedure L2;
        procedure L3;
        begin V := 55 end;
      begin L3() end;
    begin V := 0; L2(); WriteLn(V) end;
    begin L1() end.
    ''', '55' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_NestedProc_GreatGrandparentCapture;
begin
  { Four levels: L4 writes V owned by L1 (three levels up).  Every
    intermediate level forwards the pointer.  Expect 9. }
  AssertRunsOnAll('''
    program Prg;
    procedure L1;
    var V: Integer;
      procedure L2;
        procedure L3;
          procedure L4;
          begin V := 9 end;
        begin L4() end;
      begin L3() end;
    begin V := 0; L2(); WriteLn(V) end;
    begin L1() end.
    ''', '9' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_NestedProc_MethodMangle_NoCollision;
begin
  { TFoo.DoIt and TBar.DoIt each contain a nested Inner.  If the nested symbols
    were not class-qualified they would collide at link (one Inner would win and
    both DoIt calls would print the same thing).  Expect foo then bar. }
  AssertRunsOnAll('''
    program Prg;
    type
      TFoo = class procedure DoIt; end;
      TBar = class procedure DoIt; end;
    procedure TFoo.DoIt;
      procedure Inner;
      begin WriteLn('foo') end;
    begin Inner() end;
    procedure TBar.DoIt;
      procedure Inner;
      begin WriteLn('bar') end;
    begin Inner() end;
    var f: TFoo; b: TBar;
    begin
      f := TFoo.Create(); b := TBar.Create();
      f.DoIt(); b.DoIt();
      f.Free(); b.Free()
    end.
    ''', 'foo' + LE + 'bar' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_NestedProc_MultiLevelMangle;
begin
  { A 3-level standalone nesting must mangle the innermost as the full chain so
    calls resolve correctly and no cross-scope collision occurs.  Expect deep. }
  AssertRunsOnAll('''
    program Prg;
    procedure L1;
      procedure L2;
        procedure L3;
        begin WriteLn('deep') end;
      begin L3() end;
    begin L2() end;
    begin L1() end.
    ''', 'deep' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_NestedProc_CaptureClassBase_ReadWriteCall;
begin
  { A method takes a class parameter; a nested proc reads a field of it, writes
    a field of it, and calls a method on it — all through the captured base.
    Expect the written value then the method's output. }
  AssertRunsOnAll('''
    program Prg;
    type
      TThing = class FName: string; FN: Integer; procedure Show; end;
      TProc = class procedure Run(AThing: TThing); end;
    procedure TThing.Show; begin WriteLn(FName) end;
    procedure TProc.Run(AThing: TThing);
      procedure Inner;
      begin
        AThing.FN := 7;
        WriteLn(AThing.FN);
        AThing.Show()
      end;
    begin Inner() end;
    var P: TProc; T: TThing;
    begin
      T := TThing.Create(); T.FName := 'hi';
      P := TProc.Create(); P.Run(T);
      P.Free(); T.Free()
    end.
    ''', '7' + LE + 'hi' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_NestedProc_CaptureVarParamClass_FieldWrite;
begin
  { A nested proc writes a field of a captured VAR-PARAM class base.  The base
    slot holds the caller's address, so the store must deref twice through
    _cap_ to reach the instance — a single deref (the review-found bug) would
    corrupt memory and lose the write.  Expect 42 then 'set'. }
  AssertRunsOnAll('''
    program Prg;
    type TThing = class FName: string; FN: Integer; end;
    procedure Run(var T: TThing);
      procedure Inner;
      begin T.FN := 42; T.FName := 'set' end;
    begin Inner() end;
    var Tv: TThing;
    begin
      Tv := TThing.Create();
      Run(Tv);
      WriteLn(Tv.FN);
      WriteLn(Tv.FName);
      Tv.Free()
    end.
    ''', '42' + LE + 'set' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_NestedProc_CaptureRecordBase;
begin
  { A nested proc reads a field of a captured RECORD var-param and of a
    captured value record local.  Expect both values. }
  AssertRunsOnAll('''
    program Prg;
    type TRec = record X: Integer; end;
    procedure UseVarParam(var R: TRec);
      procedure Inner;
      begin WriteLn(R.X) end;
    begin Inner() end;
    procedure UseLocal;
    var L: TRec;
      procedure Inner;
      begin WriteLn(L.X) end;
    begin L.X := 44; Inner() end;
    var Rr: TRec;
    begin
      Rr.X := 33; UseVarParam(Rr);
      UseLocal()
    end.
    ''', '33' + LE + '44' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Builtin_SinCos;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    var R: Integer;
    begin
      R := Round(Sin(0.0));
      WriteLn(IntToStr(R));
      R := Round(Cos(0.0));
      WriteLn(IntToStr(R))
    end.
    ''',
    '0' + LE + '1' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Builtin_SqrtDouble;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    var R: Integer;
    begin
      R := Round(Sqrt(4.0));
      WriteLn(IntToStr(R))
    end.
    ''',
    '2' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_DoublePtrWrite;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    var D: Double; PD: ^Double;
    begin
      D := 0.0;
      PD := @D;
      PD^ := 3.14;
      WriteLn(D)
    end.
    ''',
    '3.14' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_SinglePtrWrite_NoAdjacentClobber;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    var A: Single; B: Single; PA: ^Single;
    begin
      A := 0.0;
      B := 9.5;
      PA := @A;
      PA^ := 1.25;
      WriteLn(B)
    end.
    ''',
    '9.5' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IncDec_RecordField;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    type TRec = record X: Integer; Y: Integer; end;
    var R: TRec;
    begin
      R.X := 10;
      R.Y := 100;
      Inc(R.X);
      Inc(R.Y, 5);
      Dec(R.X, 3);
      WriteLn(R.X);
      WriteLn(R.Y)
    end.
    ''',
    '8' + LE + '105' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IncDec_PtrDeref;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    var N: Integer;
    var P: ^Integer;
    begin
      N := 20;
      P := @N;
      Inc(P^);
      Inc(P^, 4);
      WriteLn(N)
    end.
    ''',
    '25' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_TypeCast_PointerClass;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    var N: Integer; P: Pointer;
    begin
      N := 42;
      P := Pointer(N);
      WriteLn(Integer(P))
    end.
    ''',
    '42' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_PropertyRead_Simple;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    type TBox = class
      FVal: Integer;
      constructor Create(V: Integer);
      function GetVal: Integer;
      property Val: Integer read GetVal;
    end;
    constructor TBox.Create(V: Integer);
    begin FVal := V end;
    function TBox.GetVal: Integer;
    begin Result := FVal end;
    var B: TBox;
    begin
      B := TBox.Create(99);
      WriteLn(B.Val);
      B.Free()
    end.
    ''',
    '99' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_PropertyRead_Indexed;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    type TArr = class
      FA: Integer; FB: Integer;
      constructor Create;
      function GetItem(I: Integer): Integer;
      property Items[I: Integer]: Integer read GetItem;
    end;
    constructor TArr.Create;
    begin FA := 10; FB := 30 end;
    function TArr.GetItem(I: Integer): Integer;
    begin if I = 0 then Result := FA else Result := FB end;
    var A: TArr;
    begin
      A := TArr.Create;
      WriteLn(A.Items[0]);
      WriteLn(A.Items[1]);
      A.Free()
    end.
    ''',
    '10' + LE + '30' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_PropertyWrite_Simple;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    type TBox = class
      FVal: Integer;
      procedure SetVal(V: Integer);
      function GetVal: Integer;
      property Val: Integer read GetVal write SetVal;
    end;
    procedure TBox.SetVal(V: Integer);
    begin FVal := V end;
    function TBox.GetVal: Integer;
    begin Result := FVal end;
    var B: TBox;
    begin
      B := TBox.Create;
      B.Val := 42;
      WriteLn(B.Val);
      B.Free()
    end.
    ''',
    '42' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_PropertyWrite_Indexed;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    type TArr = class
      FA: Integer; FB: Integer;
      procedure SetItem(I: Integer; V: Integer);
      function GetItem(I: Integer): Integer;
      property Items[I: Integer]: Integer read GetItem write SetItem;
    end;
    procedure TArr.SetItem(I: Integer; V: Integer);
    begin if I = 0 then FA := V else FB := V end;
    function TArr.GetItem(I: Integer): Integer;
    begin if I = 0 then Result := FA else Result := FB end;
    var A: TArr;
    begin
      A := TArr.Create;
      A.Items[0] := 10;
      A.Items[1] := 30;
      WriteLn(A.Items[0]);
      WriteLn(A.Items[1]);
      A.Free()
    end.
    ''',
    '10' + LE + '30' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ClassName;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    type TFoo = class end;
    var F: TFoo;
    begin
      F := TFoo.Create;
      WriteLn(F.ClassName);
      F.Free()
    end.
    ''',
    'TFoo' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_MethodCall_ManyArgs;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    type TCalc = class
      function Sum6(A: Integer; B: Integer; C: Integer;
        D: Integer; E: Integer; F: Integer): Integer;
    end;
    function TCalc.Sum6(A: Integer; B: Integer; C: Integer;
      D: Integer; E: Integer; F: Integer): Integer;
    begin Result := A + B + C + D + E + F end;
    var Obj: TCalc;
    begin
      Obj := TCalc.Create;
      WriteLn(Obj.Sum6(1, 2, 3, 4, 5, 6));
      Obj.Free()
    end.
    ''',
    '21' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ImplicitSelf_ClassField;
begin
  AssertRunsOnAll('''
    program T;
    type
      TInner = class FVal: Integer; end;
      TOuter = class
        FInner: TInner;
        function GetVal(): Integer;
      end;
    function TOuter.GetVal(): Integer;
    begin Result := FInner.FVal end;
    var I: TInner; O: TOuter;
    begin
      I := TInner.Create;
      I.FVal := 42;
      O := TOuter.Create;
      O.FInner := I;
      WriteLn(O.GetVal());
      O.Free();
      I.Free()
    end.
    ''',
    '42' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ImplicitSelf_PropertyGetter;
begin
  AssertRunsOnAll('''
    program T;
    type
      TMyObj = class
      private
        FVal: Integer;
        function GetVal: Integer;
      public
        property Val: Integer read GetVal;
        procedure Show;
      end;
    function TMyObj.GetVal: Integer;
    begin Result := FVal end;
    procedure TMyObj.Show;
    begin WriteLn(Val) end;
    var O: TMyObj;
    begin
      O := TMyObj.Create;
      O.FVal := 99;
      O.Show();
      O.Free()
    end.
    ''',
    '99' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ConstArray_StringElements;
begin
  AssertRunsOnAll('''
    program T;
    const
      Regs: array[0..2] of string = ('ax', 'bx', 'cx');
    var I: Integer;
    begin
      for I := 0 to 2 do
        WriteLn(Regs[I])
    end.
    ''',
    'ax' + LE + 'bx' + LE + 'cx' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_VirtualDispatch_Expr;
begin
  AssertRunsOnAll('''
    program T;
    type
      TBase = class
        function GetVal(): Integer; virtual; abstract;
      end;
      TChild = class(TBase)
        function GetVal(): Integer; override;
      end;
    function TChild.GetVal(): Integer;
    begin Result := 42 end;
    var B: TBase;
    begin
      B := TChild.Create;
      WriteLn(B.GetVal());
      B.Free()
    end.
    ''',
    '42' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_StringEquality;
begin
  AssertRunsOnAll('''
    program T;
    function MakeStr(const S: string): string; begin Result := S end;
    var A, B: string;
    begin
      A := MakeStr('hello');
      B := 'hello';
      if A = B then WriteLn('eq') else WriteLn('ne');
      if A <> 'world' then WriteLn('diff') else WriteLn('same')
    end.
    ''',
    'eq' + LE + 'diff' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_OutParam_String;
begin
  AssertRunsOnAll('''
    program T;
    procedure Fill(out S: string); begin S := 'filled' end;
    var X: string;
    begin
      X := 'old';
      Fill(X);
      WriteLn(X)
    end.
    ''',
    'filled' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_VarParam_String;
begin
  AssertRunsOnAll('''
    program T;
    procedure Append(var S: string); begin S := S + '_tail' end;
    var X: string;
    begin
      X := 'head';
      Append(X);
      WriteLn(X)
    end.
    ''',
    'head_tail' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_Constructor_CallArg;
begin
  AssertRunsOnAll('''
    program T;
    type
      THolder = class
        FVal: string;
        constructor Create(S: string);
      end;
    constructor THolder.Create(S: string); begin FVal := S end;
    function MakeStr: string; begin Result := 'hello' end;
    var H: THolder;
    begin
      H := THolder.Create(MakeStr());
      WriteLn(H.FVal);
      H.Free()
    end.
    ''',
    'hello' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_MethodSretReturn;
begin
  AssertRunsOnAll('''
    program T;
    type
      TPoint = record X: Integer; Y: Integer; Z: Integer; end;
      TMaker = class
        function Make(AX, AY, AZ: Integer): TPoint;
      end;
    function TMaker.Make(AX, AY, AZ: Integer): TPoint;
    begin Result.X := AX; Result.Y := AY; Result.Z := AZ end;
    var M: TMaker; P: TPoint;
    begin
      M := TMaker.Create();
      P := M.Make(10, 20, 30);
      WriteLn(P.X);
      WriteLn(P.Y);
      WriteLn(P.Z);
      M.Free()
    end.
    ''',
    '10' + LE + '20' + LE + '30' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_FieldSretReturn;
begin
  AssertRunsOnAll('''
    program T;
    type
      TRec = record A: Integer; S: string; B: Integer; end;
      TGen = class
        function Make(V: Integer; N: string): TRec;
      end;
      THold = class
        FR: TRec;
        FG: TGen;
        constructor Create(AG: TGen);
      end;
    function TGen.Make(V: Integer; N: string): TRec;
    begin Result.A := V; Result.S := N; Result.B := V * 2 end;
    constructor THold.Create(AG: TGen);
    begin inherited Create(); FG := AG; FR := FG.Make(5, 'hi') end;
    var G: TGen; H: THold;
    begin
      G := TGen.Create();
      H := THold.Create(G);
      WriteLn(H.FR.A);
      WriteLn(H.FR.S);
      WriteLn(H.FR.B);
      H.Free(); G.Free()
    end.
    ''',
    '5' + LE + 'hi' + LE + '10' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ImplicitSelfMethodCall;
begin
  AssertRunsOnAll('''
    program T;
    type
      TCalc = class
        FVal: Integer;
        procedure Step;
        function Double: Integer;
        procedure Run;
      end;
    procedure TCalc.Step;
    begin FVal := FVal + 10 end;
    function TCalc.Double: Integer;
    begin Result := FVal * 2 end;
    procedure TCalc.Run;
    begin
      FVal := 5;
      Step();
      WriteLn(FVal);
      WriteLn(Double())
    end;
    var C: TCalc;
    begin
      C := TCalc.Create();
      C.Run();
      C.Free()
    end.
    ''',
    '15' + LE + '30' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_RecordFieldCopy;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program test_rec_field_copy;
    type
      TToken = record Kind: Integer; Value: string; Line: Integer; Col: Integer; end;
      TParser = class
      private FA: TToken; FB: TToken; FC: TToken;
      public
        procedure Setup;
        procedure Advance;
      end;
    procedure TParser.Setup;
    begin
      FA.Kind := 1; FA.Value := 'first'; FA.Line := 10; FA.Col := 20;
      FB.Kind := 2; FB.Value := 'second'; FB.Line := 30; FB.Col := 40;
      FC.Kind := 3; FC.Value := 'third'; FC.Line := 50; FC.Col := 60
    end;
    procedure TParser.Advance;
    begin FA := FB; FB := FC end;
    var P: TParser;
    begin
      P := TParser.Create();
      P.Setup();
      P.Advance();
      WriteLn(P.FA.Kind, ':', P.FA.Value, ':', P.FA.Line, ':', P.FA.Col);
      WriteLn(P.FB.Kind, ':', P.FB.Value, ':', P.FB.Line, ':', P.FB.Col);
      P.Free()
    end.
    ''',
    '2:second:30:40' + LE + '3:third:50:60' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_SretFieldARC;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program test_sret_field_arc;
    type
      TRec = record Kind: Integer; Value: string; end;
      TFactory = class
      public
        function Make(AKind: Integer; const AVal: string): TRec;
      end;
    function TFactory.Make(AKind: Integer; const AVal: string): TRec;
    begin Result.Kind := AKind; Result.Value := AVal end;
    var
      F: TFactory;
      R: TRec;
    begin
      F := TFactory.Create();
      R := F.Make(42, 'hello');
      WriteLn(R.Kind, ':', R.Value);
      R := F.Make(99, 'world');
      WriteLn(R.Kind, ':', R.Value);
      F.Free()
    end.
    ''',
    '42:hello' + LE + '99:world' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_VarParam_MethodCall;
begin
  Self.AssertRunsOnAll('''
    program TestVarParamMethodCall;
    type
      TBox = class
      public
        FValue: Integer;
        procedure SetVal(AV: Integer);
        function GetVal(): Integer;
      end;
    procedure TBox.SetVal(AV: Integer);
    begin FValue := AV end;
    function TBox.GetVal(): Integer;
    begin Result := FValue end;
    procedure Bump(var B: TBox);
    begin B.SetVal(B.GetVal() + 10) end;
    var
      X: TBox;
    begin
      X := TBox.Create();
      X.SetVal(5);
      Bump(X);
      WriteLn(X.GetVal());
      X.Free()
    end.
    ''',
    '15' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_StringConst;
begin
  Self.AssertRunsOnAll('''
    program TestStringConst;
    const
      NL = #10;
      GREETING = 'hello';
    var
      S: string;
    begin
      S := GREETING;
      Write(S);
      Write(NL);
      WriteLn('done')
    end.
    ''',
    'hello' + LE + 'done' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_SretForward;
begin
  Self.AssertRunsOnAll('''
    program TestSretFwd;
    type
      TPair = record A: Integer; B: Integer; end;
    function MakePair(X, Y: Integer): TPair;
    begin Result.A := X; Result.B := Y; end;
    function DoubledPair(X, Y: Integer): TPair;
    begin Result := MakePair(X * 2, Y * 2); end;
    var
      P: TPair;
    begin
      P := DoubledPair(5, 7);
      WriteLn(P.A);
      WriteLn(P.B);
    end.
    ''',
    '10' + LE + '14' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_ForLoop_RecursiveBody;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  Self.AssertRunsOnAll('''
    program TestForRec;
    procedure Walk(Depth: Integer);
    var I: Integer;
    begin
      if Depth <= 0 then begin WriteLn('leaf'); Exit; end;
      for I := 0 to Depth - 1 do
        Walk(I);
    end;
    begin
      Walk(3);
    end.
    ''',
    'leaf' + LE + 'leaf' + LE + 'leaf' + LE + 'leaf' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_MethodCall_OpenArray;
begin
  Self.AssertRunsOnAll('''
    program TestOpenArray;
    function Sum(const A: array of Integer): Integer;
    var I: Integer;
    begin
      Result := 0;
      for I := 0 to High(A) do
        Result := Result + A[I];
    end;
    begin
      WriteLn(Sum([10, 20, 30]));
    end.
    ''',
    '60' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IntfFieldAsArg;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcIntfFieldAsArg, '77' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IntfFieldNilAssign;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcIntfFieldNilAssign, '99' + LE + 'cleared' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_DynArrayElemArc_String;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDynArrayElemArcString,
    'first' + LE + 'second' + LE + 'replaced' + LE + 'second' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IntfFuncReturn;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcIntfFuncReturn, '42' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IntfFromClassMethod;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcIntfFromClassMethod,
    '1' + LE + '2' + LE + '103' + LE + '5' + LE + '203' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_RecReturnVirtualOverride;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    type
      TPair = record A, B: Int64; end;
      TBase = class
        function Get(): TPair; virtual;
      end;
      TSub = class(TBase)
        function Get(): TPair; override;
      end;
    function TBase.Get(): TPair;
    begin
      Result.A := 1;
      Result.B := 2
    end;
    function TSub.Get(): TPair;
    begin
      Result.A := 10;
      Result.B := 20
    end;
    var
      B: TBase;
      P: TPair;
    begin
      B := TSub.Create();
      P := B.Get();
      WriteLn(P.A, ' ', P.B)
    end.
    ''',
    '10 20' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IntfFieldFromFunc;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcIntfFieldFromFunc, '10' + LE + '20' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_IntfVarParamAndChainedReceiver;
begin
  { var/out interface parameter (the callee stores both halves through the
    caller's pair address, releasing the old obj), a field-chain receiver
    (O.H.FG.Greet), a discarded interface-returning itab call, and an
    interface field filled through a var argument.  The destructor lines pin
    the ARC: each instance dies exactly once, when its last ref goes. }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    type
      IGreeter = interface
        function Greet(N: Integer): Integer;
        function Again: IGreeter;
      end;
      TGreeter = class(IGreeter)
      public
        FBase: Integer;
        constructor Create(ABase: Integer);
        destructor Destroy; override;
        function Greet(N: Integer): Integer;
        function Again: IGreeter;
      end;
      THolder = class
      public
        FG: IGreeter;
      end;
      TOuter = class
      public
        H: THolder;
      end;
    constructor TGreeter.Create(ABase: Integer);
    begin
      FBase := ABase;
    end;
    destructor TGreeter.Destroy;
    begin
      WriteLn('destroyed ', FBase);
      inherited Destroy();
    end;
    function TGreeter.Greet(N: Integer): Integer;
    begin
      Result := FBase + N;
    end;
    function TGreeter.Again: IGreeter;
    begin
      Result := Self;
    end;
    procedure Fill(var G: IGreeter; B: Integer);
    begin
      G := TGreeter.Create(B);
    end;
    procedure Run;
    var
      L: IGreeter;
      O: TOuter;
    begin
      Fill(L, 7);
      WriteLn(L.Greet(1));
      Fill(L, 8);
      WriteLn(L.Greet(1));
      O := TOuter.Create();
      O.H := THolder.Create();
      Fill(O.H.FG, 30);
      WriteLn(O.H.FG.Greet(3));
      O.H.FG.Again();
      O.H.FG := L;
      WriteLn(O.H.FG.Greet(4));
      L := nil;
      WriteLn('end run');
    end;
    begin
      Run();
      WriteLn('done');
    end.
    ''',
    '8' + LE + 'destroyed 7' + LE + '9' + LE + '33' + LE + 'destroyed 30' + LE +
    '12' + LE + 'end run' + LE + 'destroyed 8' + LE + 'done' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_VarOpenArray_ElemReadWrite;
begin
  { a var open-array parameter is the same (data, high) pair as a value one
    -- the slot holds the element-0 pointer, NOT the caller variable's
    address.  Writing A[I] used to stop as NotYet on arm64, and reading
    A[I] dereferenced the pointer once too often (silently wrong bytes). }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    procedure Fill(var A: array of Byte);
    var
      I: Integer;
    begin
      for I := 0 to High(A) do
        A[I] := I * 3;
      WriteLn(A[2]);
    end;
    procedure Show(const A: array of Byte);
    begin
      WriteLn(A[0], ' ', A[1], ' ', A[2], ' ', A[3]);
    end;
    var
      M: array[0..3] of Byte;
    begin
      Fill(M);
      Show(M);
    end.
    ''',
    '6' + LE + '0 3 6 9' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_WeakInterfaceVar;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcWeakInterfaceVar,
    '77' + LE + 'destroyed' + LE + 'done' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_SretTempFieldRelease;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcSretTempFieldRelease, 'hello' + LE + 'done' + LE, 0);
end;

{ ------------------------------------------------------------------ }
{ Record-by-value returns — all SysV ABI register-return shapes      }
{ ------------------------------------------------------------------ }

procedure TE2ENativeTests.TestRun_Native_RecReturn_RcInt2_TwoInt64;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    type T2 = record A, B: Int64; end;
    function MakeIt(A, B: Int64): T2;
    begin
      Result.A := A;
      Result.B := B
    end;
    var R: T2;
    begin
      R := MakeIt(111111111111, 222222222222);
      WriteLn(R.A, ' ', R.B)
    end.
    ''',
    '111111111111 222222222222' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_RecReturn_RcSSE1_Double;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    type TF = record V: Double; end;
    function MakeIt(V: Double): TF;
    begin
      Result.V := V
    end;
    var R: TF;
    begin
      R := MakeIt(3.5);
      WriteLn(R.V)
    end.
    ''',
    '3.5' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_RecReturn_RcSSE1_Single;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    type TF = record V: Single; end;
    function MakeIt(V: Single): TF;
    begin
      Result.V := V
    end;
    var R: TF;
    begin
      R := MakeIt(2.5);
      WriteLn(R.V)
    end.
    ''',
    '2.5' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_RecReturn_RcSSE2_TwoDouble;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    type T2D = record A, B: Double; end;
    function MakeIt(A, B: Double): T2D;
    begin
      Result.A := A;
      Result.B := B
    end;
    var R: T2D;
    begin
      R := MakeIt(1.5, -2.5);
      WriteLn(R.A);
      WriteLn(R.B)
    end.
    ''',
    '1.5' + LE + '-2.5' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_RecReturn_RcIntSSE;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    type TM = record I: Int64; D: Double; end;
    function MakeIt(I: Int64; D: Double): TM;
    begin
      Result.I := I;
      Result.D := D
    end;
    var R: TM;
    begin
      R := MakeIt(42, 3.5);
      WriteLn(R.I);
      WriteLn(R.D)
    end.
    ''',
    '42' + LE + '3.5' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_RecReturn_RcSSEInt;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    type TM = record D: Double; I: Int64; end;
    function MakeIt(D: Double; I: Int64): TM;
    begin
      Result.D := D;
      Result.I := I
    end;
    var R: TM;
    begin
      R := MakeIt(-1.5, 99);
      WriteLn(R.D);
      WriteLn(R.I)
    end.
    ''',
    '-1.5' + LE + '99' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_RecReturn_Nested_RcInt2;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    type
      TInner = record X, Y: Integer; end;
      TOuter = record A: TInner; B: Integer; end;
    function MakeIt(X, Y, B: Integer): TOuter;
    begin
      Result.A.X := X;
      Result.A.Y := Y;
      Result.B := B
    end;
    var R: TOuter;
    begin
      R := MakeIt(10, 20, 30);
      WriteLn(R.A.X, ' ', R.A.Y, ' ', R.B)
    end.
    ''',
    '10 20 30' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_RecReturn_Method_RcInt1;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    type
      TPoint = record X, Y: Integer; end;
      TFactory = class
        function MakePoint(X, Y: Integer): TPoint;
      end;
    function TFactory.MakePoint(X, Y: Integer): TPoint;
    begin
      Result.X := X;
      Result.Y := Y
    end;
    var
      F: TFactory;
      Pt: TPoint;
    begin
      F := TFactory.Create();
      Pt := F.MakePoint(5, 9);
      WriteLn(Pt.X, ' ', Pt.Y);
      F.Free()
    end.
    ''',
    '5 9' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_RecReturn_ManagedStaysSret;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program Prg;
    type TS = record S: string; end;
    function MakeIt(S: string): TS;
    begin
      Result.S := S
    end;
    var R: TS;
    begin
      R := MakeIt('hello');
      WriteLn(R.S)
    end.
    ''',
    'hello' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_RecordSret_OutParam;
begin
  AssertRunsOnAll('''
    program Prg;
    type
      TOS = (osLinux, osFreeBSD, osWindows);
      TCPU = (cpuX86_64, cpuI386, cpuArm64);
      TTarget = record
        OS: TOS;
        CPU: TCPU;
      end;
    procedure MakeTarget(AOS: TOS; ACPU: TCPU; out ATarget: TTarget);
    begin
      ATarget.OS := AOS;
      ATarget.CPU := ACPU
    end;
    function HostTarget: TTarget;
    begin
      MakeTarget(osLinux, cpuX86_64, Result)
    end;
    function ParseArgs(out S1: string; out S2: string; out B1: Boolean;
                       out B2: Boolean; out B3: Boolean;
                       out Target: TTarget): Boolean;
    begin
      Result := True;
      S1 := '';
      S2 := '';
      B1 := False;
      B2 := False;
      B3 := False;
      Target := HostTarget()
    end;
    var
      S1, S2: string;
      B1, B2, B3: Boolean;
      T: TTarget;
    begin
      ParseArgs(S1, S2, B1, B2, B3, T);
      if (T.OS = osLinux) and (T.CPU = cpuX86_64) then
        WriteLn('linux-x86_64')
      else
        WriteLn('unknown-unknown')
    end.
    ''',
    'linux-x86_64' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_Native_StaticArray_ComputedIndex;
const Src = '''
    program Prg;
    const
      Names: array[0..3] of string = ('alpha', 'beta', 'gamma', 'delta');
    var I: Integer;
    begin
      for I := 0 to 2 do
        WriteLn(Names[I + 1])
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'beta' + LE + 'gamma' + LE + 'delta' + LE, 0)
end;

procedure TE2ENativeTests.TestRun_Native_Metaclass_BareClassRef;
const Src = '''
    program Prg;
    type
      TFoo = class
      public
        constructor Create;
        procedure DoIt; virtual;
      end;
      TBar = class(TFoo)
      public
        procedure DoIt; override;
      end;
      TFooClass = class of TFoo;
    var GCount: Integer;
    { The ctor body must do real work: a trivial body leaves the allocated
      instance untouched in %rax and masks a missing save/restore around
      the ClassCreate ctor call. }
    constructor TFoo.Create;
    begin
      GCount := GCount + Length(IntToStr(21))
    end;
    procedure TFoo.DoIt;
    begin
      WriteLn('foo')
    end;
    procedure TBar.DoIt;
    begin
      WriteLn('bar')
    end;
    procedure Run(AClass: TFooClass);
    var F: TFoo;
    begin
      F := ClassCreate(AClass);
      F.DoIt();
      F.Free()
    end;
    var C: TFooClass;
    begin
      C := TFoo;
      Run(C);
      Run(TBar);
      if C = TFoo then
        WriteLn('same')
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'foo' + LE + 'bar' + LE + 'same' + LE, 0)
end;

procedure TE2ENativeTests.TestRun_Native_MultiUnit_Metaclass;
var
  UnitSrc, ProgSrc, NOut, QOut: string;
  NCode, QCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { Mirrors the RegisterTest pattern in blaise.testing: the unit holds a
    registry of metaclass values; the program registers its class from the
    _init path and the unit constructs it later via ClassCreate. }
  UnitSrc := '''
    unit mu_mc;
    interface
    type
      TWidget = class
      public
        FName: string;
        constructor Create(AName: string);
        function Describe: string; virtual;
      end;
      TWidgetClass = class of TWidget;
    procedure RegisterWidget(AClass: TWidgetClass);
    function MakeRegistered(AName: string): TWidget;
    implementation
    var GClass: TWidgetClass;
    constructor TWidget.Create(AName: string);
    begin
      FName := AName + '!'
    end;
    function TWidget.Describe: string;
    begin
      Result := 'widget:' + FName
    end;
    procedure RegisterWidget(AClass: TWidgetClass);
    begin
      GClass := AClass
    end;
    function MakeRegistered(AName: string): TWidget;
    begin
      Result := ClassCreate(GClass, AName)
    end;
    end.
    ''';
  ProgSrc := '''
    program Prg;
    uses mu_mc;
    type
      TGadget = class(TWidget)
      public
        function Describe: string; override;
      end;
    function TGadget.Describe: string;
    begin
      Result := 'gadget:' + FName
    end;
    var W: TWidget;
    begin
      RegisterWidget(TGadget);
      W := MakeRegistered('g');
      WriteLn(W.Describe());
      W.Free();
      RegisterWidget(TWidget);
      W := MakeRegistered('w');
      WriteLn(W.Describe());
      W.Free();
    end.
    ''';
  AssertTrue('native compile+run',
    CompileAndRunWithUnitNative('mu_mc', UnitSrc, ProgSrc, NOut, NCode));
  AssertTrue('qbe compile+run',
    CompileAndRunWithUnit('mu_mc', UnitSrc, ProgSrc, QOut, QCode));
  AssertEquals('stdout parity', QOut, NOut);
  AssertEquals('exit parity', QCode, NCode);
  AssertEquals('value', 'gadget:g!' + LE + 'widget:w!' + LE, NOut);
end;

procedure TE2ENativeTests.TestRun_Native_OpenArrayLiteral_AfterOtherArgs;
const Src = '''
    program Prg;
    procedure Inner(const AArgs: array of string);
    var I: Integer;
    begin
      for I := 0 to High(AArgs) do
        WriteLn('arg:', AArgs[I])
    end;
    procedure Outer(const AExe: string; const AArgs: array of string;
                    ATail: Integer);
    begin
      WriteLn('exe:', AExe);
      Inner(AArgs);
      WriteLn('tail:', ATail)
    end;
    function MakeName(N: Integer): string;
    begin
      Result := 'file' + IntToStr(N)
    end;
    begin
      Outer('gcc', ['-o', MakeName(1), MakeName(2)], 7)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'exe:gcc' + LE + 'arg:-o' + LE + 'arg:file1' + LE + 'arg:file2' + LE +
    'tail:7' + LE, 0)
end;

{ ===================================================================== }
{ Zero-initialisation tests                                             }
{ Dirty() fills the stack frame with 0xDEADBEEF garbage before the     }
{ real procedure runs, so any zero we observe must come from the        }
{ prologue zero-init, not from lucky leftover zeros.                    }
{ ===================================================================== }

const
  { Dirty helper shared across all zero-init tests. }
  SrcZeroInitDirtyPrologue =
    '''
    procedure Dirty();
    var
      A: array[0..127] of Int64;
      I: Integer;
    begin
      for I := 0 to 127 do
        A[I] := -81985529216486896
    end;
    ''';

  SrcZeroInit_ScalarIntegers =
    'program Prg;' + LE +
    SrcZeroInitDirtyPrologue +
    '''
    procedure Check();
    var
      A: Integer;
      B: Int64;
      C: Byte;
      D: Word;
      E: SmallInt;
      F: UInt32;
      G: UInt64;
    begin
      WriteLn(A);
      WriteLn(B);
      WriteLn(C);
      WriteLn(D);
      WriteLn(E);
      WriteLn(F);
      WriteLn(G)
    end;
    begin
      Dirty();
      Check()
    end.
    ''';

  SrcZeroInit_FloatLocals =
    'program Prg;' + LE +
    SrcZeroInitDirtyPrologue +
    '''
    procedure Check();
    var
      D: Double;
      S: Single;
    begin
      if D = 0.0 then WriteLn('d_ok');
      if S = 0.0 then WriteLn('s_ok')
    end;
    begin
      Dirty();
      Check()
    end.
    ''';

  SrcZeroInit_BooleanAndChar =
    'program Prg;' + LE +
    SrcZeroInitDirtyPrologue +
    '''
    procedure Check();
    var
      B: Boolean;
      C: Byte;
    begin
      if not B then WriteLn('b_ok');
      if C = 0 then WriteLn('c_ok')
    end;
    begin
      Dirty();
      Check()
    end.
    ''';

  SrcZeroInit_PointerLocals =
    'program Prg;' + LE +
    SrcZeroInitDirtyPrologue +
    '''
    procedure Check();
    var
      P: Pointer;
    begin
      if not Assigned(P) then WriteLn('ok')
    end;
    begin
      Dirty();
      Check()
    end.
    ''';

  SrcZeroInit_EnumLocal =
    'program Prg;' + LE +
    SrcZeroInitDirtyPrologue +
    '''
    type
      TColor = (clRed, clGreen, clBlue);
    procedure Check();
    var
      C: TColor;
    begin
      if Ord(C) = 0 then WriteLn('ok')
    end;
    begin
      Dirty();
      Check()
    end.
    ''';

  SrcZeroInit_SetLocal =
    'program Prg;' + LE +
    SrcZeroInitDirtyPrologue +
    '''
    type
      TFlag = (fA, fB, fC);
      TFlags = set of TFlag;
    procedure Check();
    var
      S: TFlags;
    begin
      if S = [] then WriteLn('empty') else WriteLn('not-empty')
    end;
    begin
      Dirty();
      Check()
    end.
    ''';

  SrcZeroInit_RecordWithMixedFields =
    'program Prg;' + LE +
    SrcZeroInitDirtyPrologue +
    '''
    type
      TPoint = record
        X: Integer;
        Y: Integer;
        Z: Double;
      end;
    procedure Check();
    var
      P: TPoint;
    begin
      WriteLn(P.X);
      WriteLn(P.Y);
      if P.Z = 0.0 then WriteLn('z_ok')
    end;
    begin
      Dirty();
      Check()
    end.
    ''';

  SrcZeroInit_StaticArray =
    'program Prg;' + LE +
    SrcZeroInitDirtyPrologue +
    '''
    procedure Check();
    var
      A: array[0..4] of Integer;
      I: Integer;
    begin
      for I := 0 to 4 do
        WriteLn(A[I])
    end;
    begin
      Dirty();
      Check()
    end.
    ''';

  SrcZeroInit_ThreadVar =
    '''
    program Prg;
    threadvar
      T: Integer;
    begin
      WriteLn(T)
    end.
    ''';

  SrcZeroInit_GlobalVars =
    '''
    program Prg;
    var
      I: Integer;
      D: Double;
      B: Boolean;
    begin
      WriteLn(I);
      if D = 0.0 then WriteLn('d_ok');
      if not B then WriteLn('b_ok')
    end.
    ''';

procedure TE2ENativeTests.TestRun_ZeroInit_ScalarIntegers;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcZeroInit_ScalarIntegers,
    '0' + LE + '0' + LE + '0' + LE + '0' + LE + '0' + LE + '0' + LE + '0' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_ZeroInit_FloatLocals;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcZeroInit_FloatLocals, 'd_ok' + LE + 's_ok' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_ZeroInit_BooleanAndChar;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcZeroInit_BooleanAndChar, 'b_ok' + LE + 'c_ok' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_ZeroInit_PointerLocals;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcZeroInit_PointerLocals, 'ok' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_ZeroInit_EnumLocal;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcZeroInit_EnumLocal, 'ok' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_ZeroInit_SetLocal;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcZeroInit_SetLocal, 'empty' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_ZeroInit_RecordWithMixedFields;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcZeroInit_RecordWithMixedFields,
    '0' + LE + '0' + LE + 'z_ok' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_ZeroInit_StaticArray;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcZeroInit_StaticArray,
    '0' + LE + '0' + LE + '0' + LE + '0' + LE + '0' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_ZeroInit_ThreadVar;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcZeroInit_ThreadVar, '0' + LE, 0);
end;

procedure TE2ENativeTests.TestRun_ZeroInit_GlobalVars;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcZeroInit_GlobalVars, '0' + LE + 'd_ok' + LE + 'b_ok' + LE, 0);
end;

initialization
  RegisterTest(TE2ENativeTests);

end.
