{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit cp.test.e2e.misc;

{ E2E tests for miscellaneous features: boolean ops, WriteLn, constants,
  procedural types, default parameters, var/const params, type casts,
  sets, and for..in. }

interface

uses
  blaise.testing, cp.test.e2e.base;

type
  [Threaded]
  TE2EMiscTests = class(TE2ETestCase)
  protected
    procedure SetUp; override;
  published
    procedure TestRun_IndirectFuncCallExpr_Shapes;
    procedure TestRun_ProcTypes_IndirectCallShapes;
    procedure TestRun_SelfHostingRTLServices;
    procedure TestRun_HighLow_OrdinalBounds;
    procedure TestRun_ChainedFields_ReadThroughEveryLevel;
    procedure TestRun_DefaultArgs_Materialised;
    procedure TestRun_IntToStr_FollowsSignedness;
    procedure TestRun_PChar_StringRoundTrip;
    procedure TestRun_File_BinaryRoundTrip;
    procedure TestRun_NestedRoutines_ScopeAndCapture;
    procedure TestRun_Routines_CallsAndResults;
    procedure TestRun_Write_MultiArg_NewlineRules;
    procedure TestRun_BooleanOps_ShortCircuitAndNot;
    procedure TestRun_WriteLn_UInt64_HighBit_Unsigned;
    procedure TestRun_FloatArg_ConvertsToParamType;
    { Boolean, WriteLn, break/exit }
    procedure TestRun_BooleanOps_AllExpressions;
    procedure TestRun_WriteLn_BoolVar_PrintsTrueOrFalse;
    procedure TestRun_WriteLn_BoolExpr_PrintsTrueOrFalse;
    procedure TestRun_MultiArgWriteLn_PrintsAllArgs;
    procedure TestRun_ForBreak_StopsAtFiveHalt;
    procedure TestRun_ExitFromFunction_ReturnsImmediately;
    procedure TestRun_ChainedRecordField_LoadsInner;
    procedure TestRun_RecordChainArrayAssign;

    { Constants }
    procedure TestRun_Const_IntegerConst;
    procedure TestRun_Const_StringConst;
    procedure TestRun_Const_NegativeConst;
    procedure TestRun_Const_CompileTimeExpression;
    procedure TestRun_Const_LocalArrayInFunction;

    { Procedural types }
    procedure TestRun_ProcType_CallViaVariable;
    { Float args through a procedural VARIABLE: native's indirect-call arg
      staging was integer-only — every arg went through the integer
      registers, so even ONE Double arg read garbage from xmm and 9 Doubles
      segfaulted (BUG-20260722-native-procvar-float-args). }
    procedure TestRun_ProcType_FloatArgs_ViaVariable;
    procedure TestRun_ProcType_MixedIntFloat_Overflow_ViaVariable;
    procedure TestRun_ProcType_HoistedStrWithOverflow_ViaVariable;
    procedure TestRun_ProcType_OfObject_Dispatch;
    { Procedural-typed class field called through a receiver (Self.FFn(...)). }
    procedure TestRun_ProcFieldCall_ReturnValue;
    procedure TestRun_ProcFieldCall_Statement;
    procedure TestRun_ProcFieldCall_OutParam;
    procedure TestRun_ProcFieldCall_MultiArg;
    { Method-pointer (of object) field: assign @Obj.Method into a field, then
      dispatch through it — exercises the 16-byte (Code, Data) field store. }
    procedure TestRun_MethodPtrField_AssignAndCall;
    { Capturing @Obj.VirtualMethod must bind the receiver's dynamic override,
      not the statically-resolved declared-type method. }
    procedure TestRun_MethodPtrVirtualCapture_Var;
    procedure TestRun_MethodPtrVirtualCapture_Field;
    procedure TestRun_MethodPtrReturn;
    procedure TestRun_MethodPtrReturn_ReadsSelf;
    procedure TestRun_MethodPtrImplicitSelfFieldAssign;
    { Unqualified call to a procedural-typed field via implicit Self (FFn(...)
      with no 'Self.' prefix), as an expression and as a statement. }
    procedure TestRun_ImplicitSelfProcField_Expr;
    procedure TestRun_ImplicitSelfProcField_Stmt;

    { Default parameters }
    procedure TestRun_DefaultParam_OmitLast;
    procedure TestRun_DefaultParam_OmitMultiple;

    { var / const params }
    procedure TestRun_VarParam_SwapIntegers;
    procedure TestRun_VarParam_ModifyString;
    procedure TestRun_ConstParam_CanRead;

    { Type casts }
    procedure TestRun_TypeCast_IntegerByte;
    procedure TestRun_TypeCast_PointerInteger;
    procedure TestRun_WriteUnsigned32_PrintsUnsigned;

    { Set `set of` operation e2e tests moved to cp.test.e2e.sets. }

    { for..in }
    procedure TestRun_ForIn_String_ByteVar_PrintsBytes;
    procedure TestRun_ForIn_String_IntegerVar_PrintsCodePoints;
    procedure TestRun_ForIn_String_IntegerVar_CodePoints_TwoByte;
    procedure TestRun_ForIn_String_IntegerVar_CodePoints_ThreeByte;
    procedure TestRun_ForIn_Array_Integer_PrintsElements;
    procedure TestRun_ForIn_ClassEnumerator_PrintsElements;

    { Nested procedures }
    procedure TestRun_NestedProc_MutatesCapturedVar;
    { Nested proc captures an outer VAR RECORD PARAMETER (read + write through
      the var-param fields).  Previously the nested proc emitted the parameter
      as a global symbol reference and the program failed to link / ran wrong. }
    procedure TestRun_NestedProc_CapturesVarRecordParam;
    { BUG-20260720-capture-varparam: a nested proc capturing an outer VAR/OUT
      SCALAR parameter must reach the pointee through TWO derefs (the _cap_
      pointer, then the var-param slot which holds the caller's address).  The
      write/read arms dropped the extra deref (QBE stored to the wrong slot;
      native routed through a bogus global -> SIGSEGV). }
    procedure TestRun_NestedProc_CapturesVarScalarParam;
    { Same double-deref path at FLOAT width (Double/Single arms had the same bug). }
    procedure TestRun_NestedProc_CapturesVarFloatParam;
    { BUG-20260720-nested-shadow-local: a nested proc's OWN local (or param) that
      shadows an enclosing var must NOT be captured — it has its own slot.  The
      capture collector over-captured shadowed names, so all accesses aliased the
      enclosing var. }
    procedure TestRun_NestedProc_ShadowsEnclosingLocal;
    { Nested proc captures an outer plain LOCAL record (field read + write). }
    procedure TestRun_NestedProc_CapturesLocalRecord;
    { Nested proc captures an outer VAR ARRAY PARAMETER (element read + write).
      The captured var-param array slot is reached through the _cap_ pointer
      with one extra dereference; without it the element address resolved to a
      global symbol and the writes/reads hit the wrong storage. }
    procedure TestRun_NestedProc_CapturesVarArrayParam;
    { Two sibling outer routines each declare a same-named nested function.
      Each call must resolve to the nested function of its own enclosing
      routine.  Previously the call fell through to the global overload index
      (which does not list nested procs) and errored with "Cannot find
      declaration". }
    procedure TestRun_NestedProc_SiblingSameName_ResolvesPerScope;
    { As above but the enclosing routines are METHODS.  Nested-in-method
      functions must be scoped to their method body, not registered globally. }
    procedure TestRun_NestedFunc_InSiblingMethods_ResolvesPerScope;

    { Diamond operator: TFoo<> infers type args from LHS }
    procedure TestRun_Diamond_SingleArg_WorksAtRuntime;
    procedure TestRun_Diamond_TwoArgs_WorksAtRuntime;

    { Address-of array field element }
    procedure TestRun_AddrOf_DynArrayFieldElement;

    { Generic records }
    procedure TestRun_GenericRecord_FieldStore_Prints;
    procedure TestRun_GenericRecord_WithMethod_Prints;
    procedure TestRun_GenericRecord_TwoParams_Prints;
    procedure TestRun_GenericRecord_StringField_Prints;
    procedure TestRun_BitwiseNot_Integer;
    procedure TestRun_BitwiseNot_Byte;
    procedure TestRun_BitwiseNot_Int64;
    procedure TestRun_BitwiseNot_Bitmask;
    procedure TestRun_WriteLn_StdErr_NotOnStdout;

    { function-of-object called through a variable must load Data (Self)
      from the TMethod block and shift user args right. }
    procedure TestRun_FunctionOfObject_IndirectCall;

    { @(class-field dynamic-array)[idx] as a USED pointer must load the
      instance pointer first (loadl), not treat the class variable's slot
      as the instance.  Regression for the QBE codegen bug where
      @Obj.Arr[I] computed `add $Obj, off` instead of
      `loadl $Obj; add .., off`, producing a garbage address that
      segfaulted when dereferenced (e.g. passed to memcpy). }
    procedure TestRun_AddrOfClassFieldDynArrayElem_LoadsInstance;

    { inherited Method() in EXPRESSION position — calling an inherited
      function and using its result (Result := inherited F() + ...). Was a
      parser gap (inherited only worked as a statement). }
    procedure TestRun_InheritedFunctionCall_InExpression;

    { (expr as T).Field := value — a parenthesised cast as an assignment
      TARGET. Was a parser gap (statements could not start with '('). }
    procedure TestRun_ParenCastAsAssignmentTarget;

    { Nested generic type arguments: TList<TList<Integer>>. Was a parser gap
      (type-arg list did not recurse, in both type and constructor position). }
    procedure TestRun_NestedGenericTypeArgs;

    { Named integer subrange type (issue #130 bug1): the type-decl parser had
      no integer-literal subrange case.  A named subrange aliases the narrowest
      standard integer type and carries no range checking. }
    procedure TestRun_Subrange_NamedType;
    procedure TestRun_Subrange_InRecordAndArray;
    procedure TestRun_Subrange_HighLow;
    procedure TestRun_Subrange_OfEnum;
    { GH #182 (follow-up report): a CONST array indexed by an enum-subrange
      type must expect the SUBRANGE's member count (the validator counted the
      full base enum) and index with the subrange's ordinal bounds. }
    procedure TestRun_Subrange_OfEnum_ConstArray;
    { GH #182 (second follow-up): an INLINE enum-subrange array bound —
      array[ptWhitePawn..ptKing] — with bare enum-member names, not a named
      subrange type.  ResolveArrayBound looked members up only in the main
      symbol table (skConstant), but enum members live in the reverse
      enum-member index, so 'Cannot resolve array bound' was raised. }
    procedure TestRun_InlineEnumSubrange_ArrayBound;
    { Sibling incidentally fixed by the same ResolveArrayBound change: an
      inline 'set of <enumLo>..<enumHi>' resolves its bounds through the same
      helper. }
    procedure TestRun_InlineEnumSubrange_SetType;
    { GH #182 (third follow-up): a MULTI-DIMENSIONAL array whose FIRST
      dimension is an enum-subrange TYPE — array[TPTStrict, 0..1] — counted the
      subrange dimension as the FULL base enum's span (the '@TEnum' dimension
      marker hardcoded low=0 and used Members.Count-1 for the high), so a
      const rejected 'has 14 element(s) but its dimensions need 16' and a var
      silently got an oversized first dimension. Covers const + var, named
      subrange type. }
    procedure TestRun_MultiDimEnumSubrange_Array;

    { forward; in a program decl section (issue #130 bug2): the forward decl
      used to swallow the following implementation as a nested-proc body. }
    procedure TestRun_Forward_MutualRecursion;

    { Large / 64-bit integer constants (issue #133): a hex value above 32 bits
      was truncated (inferred Integer); a value above High(Int64) was rejected.
      Untyped consts now widen by magnitude; typed Int64/UInt64 accept the full
      64-bit bit pattern. }
    procedure TestRun_Const_LargeHex_NotTruncated;
    procedure TestRun_Const_Int64BitPattern;
    procedure TestRun_Const_UInt64BitPattern;
    procedure TestRun_Const_UntypedAboveInt64_IsUInt64;
    procedure TestRun_ArrayConst_Int64BitPattern;

    { Conditional compilation (issue #131): predefined BLAISE, DEFINE/UNDEF,
      IFDEF/IFNDEF/ELSE/ENDIF, nesting. }
    procedure TestRun_Ifdef_PredefinedBlaise;
    procedure TestRun_Ifdef_DefineUndefIfndefNested;
    { BUG-031: a nested routine that calls a SIBLING nested routine must
      inherit the sibling's captures so the call site can forward the
      outer variables' addresses. }
    procedure TestRun_SiblingNestedCall_ForwardsCaptures;
    procedure TestRun_SiblingNestedCall_ForwardsSelfCapture;
    { Inc/Dec on an Int64 target with an Integer-typed step: QBE emitted
      `add l, w` (mixing a w step temp into an l add) and rejected the IR.
      The step must be sign-extended to l first (BUG-20260723-qbe-incdec-wide-narrow-step). }
    procedure TestRun_IncDec_WideTarget_NarrowStep;
    { GH #195 — bit operators inside a float const expression, end to end. }
    procedure TestRun_BitOpsInFloatConstExpr;
  end;

implementation

procedure TE2EMiscTests.SetUp;
begin
  inherited SetUp();
  SetUpScratch('compiler/target/test-e2e-misc');
end;

const
  LE = #10;

  SrcBoolOps = '''
    program Prg;
    var A, B: Boolean;
    begin
      A := True;
      B := False;
      if A and not B then WriteLn('t1');
      if A or B then WriteLn('t2');
      if not (A and B) then WriteLn('t3')
    end.
    ''';

  SrcWriteLnBoolVar = '''
    program Prg;
    var B: Boolean;
    begin
      B := True;
      WriteLn(B);
      B := False;
      WriteLn(B)
    end.
    ''';

  SrcWriteLnBoolExpr = '''
    program Prg;
    begin
      WriteLn(3 > 2);
      WriteLn(1 = 2)
    end.
    ''';

  SrcMultiArg = '''
    program Prg;
    var I, J, K: Integer;
    begin
      I := 1; J := 2; K := 3;
      WriteLn(I, J, K)
    end.
    ''';

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

  SrcChainedRecord = '''
    program Prg;
    type
      TInner = record Value: Integer; end;
      TOuter = record I: TInner; end;
    var O: TOuter; N: Integer;
    begin
      N := O.I.Value;
      WriteLn(N)
    end.
    ''';

  { GH #187: a record-in-record chain that ENDS in an array subscript is a
    valid assignment target — Aouter.ora[x].innerOneArr[c] := V.  The parser
    used to reject the ':=' with "Expected ':=' or '(' after chain". }
  SrcRecordChainArrayAssign = '''
    program Prg;
    type
      TInner = record Arr: array[0..3] of Integer; end;
      TOuter = record Ora: array[0..1] of TInner; end;
    var O: TOuter; x, c: Integer;
    begin
      for x := 0 to 1 do
        for c := 0 to 3 do
          O.Ora[x].Arr[c] := (x + 1) * (c + 1);
      WriteLn(O.Ora[0].Arr[0], ' ', O.Ora[0].Arr[3], ' ',
              O.Ora[1].Arr[0], ' ', O.Ora[1].Arr[3])
    end.
    ''';

  SrcConstInt = '''
    program Prg;
    const MaxVal = 100;
    var X: Integer;
    begin
      X := MaxVal + 1;
      WriteLn(X)
    end.
    ''';

  SrcConstStr = '''
    program Prg;
    const Greeting = 'Hello';
    begin
      WriteLn(Greeting)
    end.
    ''';

  SrcConstNeg = '''
    program Prg;
    const MinVal = -10;
    var X: Integer;
    begin
      X := MinVal * 2;
      WriteLn(X)
    end.
    ''';

  { issue #96 — const declared with a compile-time formula (precedence,
    parentheses, division, and a forward reference to a prior const). }
  SrcConstExpr = '''
    program Prg;
    const
      A = 2 * 3;
      B = 2 + 3 * 4;
      C = (2 + 3) * 4;
      D = 100 div 7;
      Base = 10;
      E = Base * 2 + 1;
    begin
      WriteLn(A);
      WriteLn(B);
      WriteLn(C);
      WriteLn(D);
      WriteLn(E)
    end.
    ''';

  { Regression: typed array constant declared inside a function body was
    referenced as $Name but never emitted as a data item, producing a
    link error.  Exercises the full toolchain (codegen + QBE + ld). }
  SrcConstLocalArrayInFunc = '''
    program Prg;
    function DaysInMonth(M: Integer): Integer;
    const
      Days: array[1..12] of Integer = (31,28,31,30,31,30,31,31,30,31,30,31);
    begin
      Result := Days[M]
    end;
    begin
      WriteLn(DaysInMonth(1));
      WriteLn(DaysInMonth(2));
      WriteLn(DaysInMonth(12))
    end.
    ''';

  SrcProcTypeVar = '''
    program Prg;
    type TFn = function(X: Integer): Integer;
    function Twice(X: Integer): Integer;
    begin Result := X * 2 end;
    var F: TFn;
    begin
      F := @Twice;
      WriteLn(F(7))
    end.
    ''';

  SrcProcTypeOfObject = '''
    program Prg;
    type
      TProc = procedure of object;
      TFoo = class
        FVal: Integer;
        procedure Print;
      end;
    procedure TFoo.Print;
    begin WriteLn(FVal) end;
    var
      Obj: TFoo;
      M: TProc;
    begin
      Obj := TFoo.Create();
      Obj.FVal := 55;
      M := @Obj.Print;
      M();
      Obj.Free()
    end.
    ''';

  { Function-pointer class field called through a receiver, as an expression. }
  SrcProcFieldReturn = '''
    program Prg;
    type
      TFn = function(const S: string): Integer;
      TBox = class
        FFn: TFn;
        function Run(const S: string): Integer;
      end;
    function Len2(const S: string): Integer;
    begin Result := Length(S) end;
    function TBox.Run(const S: string): Integer;
    begin Result := Self.FFn(S) end;
    var B: TBox;
    begin
      B := TBox.Create();
      B.FFn := @Len2;
      WriteLn(IntToStr(B.Run('hello')));
      B.Free()
    end.
    ''';

  { Function-pointer class field called as a statement. }
  SrcProcFieldStmt = '''
    program Prg;
    type
      TFn = procedure(const S: string);
      TBox = class
        FFn: TFn;
        procedure Run;
      end;
    procedure Hi(const S: string);
    begin WriteLn(S) end;
    procedure TBox.Run;
    begin Self.FFn('hi') end;
    var B: TBox;
    begin
      B := TBox.Create();
      B.FFn := @Hi;
      B.Run();
      B.Free()
    end.
    ''';

  { Function-pointer class field with an out parameter — the argument must be
    passed by reference so the callee writes back into the caller's variable. }
  SrcProcFieldOut = '''
    program Prg;
    type
      TFn = function(const S: string; out V: string): Boolean;
      TBox = class
        FFn: TFn;
        function Run(const S: string): string;
      end;
    function Echo(const S: string; out V: string): Boolean;
    begin V := S; Result := True end;
    function TBox.Run(const S: string): string;
    var V: string;
    begin
      if Self.FFn(S, V) then Result := V else Result := '?'
    end;
    var B: TBox;
    begin
      B := TBox.Create();
      B.FFn := @Echo;
      WriteLn(B.Run('hi'));
      B.Free()
    end.
    ''';

  { Function-pointer class field with several value arguments. }
  SrcProcFieldMultiArg = '''
    program Prg;
    type
      TFn = function(A, B, C: Integer): Integer;
      TBox = class
        FFn: TFn;
        function Run(X: Integer): Integer;
      end;
    function Sum3(A, B, C: Integer): Integer;
    begin Result := A + B + C end;
    function TBox.Run(X: Integer): Integer;
    begin Result := Self.FFn(X, X + 1, X + 2) end;
    var B: TBox;
    begin
      B := TBox.Create();
      B.FFn := @Sum3;
      WriteLn(IntToStr(B.Run(10)));
      B.Free()
    end.
    ''';

  { Method-pointer (of object) class field: capture @Obj.Method into a field
    and call through it.  The capture stores a 16-byte (Code, Data) pair. }
  SrcMethodPtrField = '''
    program Prg;
    type
      TEvt = procedure(const S: string) of object;
      TSrc = class
        Tag: string;
        procedure Handle(const S: string);
      end;
      TBox = class
        FEvt: TEvt;
        procedure Fire(const S: string);
      end;
    procedure TSrc.Handle(const S: string);
    begin WriteLn(Self.Tag, ':', S) end;
    procedure TBox.Fire(const S: string);
    begin Self.FEvt(S) end;
    var B: TBox; S: TSrc;
    begin
      S := TSrc.Create(); S.Tag := 'T';
      B := TBox.Create();
      B.FEvt := @S.Handle;
      B.Fire('hello');
      B.Free();
      S.Free()
    end.
    ''';

  { Method-pointer capture of a VIRTUAL method through a base-typed variable:
    A is declared TAnimal but holds a TDog, so @A.Speak must capture TDog's
    override (print 'dog'), resolving the Code half through A's vtable rather
    than freezing the declared type's TAnimal.Speak. }
  SrcMethodPtrVirtualCaptureVar = '''
    program Prg;
    type
      TSpeak = procedure of object;
      TAnimal = class
        procedure Speak; virtual;
      end;
      TDog = class(TAnimal)
        procedure Speak; override;
      end;
    procedure TAnimal.Speak;
    begin WriteLn('animal') end;
    procedure TDog.Speak;
    begin WriteLn('dog') end;
    var A: TAnimal; M: TSpeak;
    begin
      A := TDog.Create();
      M := @A.Speak;
      M();
      A.Free()
    end.
    ''';

  { Same dynamic-dispatch capture, but stored into a class FIELD rather than a
    local variable — exercises the field-destination assignment path. }
  SrcMethodPtrVirtualCaptureField = '''
    program Prg;
    type
      TSpeak = procedure of object;
      TAnimal = class
        procedure Speak; virtual;
      end;
      TDog = class(TAnimal)
        procedure Speak; override;
      end;
      TBox = class
        M: TSpeak;
      end;
    procedure TAnimal.Speak;
    begin WriteLn('animal') end;
    procedure TDog.Speak;
    begin WriteLn('dog') end;
    var A: TAnimal; B: TBox;
    begin
      A := TDog.Create();
      B := TBox.Create();
      B.M := @A.Speak;
      B.M();
      B.Free();
      A.Free()
    end.
    ''';

  { A method returning a 'function ... of object' value.  The return is a
    16-byte (Code, Data) aggregate; it must travel back by the two-register/
    sret record-return ABI rather than a scalar that drops the Data half.
    Op(3, 4) invokes the captured method pointer and must print 7. }
  SrcMethodPtrReturn = '''
    program Prg;
    type TBinOp = function(X, Y: Integer): Integer of object;
    type
      TCalc = class
        function Add(X, Y: Integer): Integer;
        function GetOp: TBinOp;
      end;
    function TCalc.Add(X, Y: Integer): Integer;
    begin Result := X + Y end;
    function TCalc.GetOp: TBinOp;
    begin Result := @Self.Add end;
    var C: TCalc; Op: TBinOp;
    begin
      C := TCalc.Create();
      Op := C.GetOp();
      WriteLn(Op(3, 4));
      C.Free()
    end.
    ''';

  { Method pointer whose RETURNED method READS an instance field (Self.Base).
    A method ptr is a 16-byte [Code; Data] aggregate; if a backend returns only
    the Code half the Data (Self) pointer is lost and the invoked method
    dereferences garbage — which it only observes when it actually uses Self.
    SrcMethodPtrReturn's Add(X,Y)=X+Y never touches Self, so it cannot catch
    that defect; this one does, on every backend.  Also exercises a field
    destination (Self.FStored), a free-function method-ptr return, and an
    immediate invoke of the returned pointer (C.GetFn()(9)). }
  SrcMethodPtrReturnSelf = '''
    program Prg;
    type TFn = function(X: Integer): Integer of object;
    type
      TCalc = class
        Base: Integer;
        FStored: TFn;
        function AddBase(X: Integer): Integer;
        function GetFn: TFn;
        procedure StoreFn;
        function CallStored(X: Integer): Integer;
      end;
    function TCalc.AddBase(X: Integer): Integer;
    begin Result := Self.Base + X end;
    function TCalc.GetFn: TFn;
    begin Result := @Self.AddBase end;
    procedure TCalc.StoreFn;
    begin Self.FStored := Self.GetFn() end;
    function TCalc.CallStored(X: Integer): Integer;
    begin Result := Self.FStored(X) end;
    var GC: TCalc;
    function GetGlobalFn: TFn;
    begin Result := @GC.AddBase end;
    var C: TCalc; F: TFn;
    begin
      C := TCalc.Create();
      C.Base := 100;
      F := C.GetFn();
      WriteLn(F(7));
      C.StoreFn();
      WriteLn(C.CallStored(5));
      GC := C;
      F := GetGlobalFn();
      WriteLn(F(3));
      WriteLn(C.GetFn()(9));
      C.Free()
    end.
    ''';

  { Assigning @Self.Method to a bare (implicit-Self) method-pointer field:
    FFn := @Self.DoIt inside a method, with no 'Self.' on the LHS.  DoIt reads
    another field through Self, so a wrong Data half (the bug) would crash or
    print garbage rather than 'T:x'. }
  SrcMethodPtrImplicitSelfFieldAssign = '''
    program Prg;
    type
      TProc = procedure(const S: string) of object;
      TA = class
        FName: string;
        FFn: TProc;
        procedure DoIt(const S: string);
        procedure Fire;
      end;
    procedure TA.DoIt(const S: string);
    begin WriteLn(FName + ':' + S) end;
    procedure TA.Fire;
    begin
      FFn := @Self.DoIt;
      FFn('x')
    end;
    var A: TA;
    begin
      A := TA.Create();
      A.FName := 'T';
      A.Fire();
      A.Free()
    end.
    ''';

  { Unqualified (implicit-Self) call to a procedural-typed field, as an
    expression — FFn(...) with no 'Self.' prefix. }
  SrcImplicitProcFieldExpr = '''
    program Prg;
    type
      TFn = function(A, B, C: Integer): Integer;
      TBox = class
        FFn: TFn;
        function Run(X: Integer): Integer;
      end;
    function Sum3(A, B, C: Integer): Integer;
    begin Result := A + B + C end;
    function TBox.Run(X: Integer): Integer;
    begin Result := FFn(X, X + 1, X + 2) end;
    var B: TBox;
    begin
      B := TBox.Create();
      B.FFn := @Sum3;
      WriteLn(IntToStr(B.Run(10)));
      B.Free()
    end.
    ''';

  { Unqualified (implicit-Self) call to a procedural-typed field, as a
    statement. }
  SrcImplicitProcFieldStmt = '''
    program Prg;
    type
      TFn = procedure(const S: string);
      TBox = class
        FFn: TFn;
        procedure Run;
      end;
    procedure Hi(const S: string);
    begin WriteLn(S) end;
    procedure TBox.Run;
    begin FFn('hi') end;
    var B: TBox;
    begin
      B := TBox.Create();
      B.FFn := @Hi;
      B.Run();
      B.Free()
    end.
    ''';

  SrcDefaultParam = '''
    program Prg;
    function Add(A: Integer; B: Integer = 10): Integer;
    begin Result := A + B end;
    begin
      WriteLn(Add(5));
      WriteLn(Add(5, 20))
    end.
    ''';

  SrcDefaultParamMulti = '''
    program Prg;
    function Greet(Name: string; Prefix: string = 'Hello';
                   Suffix: string = '!'): string;
    begin Result := Prefix + ' ' + Name + Suffix end;
    begin
      WriteLn(Greet('World'));
      WriteLn(Greet('Ada', 'Hi'))
    end.
    ''';

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

  SrcVarParamString = '''
    program Prg;
    procedure Append(var S: string; const T: string);
    begin
      S := S + T
    end;
    var R: string;
    begin
      R := 'Hello';
      Append(R, ' World');
      WriteLn(R)
    end.
    ''';

  SrcConstParam = '''
    program Prg;
    function Twice(const X: Integer): Integer;
    begin Result := X * 2 end;
    begin
      WriteLn(Twice(21))
    end.
    ''';

  SrcTypeCastIntByte = '''
    program Prg;
    var I: Integer; B: Byte;
    begin
      I := 300;
      B := Byte(I);
      WriteLn(B)
    end.
    ''';

  SrcTypeCastPointerInt = '''
    program Prg;
    var I: Integer; P1: Pointer;
    begin
      I  := 42;
      P1 := Pointer(I);
      WriteLn(Integer(P1))
    end.
    ''';

  { A Cardinal/UInt32 value above 2^31 must print as the large unsigned value,
    not a negative signed wrap.  3000000000 fits in UInt32 but is negative as a
    signed Int32. }
  SrcWriteUnsigned32 = '''
    program Prg;
    var c: Cardinal;
    begin
      c := 3000000000;
      WriteLn(c)
    end.
    ''';

  SrcForInStringByte = '''
    program Prg;
    var
      S: string;
      B: Byte;
    begin
      S := 'Hi';
      for B in S do
        WriteLn(B)
    end.
    ''';

  SrcForInStringInteger = '''
    program Prg;
    var
      S: string;
      I: Integer;
    begin
      S := 'Hi';
      for I in S do
        WriteLn(I)
    end.
    ''';

  { 'Aâ' = A (65) + â (U+00E2, codepoint 226, 2 UTF-8 bytes) }
  SrcForInStringCP2Byte = '''
    program Prg;
    var
      S: string;
      I: Integer;
    begin
      S := 'Aâ';
      for I in S do
        WriteLn(I)
    end.
    ''';

  { '€X' = € (U+20AC, codepoint 8364, 3 UTF-8 bytes) + X (88) }
  SrcForInStringCP3Byte = '''
    program Prg;
    var
      S: string;
      I: Integer;
    begin
      S := '€X';
      for I in S do
        WriteLn(I)
    end.
    ''';

  SrcForInArrayInteger = '''
    program Prg;
    var
      A: array[0..2] of Integer;
      X: Integer;
    begin
      A[0] := 10;
      A[1] := 20;
      A[2] := 30;
      for X in A do
        WriteLn(X)
    end.
    ''';

  SrcForInClassEnum = '''
    program Prg;
    type
      TRangeEnum = class
        FCurrent: Integer;
        FLast: Integer;
        constructor Create(AFirst, ALast: Integer);
        function MoveNext: Boolean;
        function GetCurrent: Integer;
        property Current: Integer read GetCurrent;
      end;
      TRange = class
        FFirst: Integer;
        FLast: Integer;
        constructor Create(AFirst, ALast: Integer);
        function GetEnumerator: TRangeEnum;
      end;
    constructor TRangeEnum.Create(AFirst, ALast: Integer);
    begin
      FCurrent := AFirst - 1;
      FLast := ALast;
    end;
    function TRangeEnum.MoveNext: Boolean;
    begin
      FCurrent := FCurrent + 1;
      Result := FCurrent <= FLast;
    end;
    function TRangeEnum.GetCurrent: Integer;
    begin
      Result := FCurrent;
    end;
    constructor TRange.Create(AFirst, ALast: Integer);
    begin
      FFirst := AFirst;
      FLast := ALast;
    end;
    function TRange.GetEnumerator: TRangeEnum;
    begin
      Result := TRangeEnum.Create(FFirst, FLast);
    end;
    var
      R: TRange;
      N: Integer;
    begin
      R := TRange.Create(3, 5);
      for N in R do
        WriteLn(N);
      R.Free();
    end.
    ''';

procedure TE2EMiscTests.TestRun_BooleanOps_AllExpressions;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue(CompileAndRun(SrcBoolOps, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('all three branches fire',
    't1' + LE + 't2' + LE + 't3' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_WriteLn_BoolVar_PrintsTrueOrFalse;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcWriteLnBoolVar, 'True' + LE + 'False' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_WriteLn_BoolExpr_PrintsTrueOrFalse;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcWriteLnBoolExpr, 'True' + LE + 'False' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_MultiArgWriteLn_PrintsAllArgs;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue(CompileAndRun(SrcMultiArg, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('three values concatenated with trailing newline',
    '123' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_ForBreak_StopsAtFiveHalt;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcForBreak, '5' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_ExitFromFunction_ReturnsImmediately;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcExitFunc, '7' + LE + '9' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_ChainedRecordField_LoadsInner;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue(CompileAndRun(SrcChainedRecord, Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('chained read of zero-initialised field', '0' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_RecordChainArrayAssign;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { (0+1)*(0+1)=1, (0+1)*(3+1)=4, (1+1)*(0+1)=2, (1+1)*(3+1)=8 }
  AssertRunsOnAll(SrcRecordChainArrayAssign, '1 4 2 8' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_Const_IntegerConst;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcConstInt, '101' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_Const_StringConst;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcConstStr, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Hello', 'Hello' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_Const_LocalArrayInFunction;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcConstLocalArrayInFunc, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Jan Feb Dec days',
    '31' + LE + '28' + LE + '31' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_Const_NegativeConst;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcConstNeg, '-20' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_Const_CompileTimeExpression;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { A=6, B=14 (precedence), C=20 (parens), D=14 (div), E=21 (named-ref). }
  AssertRunsOnAll(SrcConstExpr,
    '6' + LE + '14' + LE + '20' + LE + '14' + LE + '21' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_ProcType_CallViaVariable;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcProcTypeVar, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('14', '14' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_ProcType_FloatArgs_ViaVariable;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll('''
    program P;
    type
      TF1 = function(A: Double): Double;
      TF9 = function(a, b, c, d, e, f, g, h, i: Double): Double;
      TFS = function(A: Single; N: Integer): Integer;
    function Dbl(A: Double): Double;
    begin
      Result := A * 2.0
    end;
    function Pick(a, b, c, d, e, f, g, h, i: Double): Double;
    begin
      Result := i + a
    end;
    function SN(A: Single; N: Integer): Integer;
    begin
      Result := Trunc(A * 10) + N
    end;
    var
      P1: TF1;
      P9: TF9;
      PS: TFS;
    begin
      P1 := @Dbl;
      WriteLn(Trunc(P1(3.5) * 10));
      P9 := @Pick;
      WriteLn(Trunc(P9(1.5,2.5,3.5,4.5,5.5,6.5,7.5,8.5,9.5) * 10));
      PS := @SN;
      WriteLn(PS(1.5, 100))
    end.
    ''', '70' + LE + '110' + LE + '115' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_ProcType_MixedIntFloat_Overflow_ViaVariable;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { 7 ints (one overflows) interleaved with 2 doubles: the int and xmm
    register sequences must advance independently and overflow slots stay
    in ascending arg order. }
  AssertRunsOnAll('''
    program P;
    type
      TFm = function(n1, n2, n3: Integer; d1: Double; n4, n5, n6: Integer;
                     d2: Double; n7: Integer): Integer;
    function M(n1, n2, n3: Integer; d1: Double; n4, n5, n6: Integer;
               d2: Double; n7: Integer): Integer;
    begin
      Result := n1 + n2*2 + n3*3 + n4*4 + n5*5 + n6*6 + n7*7 +
                Trunc(d1) * 100 + Trunc(d2) * 1000
    end;
    var PM: TFm;
    begin
      PM := @M;
      WriteLn(PM(1, 2, 3, 4.5, 4, 5, 6, 7.5, 8))
    end.
    ''', IntToStr(1 + 4 + 9 + 16 + 25 + 36 + 56 + 400 + 7000) + LE, 0);
end;

procedure TE2EMiscTests.TestRun_ProcType_HoistedStrWithOverflow_ViaVariable;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { A hoisted const-string arg (the concat transient is pinned, adding 8
    bytes to the hoist region) combined with overflow args: the overflow
    fresh-region size must be computed ONCE — the first subq changes
    FSPDepth, so recomputing AlignFreshBytes afterwards yields a different
    pad, shifting the overflow reload offsets and the cleanup amount by 8
    (BUG-20260722-native-procvar-float-args review follow-up). }
  AssertRunsOnAll('''
    program P;
    type
      TFh = function(const S: string; a, b, c, d, e: Integer; d1: Double;
                     f, g: Integer): Integer;
    function H(const S: string; a, b, c, d, e: Integer; d1: Double;
               f, g: Integer): Integer;
    begin
      Result := Length(S) + a + b*2 + c*3 + d*4 + e*5 +
                Trunc(d1) * 100 + f*6 + g*7
    end;
    var
      PH: TFh;
      S: string;
      R: Integer;
    begin
      PH := @H;
      S := 'ab';
      R := PH(S + '!', 1, 2, 3, 4, 5, 2.5, 6, 7);
      WriteLn(R)
    end.
    ''', IntToStr(3 + 1 + 4 + 9 + 16 + 25 + 200 + 36 + 49) + LE, 0);
end;

procedure TE2EMiscTests.TestRun_ProcType_OfObject_Dispatch;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcProcTypeOfObject, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('55', '55' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_ProcFieldCall_ReturnValue;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcProcFieldReturn, '5' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_ProcFieldCall_Statement;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcProcFieldStmt, 'hi' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_ProcFieldCall_OutParam;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcProcFieldOut, 'hi' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_ProcFieldCall_MultiArg;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcProcFieldMultiArg, '33' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_MethodPtrField_AssignAndCall;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcMethodPtrField, 'T:hello' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_MethodPtrVirtualCapture_Var;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcMethodPtrVirtualCaptureVar, 'dog' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_MethodPtrVirtualCapture_Field;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcMethodPtrVirtualCaptureField, 'dog' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_MethodPtrReturn;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcMethodPtrReturn, '7' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_MethodPtrReturn_ReadsSelf;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  { 107, 105, 103, 109 — each line proves the Data (Self) half of the returned
    16-byte method pointer survived: AddBase reads Self.Base (100). }
  AssertRunsOnAll(SrcMethodPtrReturnSelf,
    '107' + LE + '105' + LE + '103' + LE + '109' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_MethodPtrImplicitSelfFieldAssign;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcMethodPtrImplicitSelfFieldAssign, 'T:x' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_ImplicitSelfProcField_Expr;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcImplicitProcFieldExpr, '33' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_ImplicitSelfProcField_Stmt;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcImplicitProcFieldStmt, 'hi' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_DefaultParam_OmitLast;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDefaultParam, '15' + LE + '25' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_DefaultParam_OmitMultiple;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcDefaultParamMulti, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('greetings', 'Hello World!' + LE + 'Hi Ada!' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_VarParam_SwapIntegers;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcVarParamSwap, '7' + LE + '3' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_VarParam_ModifyString;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcVarParamString, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Hello World', 'Hello World' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_ConstParam_CanRead;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcConstParam, '42' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_TypeCast_IntegerByte;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcTypeCastIntByte, '44' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_TypeCast_PointerInteger;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTypeCastPointerInt, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('42', '42' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_WriteUnsigned32_PrintsUnsigned;
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcWriteUnsigned32, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('3000000000 (unsigned, not negative)', '3000000000' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_ForIn_String_ByteVar_PrintsBytes;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcForInStringByte, '72' + LE + '105' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_ForIn_String_IntegerVar_PrintsCodePoints;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcForInStringInteger, '72' + LE + '105' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_ForIn_String_IntegerVar_CodePoints_TwoByte;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcForInStringCP2Byte,
    '65' + LE + '226' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_ForIn_String_IntegerVar_CodePoints_ThreeByte;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcForInStringCP3Byte,
    '8364' + LE + '88' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_ForIn_Array_Integer_PrintsElements;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcForInArrayInteger, '10' + LE + '20' + LE + '30' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_ForIn_ClassEnumerator_PrintsElements;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcForInClassEnum, '3' + LE + '4' + LE + '5' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_NestedProc_MutatesCapturedVar;
const
  Src =
    '''
        program Prg;
        procedure Outer;
        var x: Integer;
          procedure Inner;
          begin
            x := x + 10;
            WriteLn(IntToStr(x))
          end;
        begin
          x := 5;
          WriteLn(IntToStr(x));
          Inner();
          WriteLn(IntToStr(x))
        end;
        begin
          Outer()
        end.
        ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('x=5, inner mutates to 15, outer sees 15',
    '5' + LE + '15' + LE + '15' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_NestedProc_SiblingSameName_ResolvesPerScope;
const
  Src =
    '''
        program Prg;
        procedure First;
          function Helper(X: Integer): Integer;
          begin
            Result := X + 1
          end;
        begin
          WriteLn(IntToStr(Helper(10)))
        end;
        procedure Second;
          function Helper(X: Integer): Integer;
          begin
            Result := X + 2
          end;
        begin
          WriteLn(IntToStr(Helper(20)))
        end;
        begin
          First();
          Second()
        end.
        ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('First.Helper(10)=11, Second.Helper(20)=22',
    '11' + LE + '22' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_NestedFunc_InSiblingMethods_ResolvesPerScope;
const
  Src =
    '''
        program Prg;
        type
          TFoo = class
            procedure MethodA;
            procedure MethodB;
          end;
        procedure TFoo.MethodA;
          function Helper(X: Integer): Integer;
          begin
            Result := X + 1
          end;
        begin
          WriteLn(IntToStr(Helper(10)))
        end;
        procedure TFoo.MethodB;
          function Helper(X: Integer): Integer;
          begin
            Result := X + 2
          end;
        begin
          WriteLn(IntToStr(Helper(20)))
        end;
        var F: TFoo;
        begin
          F := TFoo.Create;
          F.MethodA();
          F.MethodB()
        end.
        ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('MethodA.Helper(10)=11, MethodB.Helper(20)=22',
    '11' + LE + '22' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_NestedProc_CapturesVarRecordParam;
const
  Src =
    '''
        program Prg;
        type TRec = record A, B: Integer; end;
        procedure Outer(var R: TRec);
          procedure Inner;
          var Sum: Integer;
          begin
            Sum := R.A + R.B;
            R.A := Sum;
            R.B := Sum * 2
          end;
        begin
          Inner()
        end;
        var Rec: TRec;
        begin
          Rec.A := 3; Rec.B := 4;
          Outer(Rec);
          WriteLn(IntToStr(Rec.A), ' ', IntToStr(Rec.B))
        end.
        ''';
begin
  AssertRunsOnAll(Src, '7 14' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_NestedProc_CapturesVarScalarParam;
const
  Src =
    '''
        program Prg;
        var ReadBack: Integer;
        procedure L1(var Q: Integer);
          procedure L2;
          begin
            ReadBack := Q + 1;   { read the captured var-param }
            Q := 88              { write through the captured var-param }
          end;
          { two levels deep — the innermost still reaches the caller's Q }
          procedure Deep;
            procedure Inner;
            begin Q := Q + 11 end;
          begin Inner() end;
        begin L2(); Deep() end;
        var X: Integer;
        begin
          X := 55;
          L1(X);
          WriteLn(IntToStr(X));         { 88 + 11 = 99 (caller sees the writes) }
          WriteLn(IntToStr(ReadBack))   { 55 + 1 = 56 (read saw the caller value) }
        end.
        ''';
begin
  AssertRunsOnAll(Src, '99' + LE + '56' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_NestedProc_CapturesVarFloatParam;
const
  { Same double-deref path, FLOAT width — the native Double/Single arms had the
    same ordering+missing-deref bug as the integer arms. }
  Src =
    '''
        program Prg;
        var Matched: Integer;
        procedure L1(var Q: Double);
          procedure L2;
          begin
            if Q = 1.25 then Matched := 1 else Matched := 0;   { read }
            Q := 3.5                                            { write }
          end;
        begin L2() end;
        var X: Double;
        begin
          X := 1.25;
          L1(X);
          WriteLn(IntToStr(Matched));   { 1 — read saw the caller value }
          WriteLn(X > 3.0)              { True — write reached the caller }
        end.
        ''';
begin
  AssertRunsOnAll(Src, '1' + LE + 'True' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_NestedProc_ShadowsEnclosingLocal;
const
  { L2 declares its OWN V (shadows L1's V) but genuinely captures W.  L2's V
    must be a distinct slot; W must still be captured.  Plus a 2-level shadow
    (L3 sees L2's V, not L1's). }
  Src =
    '''
        program Prg;
        procedure L1;
        var V, W: Integer;
          procedure L2;
          var V: Integer;                { shadows L1.V }
            procedure L3;
            begin WriteLn(IntToStr(V)) end;   { sees L2's V }
          begin
            V := 7;                       { L2's own V }
            W := 9;                       { captured L1.W }
            L3();
            WriteLn(IntToStr(V));
            WriteLn(IntToStr(W))
          end;
        begin
          V := 1; W := 0;
          L2();
          WriteLn(IntToStr(V));           { 1 — L1.V untouched by L2's shadow }
          WriteLn(IntToStr(W))            { 9 — L1.W written through the capture }
        end;
        begin L1() end.
        ''';
begin
  AssertRunsOnAll(Src,
    '7' + LE + '7' + LE + '9' + LE + '1' + LE + '9' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_NestedProc_CapturesLocalRecord;
const
  Src =
    '''
        program Prg;
        type TRec = record A, B: Integer; end;
        procedure Outer;
        var R: TRec;
          procedure Inner;
          begin
            R.A := R.A + 10;
            R.B := R.B + 20
          end;
        begin
          R.A := 1; R.B := 2;
          Inner();
          WriteLn(IntToStr(R.A), ' ', IntToStr(R.B))
        end;
        begin
          Outer()
        end.
        ''';
begin
  AssertRunsOnAll(Src, '11 22' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_NestedProc_CapturesVarArrayParam;
const
  Src =
    '''
        program Prg;
        type TArr = array[0..2] of Integer;
        procedure Outer(var A: TArr);
          procedure Inner;
          begin
            A[0] := 10; A[1] := 20; A[2] := A[0] + A[1]
          end;
        begin
          Inner()
        end;
        var Ar: TArr;
        begin
          Ar[0] := 0; Ar[1] := 0; Ar[2] := 0;
          Outer(Ar);
          WriteLn(IntToStr(Ar[0]), ' ', IntToStr(Ar[1]), ' ', IntToStr(Ar[2]))
        end.
        ''';
begin
  AssertRunsOnAll(Src, '10 20 30' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_Diamond_SingleArg_WorksAtRuntime;
const
  Src = '''
    program Prg;
    type
      TBox<T> = class
        FValue: T;
        function  GetValue: T;
        begin Result := Self.FValue end;
        procedure SetValue(V: T);
        begin Self.FValue := V end;
      end;
    var B: TBox<Integer>;
    begin
      B := TBox<>.Create();
      B.SetValue(99);
      WriteLn(B.GetValue())
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('output', '99' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_Diamond_TwoArgs_WorksAtRuntime;
const
  Src = '''
    program Prg;
    type
      TPair<K, V> = class
        FKey: K;
        FVal: V;
        function  GetKey: K;
        begin Result := Self.FKey end;
        function  GetVal: V;
        begin Result := Self.FVal end;
        procedure SetKey(K2: K);
        begin Self.FKey := K2 end;
        procedure SetVal(V2: V);
        begin Self.FVal := V2 end;
      end;
    var P: TPair<Integer, Integer>;
    begin
      P := TPair<>.Create();
      P.SetKey(3);
      P.SetVal(7);
      WriteLn(P.GetKey());
      WriteLn(P.GetVal())
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('output', '3' + LE + '7' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_AddrOf_DynArrayFieldElement;
const Src = '''
    program Prg;
    type
      THolder = record Items: array of Integer; end;
    var
      A: array of Integer;
      H: THolder;
      P: ^Integer;
    begin
      SetLength(A, 3);
      A[0] := 10;
      A[1] := 20;
      A[2] := 30;
      H.Items := A;
      P := @H.Items[1];
      WriteLn(P^)
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('output', '20' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_GenericRecord_FieldStore_Prints;
const Src = '''
    program Prg;
    type
      TMyVal<T> = record
        Value: T;
      end;
    var V: TMyVal<Integer>;
    begin
      V.Value := 9;
      WriteLn(V.Value)
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('output', '9' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_GenericRecord_WithMethod_Prints;
const Src = '''
    program Prg;
    type
      TMyVal<T> = record
        Value: T;
        function GetValue: T;
        begin
          Result := Self.Value
        end;
      end;
    var V: TMyVal<Integer>;
    begin
      V.Value := 42;
      WriteLn(V.GetValue())
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('output', '42' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_GenericRecord_TwoParams_Prints;
const Src = '''
    program Prg;
    type
      TPair<K, V> = record
        Key: K;
        Val: V;
      end;
    var P: TPair<Integer, Integer>;
    begin
      P.Key := 10;
      P.Val := 20;
      WriteLn(P.Key);
      WriteLn(P.Val)
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('output', '10' + LE + '20' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_GenericRecord_StringField_Prints;
const Src = '''
    program Prg;
    type
      TMyVal<T> = record
        Value: T;
      end;
    var V: TMyVal<string>;
    begin
      V.Value := 'hello';
      WriteLn(V.Value)
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('output', 'hello' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_BitwiseNot_Integer;
const Src = '''
    program Prg;
    var I: Integer;
    begin
      I := 0;
      WriteLn(not I)
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('output', '-1' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_BitwiseNot_Byte;
const Src = '''
    program Prg;
    var B: Byte;
    begin
      B := 0;
      WriteLn(not B)
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('output', '-1' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_BitwiseNot_Int64;
const Src = '''
    program Prg;
    var I: Int64;
    begin
      I := 0;
      WriteLn(not I)
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('output', '-1' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_BitwiseNot_Bitmask;
const Src = '''
    program Prg;
    const MASK = 3;
    var Flags: Integer;
    begin
      Flags := 7;
      Flags := Flags and (not MASK);
      WriteLn(Flags)
    end.
    ''';
var Output: string; RCode: Integer;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('output', '4' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_WriteLn_StdErr_NotOnStdout;
const Src = '''
    program Prg;
    begin
      WriteLn(StdErr, 'error msg');
      WriteLn('ok')
    end.
    ''';
var
  Output: string;
  RCode:  Integer;
  BE:     TBackend;
  BName:  string;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  for BE := Low(TBackend) to High(TBackend) do
  begin
    BName := BackendName(BE);
    AssertTrue('[' + BName + '] compile+run',
      Self.CompileAndRunOn(BE, Src, Output, RCode));
    AssertEquals('[' + BName + '] exit code', 0, RCode);
    AssertTrue('[' + BName + '] fd not printed as integer prefix',
      Pos('2error', Output) = -1)
  end
end;

const
  SrcFuncOfObjectIndirect = '''
    program Prg;
    type
      TFn = function(N: Integer): Integer of object;
      TC = class
        FBase: Integer;
        function AddBase(N: Integer): Integer;
      end;
    function TC.AddBase(N: Integer): Integer;
    begin
      Result := FBase + N;
    end;
    var
      C: TC;
      F: TFn;
      X: Integer;
    begin
      C := TC.Create();
      C.FBase := 100;
      F := @C.AddBase;
      writeln(F(23));
      X := F(7) + F(8);
      writeln(X);
    end.
    ''';

procedure TE2EMiscTests.TestRun_FunctionOfObject_IndirectCall;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcFuncOfObjectIndirect, '123' + LE + '215' + LE, 0);
end;

const
  { @(class-field dynamic array)[idx] used as a real pointer: write through
    it (memcpy), then read the bytes back.  Under the old QBE codegen the
    element address was computed off the class variable's slot instead of
    the loaded instance pointer, so the memcpy scribbled garbage / crashed.
    Runs on BOTH backends. }
  SrcAddrClassFieldDynArr = '''
    program Prg;
    procedure CopyBytes(Dst, Src: Pointer; N: Int64); external name 'memcpy';
    type
      TBuf = class
        Data: array of Byte;
        Count: Integer;
      end;
    var
      B: TBuf;
    begin
      B := TBuf.Create();
      SetLength(B.Data, 8);
      B.Count := 0;
      CopyBytes(@B.Data[B.Count], PChar('Hi'), 2);
      B.Count := 2;
      CopyBytes(@B.Data[B.Count], PChar('!!'), 2);
      WriteLn(Chr(B.Data[0]), Chr(B.Data[1]), Chr(B.Data[2]), Chr(B.Data[3]));
      B.Free();
    end.
    ''';

procedure TE2EMiscTests.TestRun_AddrOfClassFieldDynArrayElem_LoadsInstance;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcAddrClassFieldDynArr, 'Hi!!' + LE, 0);
end;

const
  { inherited as an expression: the overriding function adds to the parent's
    result.  Exercises a value-returning inherited call plus inherited with an
    argument (inherited Scale(F)). }
  SrcInheritedExprCall = '''
    program Prg;
    type
      TBase = class
        function V: Integer; virtual;
        begin Result := 5 end;
        function Scale(F: Integer): Integer; virtual;
        begin Result := F * 10 end;
      end;
      TDerived = class(TBase)
        function V: Integer; override;
        begin Result := inherited V() + 100 end;
        function Scale(F: Integer): Integer; override;
        begin Result := inherited Scale(F) + 1 end;
      end;
    var D: TDerived;
    begin
      D := TDerived.Create();
      WriteLn(D.V());
      WriteLn(D.Scale(3));
      D.Free()
    end.
    ''';

procedure TE2EMiscTests.TestRun_InheritedFunctionCall_InExpression;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcInheritedExprCall, '105' + LE + '31' + LE, 0);
end;

const
  { Assign through a parenthesised cast: (a as TB).FX := 42.  The statement
    parser must accept a leading '(' as an assignment lvalue. }
  SrcParenCastTarget = '''
    program Prg;
    type
      TBase = class end;
      TDerived = class(TBase) FX: Integer; end;
    var a: TBase;
    begin
      a := TDerived.Create();
      (a as TDerived).FX := 42;
      WriteLn((a as TDerived).FX);
      a.Free()
    end.
    ''';

procedure TE2EMiscTests.TestRun_ParenCastAsAssignmentTarget;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcParenCastTarget, '42' + LE, 0);
end;

const
  { Nested generic type args, in both var-type and constructor position. }
  SrcNestedGeneric = '''
    program Prg;
    type TBox<T> = class
      FV: T;
      procedure SetV(V: T); begin FV := V end;
      function GetV: T; begin Result := FV end;
    end;
    var outer: TBox<TBox<Integer>>; inner: TBox<Integer>;
    begin
      inner := TBox<Integer>.Create();
      inner.SetV(7);
      outer := TBox<TBox<Integer>>.Create();
      outer.SetV(inner);
      WriteLn(outer.GetV().GetV());
      outer.Free();
      inner.Free()
    end.
    ''';

procedure TE2EMiscTests.TestRun_NestedGenericTypeArgs;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcNestedGeneric, '7' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_Subrange_NamedType;
const
  Src = '''
    program P;
    type TByte = 0..255;
    var b: TByte;
    begin b := 5; WriteLn(b) end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '5' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_Subrange_InRecordAndArray;
const
  { A subrange as a record field and as an array element type, plus a negative
    subrange — exercises that the aliased base type sizes layout correctly. }
  Src = '''
    program P;
    type
      TByte = 0..255;
      TIdx  = -10..10;
      TRec  = record b: TByte; i: TIdx; end;
    var
      r: TRec;
      a: array[0..2] of TByte;
    begin
      r.b := 200; r.i := -7;
      a[0] := 1; a[1] := 250; a[2] := 99;
      WriteLn(r.b, ' ', r.i, ' ', a[1])
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '200 -7 250' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_Subrange_HighLow;
const
  { GH #160: High/Low of a subrange TYPE (or a variable of it) must return the
    subrange's own bounds, not the base type's (2..10 gave 255/0 before).  A
    negative subrange must fold Low signed.  High/Low of an array indexed BY the
    subrange already worked — kept here as the no-regression check. }
  Src = '''
    program P;
    type
      Trange = 2..10;
      Tar = array[Trange] of Integer;
      TNeg = -3..3;
    var a: Tar; c: Trange; n: TNeg;
    begin
      WriteLn(High(Trange), ' ', Low(Trange));
      WriteLn(High(c), ' ', Low(c));
      WriteLn(High(a), ' ', Low(a));
      WriteLn(High(TNeg), ' ', Low(TNeg))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '10 2' + LE + '10 2' + LE + '10 2' + LE + '3 -3' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_Subrange_OfEnum;
const
  { GH #182: a subrange of an ENUMERATED type (TSub = b..c) must parse and work
    — High/Low yield the member ordinals, a var of it holds enum values, and an
    array indexed by the enum-subrange uses the subrange's ordinal bounds (not
    the full enum range). }
  Src = '''
    program P;
    type
      TE = (a, b, c, d);
      TSub = b..c;
      TArr = array[TSub] of Integer;
    var s: TSub; arr: TArr;
    begin
      WriteLn(Ord(High(TSub)), ' ', Ord(Low(TSub)));
      s := b; WriteLn(Ord(s));
      arr[b] := 10; arr[c] := 20;
      WriteLn(arr[b], ' ', arr[c]);
      WriteLn(High(TArr), ' ', Low(TArr))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '2 1' + LE + '1' + LE + '10 20' + LE + '2 1' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_Subrange_OfEnum_ConstArray;
const
  { The reporter's follow-up shape: C2 has exactly the subrange's 2 members.
    Element reads pin the ordinal-bounds indexing (East = ordinal 1 maps to
    the first element) alongside the full-enum control C1. }
  Src = '''
    program Array11;
    type
      TDirection = (North, East, South, West);
    const
      C1: array[TDirection] of Int64 = (10, 11, 12, 13);
    type
      TTurn = East..South;
    const
      C2: array[TTurn] of Int64 = (21, 22);
    begin
      WriteLn(C1[North], ' ', C1[West]);
      WriteLn(C2[East], ' ', C2[South])
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '10 13' + LE + '21 22' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_InlineEnumSubrange_ArrayBound;
const
  { The reporter's exact second-follow-up shape (CTargets2): an inline
    'array[ptWhitePawn..ptKing]' bound written with bare enum-member names.
    Covers const AND var forms, and element read/write at the subrange's
    ordinal offsets (ptWhitePawn = 1 maps to the first slot). }
  Src = '''
    program Array12;
    type
      TPieceType = (ptNil, ptWhitePawn, ptBlackPawn, ptRook,
                    ptKnight, ptBishop, ptQueen, ptKing);
    const
      CTargets: array[ptWhitePawn..ptKing] of Int64 = (1, 2, 3, 4, 5, 6, 7);
    var
      Live: array[ptWhitePawn..ptKing] of Int64;
      P: TPieceType;
    begin
      WriteLn(CTargets[ptWhitePawn], ' ', CTargets[ptRook], ' ', CTargets[ptKing]);
      for P := ptWhitePawn to ptKing do
        Live[P] := Ord(P) * 10;
      WriteLn(Live[ptWhitePawn], ' ', Live[ptKnight], ' ', Live[ptKing])
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '1 3 7' + LE + '10 40 70' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_InlineEnumSubrange_SetType;
const
  Src = '''
    program SetSub;
    type
      TPiece = (pNil, pPawn, pRook, pKnight, pBishop, pQueen, pKing);
    var
      S: set of pPawn..pKing;
    begin
      S := [pRook, pQueen];
      if pRook  in S then WriteLn('rook')  else WriteLn('no-rook');
      if pPawn  in S then WriteLn('pawn')  else WriteLn('no-pawn');
      Include(S, pPawn);
      if pPawn  in S then WriteLn('pawn2') else WriteLn('no-pawn2')
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'rook' + LE + 'no-pawn' + LE + 'pawn2' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_MultiDimEnumSubrange_Array;
const
  { The reporter's shape: a 2D const/var whose first dimension is the
    enum-subrange TYPE TPTStrict (ptWhitePawn..ptKing, 7 members).  The const
    has exactly 7 rows of 2 (14 elements); the earlier bug counted the
    subrange dimension as the full base enum (8) and rejected 14 vs 16.  The
    var confirms the first dimension really is [ptWhitePawn..ptKing], not an
    oversized [0..7]: writing at ptWhitePawn (ordinal 1) and ptKing (7) and
    reading back exercises the LowBound=1 rebase. }
  Src = '''
    program MD;
    type
      TPT = (ptNil, ptWhitePawn, ptBlackPawn, ptRook,
             ptKnight, ptBishop, ptQueen, ptKing);
      TPTStrict = ptWhitePawn..ptKing;
    const
      C: array[TPTStrict, 0..1] of Int64 = (
        (11, 12), (21, 22), (31, 32), (41, 42),
        (51, 52), (61, 62), (71, 72));
    var
      A: array[TPTStrict, 0..1] of Int64;
      { Full-enum first dim + enum-subrange second dim, and a NESTED
        'array[TEnum] of array[0..1]' — the latter guards the '..'-in-element
        scoping (the index-only '..' test must not see the element's range). }
      G: array[TPT, 0..1] of Int64;
      N: array[TPTStrict] of array[0..1] of Int64;
    begin
      WriteLn(C[ptWhitePawn, 0], ' ', C[ptRook, 1], ' ', C[ptKing, 0]);
      A[ptWhitePawn, 0] := 5;
      A[ptKing, 1] := 9;
      WriteLn(A[ptWhitePawn, 0], ' ', A[ptKing, 1]);
      G[ptNil, 0] := 100;
      G[ptKing, 1] := 200;
      WriteLn(G[ptNil, 0], ' ', G[ptKing, 1]);
      N[ptWhitePawn][0] := 3;
      N[ptKing][1] := 4;
      WriteLn(N[ptWhitePawn][0], ' ', N[ptKing][1])
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '11 32 71' + LE + '5 9' + LE + '100 200' + LE +
    '3 4' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_Ifdef_PredefinedBlaise;
const
  { The headline cross-compiler use case: BLAISE is predefined. }
  Src = '''
    program P;
    begin
      {$IFDEF BLAISE}
      WriteLn('blaise')
      {$ELSE}
      WriteLn('other')
      {$ENDIF}
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'blaise' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_Ifdef_DefineUndefIfndefNested;
const
  { DEFINE/UNDEF, IFNDEF, a predefined CPU/OS symbol, and nesting together. }
  Src = '''
    program P;
    {$DEFINE FOO}
    {$UNDEF FOO}
    begin
      {$IFDEF FOO}WriteLn('foo'){$ELSE}WriteLn('no-foo'){$ENDIF};
      {$IFNDEF BAR}WriteLn('no-bar'){$ENDIF};
      {$IFDEF CPUX86_64}
        {$IFDEF BLAISE}WriteLn('cpu-blaise'){$ENDIF}
      {$ENDIF}
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'no-foo' + LE + 'no-bar' + LE + 'cpu-blaise' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_Const_LargeHex_NotTruncated;
const
  { $080808080808 = 8830587504648, needs 64 bits — must not truncate to 32. }
  Src = '''
    program P;
    const DECI = $080808080808;
    begin WriteLn(DECI) end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '8830587504648' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_Const_Int64BitPattern;
const
  { $8080808080808080 as Int64 is the bit pattern -9187201950435737472. }
  Src = '''
    program P;
    const A: Int64 = $8080808080808080;
    begin WriteLn(A) end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '-9187201950435737472' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_Const_UInt64BitPattern;
const
  { Same bits as UInt64 = 9259542123273814144. }
  Src = '''
    program P;
    const A: UInt64 = $8080808080808080;
    begin WriteLn(A) end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '9259542123273814144' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_Const_UntypedAboveInt64_IsUInt64;
const
  { An untyped literal above High(Int64) types as UInt64 (matches Delphi). }
  Src = '''
    program P;
    const A = $8080808080808080;
    begin WriteLn(A) end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '9259542123273814144' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_ArrayConst_Int64BitPattern;
const
  { A sign-bit hex literal is a valid Int64 bit pattern inside an array
    const, matching the scalar typed-const rule from issue #133.  This is
    the issue #159 regression case: the array-const fold used the strict
    ParseIntLiteral and rejected $8080808080808080. }
  Src = '''
    program P;
    const B: array[0..1] of Int64 = (
      $4040404040404040,
      $8080808080808080
    );
    begin
      WriteLn(B[0]);
      WriteLn(B[1])
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '4629771061636907072' + LE + '-9187201950435737472' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_Forward_MutualRecursion;
const
  { Mutually-recursive routines via a forward; declaration in the program's
    decl section.  Asserts the recursion actually computes parity, not just
    that it compiles. }
  Src = '''
    program P;
    function IsEven(n: Integer): Boolean; forward;
    function IsOdd(n: Integer): Boolean;
    begin if n = 0 then Result := False else Result := IsEven(n - 1) end;
    function IsEven(n: Integer): Boolean;
    begin if n = 0 then Result := True else Result := IsOdd(n - 1) end;
    begin
      WriteLn(IsEven(10), ' ', IsEven(7), ' ', IsOdd(7), ' ', IsOdd(4))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'True False True False' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_SiblingNestedCall_ForwardsCaptures;
const
  Src = '''
    program p;
    procedure Run;
    var
      Total: Integer;
      procedure Bump;
      begin
        Total := Total + 5
      end;
      procedure Twice;   { captures nothing itself — calls the sibling }
      begin
        Bump();
        Bump()
      end;
    begin
      Total := 1;
      Twice();
      WriteLn(Total)
    end;
    begin
      Run()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '11' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_SiblingNestedCall_ForwardsSelfCapture;
const
  Src = '''
    program p;
    type
      TBox = class
      public
        FVal: Integer;
        procedure Grow;
      end;
    procedure TBox.Grow;
      procedure Inc1;
      begin
        FVal := FVal + 1   { captures Self }
      end;
      procedure Inc3;      { no Self reference of its own }
      begin
        Inc1();
        Inc1();
        Inc1()
      end;
    begin
      Inc3()
    end;
    var B: TBox;
    begin
      B := TBox.Create();
      B.FVal := 4;
      B.Grow();
      WriteLn(B.FVal)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '7' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_IncDec_WideTarget_NarrowStep;
const
  Src = '''
    program Prg;
    type TProc = reference to procedure;
    function StepL(): Int64; begin Result := 3000000000 end;
    var
      V: Int64;
      S: Integer;
      A: array[0..1] of Int64;
      N: Integer;
      U: UInt32;
      Pr: TProc;
    begin
      V := 5000000000; S := 1000000000;
      Inc(V, S);              { stack-slot local, Int64 target + Integer step }
      WriteLn(V);             { 6000000000 }
      S := -2000000000;
      Dec(V, S);              { Dec with negative Integer step -> +2e9 = 8e9 }
      WriteLn(V);             { 8000000000 }
      V := 1000000000;
      Inc(V, StepL());        { Int64 step still works }
      WriteLn(V);             { 4000000000 }
      A[1] := 5000000000; S := 1000000000;
      Inc(A[1], S);           { address-based arm, Int64 element + Integer step }
      WriteLn(A[1]);          { 6000000000 }
      V := 5000000000; N := 7;
      Pr := procedure begin Inc(V, N) end;  { captured Int64 V + Integer step }
      Pr();
      WriteLn(V);             { 5000000007 }
      V := 1000000000; U := 3000000000;
      Inc(V, U);              { UInt32 step with high bit set: must ZERO-extend }
      WriteLn(V);             { 4000000000 (extsw would give -294967296) }
      Dec(V, U);
      WriteLn(V)              { 1000000000 }
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '6000000000' + LE + '8000000000' + LE + '4000000000' + LE +
    '6000000000' + LE + '5000000007' + LE + '4000000000' + LE + '1000000000' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_BitOpsInFloatConstExpr;
var LE: string;
begin
  { GH #195: `1.0 / (UInt64(1) shl 53)` was rejected outright.  The value is
    the classic 2^-53 machine epsilon, and it is the reason the shift MUST
    fold in Int64: a Double cannot represent 2^53 + 1, so folding the shift in
    floating point would silently give the wrong constant.  Asserting the
    printed value end to end is what pins that. }
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  LE := LineEnding;
  AssertRunsOnAll('''
    program P;
    const
      Eps  = 1.0 / (UInt64(1) shl 53);
      Frac = 1.0 / (1024 shr 2);
    begin
      WriteLn(Eps);
      WriteLn(Frac)
    end.
    ''', '1.11022302462516e-16' + LE + '0.00390625' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_FloatArg_ConvertsToParamType;
const
  {
    A float argument is converted to its PARAMETER's precision, whatever the
    argument's own type: a double literal to a Single parameter is narrowed, a
    Single variable to a Double parameter is widened.  arm64 chose the register
    class from the argument, so the callee read half a double (0) or a
    single-precision bit pattern as a double (5.3e-315). }
  Src = '''
    program P;
    procedure One(S: Single);
    begin
      WriteLn(SingleToStr(S))
    end;
    procedure Dbl(D: Double);
    begin
      WriteLn(DoubleToStr(D))
    end;
    procedure Both(D: Double; S: Single);
    begin
      WriteLn(DoubleToStr(D), ' ', SingleToStr(S))
    end;
    var X: Single; Y: Double;
    begin
      X := 2.5;
      Y := 0.75;
      One(1.5);
      One(X);
      One(Y);
      Dbl(X);
      Dbl(3.25);
      Both(X, 1.5);
      Both(Y, Y)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '1.5' + LE +
    '2.5' + LE +
    '0.75' + LE +
    '2.5' + LE +
    '3.25' + LE +
    '2.5 1.5' + LE +
    '0.75 0.75' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_WriteLn_UInt64_HighBit_Unsigned;
const
  {
    WriteLn of a UInt64 with the high bit set prints it unsigned.  arm64 fell
    through to the signed Integer writer: 2^63 printed as -9223372036854775808.
    Includes a sar result, which keeps the UInt64 type (arithmetic shift of the
    bit pattern, as on x86-64 and QBE). }
  Src = '''
    program P;
    var U, V: UInt64;
    begin
      U := 1;
      U := U shl 63;
      WriteLn(U);
      WriteLn(U or 1);
      V := U sar 1;
      WriteLn(V);
      WriteLn(U shr 1);
      Write(U);
      WriteLn('')
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '9223372036854775808' + LE +
    '9223372036854775809' + LE +
    '13835058055282163712' + LE +
    '4611686018427387904' + LE +
    '9223372036854775808' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_BooleanOps_ShortCircuitAndNot;
const
  {
    and / or short-circuit: the right operand is not evaluated when the left
    decides the result (Calls counts evaluations).  not on a Boolean is logical,
    on an Integer bitwise; xor on Booleans.  Replaces the QBE IR checks in
    cp.test.booleanops. }
  Src = '''
    program P;
    var Calls: Integer;
    function T(V: Boolean): Boolean;
    begin
      Calls := Calls + 1;
      Result := V
    end;
    var A, B: Boolean; I: Integer;
    begin
      Calls := 0;
      A := T(False) and T(True);
      WriteLn(A, ' ', Calls);
      Calls := 0;
      A := T(True) or T(False);
      WriteLn(A, ' ', Calls);
      Calls := 0;
      A := T(True) and T(False);
      WriteLn(A, ' ', Calls);
      B := True;
      WriteLn(not B, ' ', not A);
      I := 5;
      WriteLn(not I);
      WriteLn(B xor A, ' ', B xor B)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'False 1' + LE +
    'True 1' + LE +
    'False 2' + LE +
    'False True' + LE +
    '-6' + LE +
    'True False' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_Write_MultiArg_NewlineRules;
const
  {
    WriteLn writes every argument with no separator and one trailing newline;
    Write writes no newline; strings and Integers mix; an empty WriteLn writes
    just the newline.  Replaces the QBE IR checks in cp.test.multiwrite. }
  Src = '''
    program P;
    var I, J: Integer; S: string;
    begin
      I := 1;
      J := 2;
      S := 'hi';
      WriteLn(I, J);
      WriteLn(I, J, 3);
      Write(I, J);
      Write('|');
      WriteLn();
      WriteLn(S, I);
      WriteLn()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '12' + LE +
    '123' + LE +
    '12|' + LE +
    'hi1' + LE +
    '' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_Routines_CallsAndResults;
const
  {
    Standalone procedures and functions and methods are called with their
    arguments, and a function's Result reaches the caller.  Replaces the QBE IR
    checks in cp.test.procs and cp.test.functions; float parameters are covered
    by TestRun_FloatArg_ConvertsToParamType. }
  Src = '''
    program P;
    type
      TBox = class
        Value: Integer;
        procedure SetValue(AVal: Integer);
        function GetValue: Integer;
      end;
    procedure TBox.SetValue(AVal: Integer);
    begin
      Self.Value := AVal
    end;
    function TBox.GetValue: Integer;
    begin
      Result := Self.Value
    end;
    procedure PrintIt(X: Integer);
    begin
      WriteLn('print ', X)
    end;
    function Add(A, B: Integer): Integer;
    var Tmp: Integer;
    begin
      Tmp := A + B;
      Result := Tmp
    end;
    var Bx: TBox;
    begin
      Bx := TBox.Create();
      Bx.SetValue(42);
      WriteLn('box ', Bx.GetValue());
      PrintIt(7);
      WriteLn('add ', Add(3, -4))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'box 42' + LE +
    'print 7' + LE +
    'add -1' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_NestedRoutines_ScopeAndCapture;
const
  {
    A nested routine updates its enclosing routine's local through the capture;
    same-named nested functions in two routines, or in two methods, each resolve
    to their own scope.  Replaces the QBE IR checks in cp.test.procs. }
  Src = '''
    program P;
    type
      TFoo = class
        procedure MethodA;
        procedure MethodB;
      end;
    procedure Outer;
    var X: Integer;
      procedure Inner;
      begin
        X := X + 1
      end;
    begin
      X := 0;
      Inner();
      Inner();
      WriteLn('captured ', X)
    end;
    procedure OuterA;
      function Helper(X: Integer): Integer;
      begin
        Result := X + 1
      end;
    begin
      WriteLn('A ', Helper(10))
    end;
    procedure OuterB;
      function Helper(X: Integer): Integer;
      begin
        Result := X + 2
      end;
    begin
      WriteLn('B ', Helper(20))
    end;
    procedure TFoo.MethodA;
      function Helper(X: Integer): Integer;
      begin
        Result := X + 3
      end;
    begin
      WriteLn('MA ', Helper(30))
    end;
    procedure TFoo.MethodB;
      function Helper(X: Integer): Integer;
      begin
        Result := X + 4
      end;
    begin
      WriteLn('MB ', Helper(40))
    end;
    var F: TFoo;
    begin
      Outer();
      OuterA();
      OuterB();
      F := TFoo.Create;
      F.MethodA();
      F.MethodB()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'captured 2' + LE +
    'A 11' + LE +
    'B 22' + LE +
    'MA 33' + LE +
    'MB 44' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_File_BinaryRoundTrip;
const
  {
    WriteFile, AppendFile and ReadFile keep every byte, NULs included.  The
    posix RTL passed paths and content through string(PChar(...)), a conversion
    that copies up to the first NUL: ReadFile of a 7-byte file holding a NUL
    returned 2 bytes, and WriteFile truncated binary content the same way. }
  Src = '''
    program P;
    var Path, S: string;
    begin
      Path := GetTempDir() + 'blaise_binrt.dat';
      WriteFile(Path, 'ab' + #0 + 'cd');
      S := ReadFile(Path);
      WriteLn(Length(S), ' ', Ord(S[2]), ' ', S[4]);
      AppendFile(Path, #0 + 'z');
      S := ReadFile(Path);
      WriteLn(Length(S), ' ', S[6]);
      WriteLn(FileExists(Path));
      DeleteFile(Path);
      WriteLn(FileExists(Path))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '5 0 100' + LE +
    '7 122' + LE +
    'True' + LE +
    'False' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_PChar_StringRoundTrip;
const
  {
    string(p) on a PChar copies the NUL-terminated bytes into a new string;
    PChar(s) hands back the string's own NUL-terminated data.  arm64 treated
    string(p) as a no-op cast and retained the raw PChar as if it were a string,
    so the runtime read a header that was not there ("_StringRelease corrupted
    header").  Bytes stored through p[i] -- a Chr(N) call, a char literal, #0 --
    land as single bytes. }
  Src = '''
    program P;
    function Echo(s: string): string;
    var p: PChar;
    begin
      p := PChar(s);
      Result := string(p)
    end;
    var Buf: PChar; S: string;
    begin
      WriteLn(Echo('round trip'));
      Buf := GetMem(8);
      Buf[0] := Chr(65);
      Buf[1] := 'B';
      Buf[2] := #0;
      Buf[3] := 'Z';
      S := string(Buf);
      WriteLn(Length(S), ' ', S);
      WriteLn('[', string(Buf), ']');
      FreeMem(Buf)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'round trip' + LE +
    '2 AB' + LE +
    '[AB]' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_IntToStr_FollowsSignedness;
const
  {
    IntToStr formats every integer type by its own signedness: a UInt64 with the
    high bit set stays positive, a Cardinal above 2^31 keeps its magnitude, a
    negative Int64 or Integer keeps its sign.  arm64 sent every argument to
    _Int64ToStr, so 2^63 came back as -9223372036854775808. }
  Src = '''
    program P;
    var U: UInt64; C: Cardinal; N: Int64; I: Integer;
    begin
      U := 1;
      U := U shl 63;
      WriteLn(IntToStr(U));
      WriteLn(IntToStr(U + 5));
      C := 4000000000;
      WriteLn(IntToStr(C));
      N := -9000000000;
      WriteLn(IntToStr(N));
      I := -7;
      WriteLn(IntToStr(I))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '9223372036854775808' + LE +
    '9223372036854775813' + LE +
    '4000000000' + LE +
    '-9000000000' + LE +
    '-7' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_DefaultArgs_Materialised;
const
  {
    An omitted default argument is passed as its declared value: for a method
    call, an implicit-Self call, a standalone procedure, and a default in the
    7th integer slot (passed on the stack on x86-64).  Replaces the QBE IR checks
    in cp.test.defaultargs. }
  Src = '''
    program P;
    type
      TFoo = class
      public
        procedure M(A: Integer; B: Integer = 4242);
        procedure M7(A, B, C, D, E: Integer; F: Integer = 7777);
        procedure Caller;
      end;
    procedure TFoo.M(A: Integer; B: Integer = 4242);
    begin
      WriteLn(A + B)
    end;
    procedure TFoo.M7(A, B, C, D, E: Integer; F: Integer = 7777);
    begin
      WriteLn(A + B + C + D + E, ' ', F)
    end;
    procedure TFoo.Caller;
    begin
      M(2)
    end;
    procedure Q(A: Integer; B: Integer = 6363);
    begin
      WriteLn(A + B)
    end;
    var F: TFoo;
    begin
      F := TFoo.Create();
      F.M(1);
      F.M(1, 2);
      F.M7(1, 2, 3, 4, 5);
      F.Caller();
      Q(1)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '4243' + LE +
    '3' + LE +
    '15 7777' + LE +
    '4244' + LE +
    '6364' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_ChainedFields_ReadThroughEveryLevel;
const
  {
    A chained field read goes through every level: record-in-record, and an
    implicit-Self class chain used as a for-loop bound.  Replaces the QBE IR
    checks in cp.test.chainedfields. }
  Src = '''
    program P;
    type
      TInner = record Value: Integer; end;
      TOuter = record Inner: TInner; end;
      TLeaf = class Value: Integer; end;
      TMid = class Leaf: TLeaf; end;
      TTop = class
        FInner: TMid;
        function Work: Integer;
      end;
    function TTop.Work: Integer;
    var I, K: Integer;
    begin
      K := 0;
      for I := 0 to FInner.Leaf.Value - 1 do
        K := K + 1;
      Result := K
    end;
    var O: TOuter; T: TTop;
    begin
      O.Inner.Value := 17;
      WriteLn(O.Inner.Value);
      T := TTop.Create();
      T.FInner := TMid.Create();
      T.FInner.Leaf := TLeaf.Create();
      T.FInner.Leaf.Value := 4;
      WriteLn(T.Work())
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '17' + LE +
    '4' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_HighLow_OrdinalBounds;
const
  {
    High and Low of every ordinal type fold to the type's bounds, for a type name
    and for a variable of that type alike, and each bound survives the store into
    a variable of that type (a truncated or sign-extended fold would print wrongly). }
  Src = '''
    program P;
    type TColour = (Red, Green, Blue);
    var
      N, X: Integer; B: Byte; W: Word; S: SmallInt; Bo: Boolean;
      U: UInt32; Q: Int64; UQ: UInt64;
    begin
      N := High(Integer); Write(N, ' ');
      N := Low(Integer); WriteLn(N);
      B := High(Byte); Write(B, ' ');
      B := Low(Byte); WriteLn(B);
      W := High(Word); Write(W, ' ');
      S := High(SmallInt); Write(S, ' ');
      S := Low(SmallInt); WriteLn(S);
      Bo := High(Boolean); Write(Bo, ' ');
      Bo := Low(Boolean); WriteLn(Bo);
      U := High(UInt32); WriteLn(U);
      Q := High(Int64); WriteLn(Q);
      UQ := High(UInt64); WriteLn(UQ);
      N := Ord(High(TColour)); Write(N, ' ');
      N := Ord(Low(TColour)); WriteLn(N);
      N := High(X); Write(N, ' ');
      B := High(B); Write(B, ' ');
      Q := High(Q); WriteLn(Q)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '2147483647 -2147483648' + LE +
    '255 0' + LE +
    '65535 32767 -32768' + LE +
    'True False' + LE +
    '4294967295' + LE +
    '9223372036854775807' + LE +
    '18446744073709551615' + LE +
    '2 0' + LE +
    '2147483647 255 9223372036854775807' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_SelfHostingRTLServices;
const
  {
    The RTL services the compiler itself is built on, as one program: command-line
    access, file read / write / existence / age, the environment, running a shell
    command, the path helpers, MaxInt as Copy's "rest of the string", classes
    declared in separate type sections, and Halt's exit code. }
  Src = '''
    program P;
    type
      TA = class
        FX: Integer;
      end;
    type
      TB = class
        FY: Integer;
      end;
    var
      Path, S: string; A: TA; B: TB; Age: Int64;
    begin
      WriteLn(ParamCount(), ' ', ParamStr(0) <> '');
      Path := GetTempDir() + 'blaise_e2e_selfhost.txt';
      WriteFile(Path, 'hello');
      WriteLn(FileExists(Path), ' ', ReadFile(Path));
      Age := FileAge(Path);
      WriteLn(Age > 0, ' ', FileAge(Path + '.missing'));
      DeleteFile(Path);
      WriteLn(FileExists(Path));
      WriteLn(GetEnvVar('PATH') <> '', ' ', GetEnvironmentVariable('PATH') = GetEnvVar('PATH'));
      WriteLn(Exec('true'), ' ', Exec('false') <> 0);
      WriteLn(ChangeFileExt('test.pas', '.bak'), ' ', ExtractFileName('/usr/bin/ls'), ' ',
        ExtractFilePath('/usr/bin/ls'), ' ', IncludeTrailingPathDelimiter('/usr/bin'));
      S := 'abcdef';
      WriteLn(MaxInt, ' ', Copy(S, 2, MaxInt));
      A := TA.Create();
      B := TB.Create();
      WriteLn(A.ClassName, ' ', B.ClassName);
      Halt(3)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '0 True' + LE +
    'True hello' + LE +
    'True -1' + LE +
    'False' + LE +
    'True True' + LE +
    '0 True' + LE +
    'test.bak ls /usr/bin/ /usr/bin/' + LE +
    '2147483647 cdef' + LE +
    'TA TB' + LE, 3);
end;

procedure TE2EMiscTests.TestRun_ProcTypes_IndirectCallShapes;
const
  {
    Indirect calls through every procedural-value shape: a routine address in a
    procedural variable, a procedural field called qualified and with implicit
    Self, a closure field called with implicit Self (its environment must travel
    as the hidden first argument), closure and plain procedural fields in a global
    and a local record (addressed off the record itself, behind a leading member),
    in statement and expression form, and an open-array argument through a
    procedural variable (data pointer plus high bound). }
  Src = '''
    program P;
    type
      TIntFn = function: Integer;
      TStrFn = function(const S: string): Integer;
      TRun = reference to procedure(N: Integer);
      TCnt = function(const A: array of Integer): Integer;
      TInts = array of Integer;
      TBox = class
      public
        FFn: TStrFn;
        FRun: TRun;
        function RunQualified(const S: string): Integer;
        function RunImplicit(const S: string): Integer;
        procedure Drv();
      end;
      TClo = reference to procedure;
      TCloFn = reference to function(A: Integer): Integer;
      TPlain = procedure;
      TR = record
        Pad: Int64;
        F: TClo;
        G: TCloFn;
        H: TPlain;
      end;
    function MyFn: Integer;
    begin
      Result := 42
    end;
    function StrLen(const S: string): Integer;
    begin
      Result := Length(S)
    end;
    function Cnt(const A: array of Integer): Integer;
    var I: Integer;
    begin
      Result := 0;
      for I := 0 to High(A) do
        Result := Result * 10 + A[I]
    end;
    procedure Plain;
    begin
      WriteLn('plain')
    end;
    function TBox.RunQualified(const S: string): Integer;
    begin
      Result := Self.FFn(S)
    end;
    function TBox.RunImplicit(const S: string): Integer;
    begin
      Result := FFn(S)
    end;
    procedure TBox.Drv();
    begin
      FRun(7)
    end;
    procedure Take(F: TCnt; const D: TInts);
    begin
      WriteLn(F(D))
    end;
    procedure LocalRec;
    var R: TR;
    begin
      R.Pad := 5;
      R.F := procedure begin WriteLn('local closure') end;
      R.F()
    end;
    var
      F: TIntFn; B: TBox; R: TR; Base: Integer; D: TInts;
    begin
      F := @MyFn;
      WriteLn(F());
      B := TBox.Create();
      B.FFn := @StrLen;
      WriteLn(B.RunQualified('abc'), ' ', B.RunImplicit('hello'));
      Base := 100;
      B.FRun := procedure(N: Integer) begin WriteLn('run ', Base + N) end;
      B.Drv();
      R.Pad := 9;
      R.F := procedure begin WriteLn('global closure') end;
      R.G := function(A: Integer): Integer begin Result := A * Base end;
      R.H := @Plain;
      R.F();
      WriteLn(R.G(5));
      R.H();
      LocalRec();
      SetLength(D, 3);
      D[0] := 1; D[1] := 2; D[2] := 3;
      Take(@Cnt, D);
      B.Free()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '42' + LE +
    '3 5' + LE +
    'run 107' + LE +
    'global closure' + LE +
    '500' + LE +
    'plain' + LE +
    'local closure' + LE +
    '123' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_IndirectFuncCallExpr_Shapes;
const
  {
    Calling the procedure pointer an EXPRESSION yields -- an array element, a
    function result -- for Integer, Double and string results and an open-array
    argument.  arm64 had no lowering for this node at all. }
  Src = '''
    program P;
    type
      TIntFn = function: Integer;
      TDblFn = function(X: Double): Double;
      TStrFn = function(const S: string): string;
      TCnt = function(const A: array of Integer): Integer;
    function One: Integer; begin Result := 1 end;
    function Two: Integer; begin Result := 2 end;
    function Half(X: Double): Double; begin Result := X / 2 end;
    function Shout(const S: string): string; begin Result := S + '!' end;
    function Cnt(const A: array of Integer): Integer; begin Result := Length(A) end;
    function PickDbl: TDblFn; begin Result := @Half end;
    function PickStr: TStrFn; begin Result := @Shout end;
    var
      Fns: array[0..1] of TIntFn; Cs: array[0..0] of TCnt; I, Sum: Integer;
      D: array of Integer; S: string;
    begin
      Fns[0] := @One;
      Fns[1] := @Two;
      Sum := 0;
      for I := 0 to 1 do
        Sum := Sum + Fns[I]() * 10;
      WriteLn(Sum);
      WriteLn(PickDbl()(5.0):0:2);
      S := PickStr()('hi' + 'gh');
      WriteLn(S);
      SetLength(D, 4);
      Cs[0] := @Cnt;
      WriteLn(Cs[0](D), ' ', Cs[0]([7, 8]))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '30' + LE +
    '2.50' + LE +
    'high!' + LE +
    '4 2' + LE, 0);
  AssertLeakFreeOnAll(Src, 'high!');
end;

initialization
  RegisterTest(TE2EMiscTests);

end.

