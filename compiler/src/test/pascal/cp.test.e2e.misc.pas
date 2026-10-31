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
    { Exit(X) in a nested routine reading the enclosing routine's record:
      x86-64 linked a symbol named after the variable and crashed, arm64
      refused it }
    procedure TestRun_NestedExitReadsCapturedRecord;
    { a const array of an aliased element type (Int16, UInt16, QWord, a user
      alias) stores and reads back elements at the type's true width }
    procedure TestRun_ConstArray_AliasElementWidths;
    { a program's overloaded forward declarations pair with their bodies:
      an earlier routine calls each overload before its body appears }
    procedure TestRun_ProgramOverloadForward_CallsEachBody;
    { statements whose chain continues past a field element: field writes,
      nested-row element writes and calls through procedural elements }
    procedure TestRun_ChainPastFieldElement;
    { procedural calls with interface, float and >6-slot arguments;
      interface-call results into >6-slot calls }
    procedure TestRun_ProcCalls_InterfaceAndFloatArgs;
    procedure TestRun_ProcFieldCalls_AllForms;
    procedure TestRun_IntfResultArg_PastRegisters;
    { more captured variables than the integer registers hold, forwarded
      on through a deeper nested routine }
    procedure TestRun_NestedProc_CapturesSpillPastRegisters;
    procedure TestRun_CodegenBasics_Combined;
    procedure TestRun_Constants_Arrays;
    procedure TestRun_Constants_Scalar;
    procedure TestRun_IndirectFuncCallExpr_Shapes;
    procedure TestRun_ProcTypes_IndirectCallShapes;
    { BUG-20261013-proctype-inline-param-types: a named procedural type whose
      parameter or return type is ^T, set of T or array of T, called through }
    procedure TestRun_ProcTypes_InlineParamAndReturnTypes;
    { GH #222: an inline procedural type in a var declaration (global, local,
      record field, of object, reference to) holds and calls the routine }
    procedure TestRun_InlineProcTypes_AllPositions;
    { GH #222 as reported (Coco/R's CRS unit): an inline procedural type on a
      unit INTERFACE var, assigned and called from the program -- the type
      survives the unit's cached interface }
    procedure TestRun_InlineProcType_UnitInterfaceVar;
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
    { a float method called on implicit Self where a float (or its truncation)
      is wanted: plain, virtual-override-through-inherited, and Single }
    procedure TestRun_ImplicitSelfFloatCall_AllForms;
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
    { Identifier-led constant values -- alias, arithmetic, enum member,
      Ord, string concat, float alias, typed enum, member-const alias --
      fold by type (BUG-20261015-const-ident-rhs-typed-string). }
    procedure TestRun_Const_IdentLedValues;
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
    { FInner.FP(7); as a statement inside a method, FInner a field of Self
      and FP a procedural field of its class -- plain, 'reference to' and
      'of object' (BUG-20260923-implicit-field-procfield-stmt: "Class
      'TInner' has no method 'FP'") }
    procedure TestRun_ImplicitFieldProcField_Stmt;
    { a call through a procedural field of a receiver a call returned, or
      an array element, as a statement and in an expression: the receiver
      lives through the call and is freed at the statement end }
    procedure TestRun_ProcFieldCall_OnCallResultReceiver;
    { calls through field-backed properties of procedural type -- 'of
      object', plain and 'reference to' -- inside the class, from a nested
      routine, through a receiver and a chained receiver, statement and
      expression, the property inherited (all were "no method 'OnChange'") }
    procedure TestRun_CallThroughProcProperty;
    { calls through GETTER-backed properties of procedural type -- plain,
      'of object' and 'reference to' -- through a variable, a call result,
      Self and a field of Self, statement and expression; the closure the
      getter returns is released after each call
      (BUG-20261020-getter-proc-property-call) }
    procedure TestRun_CallThroughGetterProcProperty;

    { Default parameters }
    procedure TestRun_DefaultParam_OmitLast;
    procedure TestRun_DefaultParam_OmitMultiple;
    { a function method through a receiver (Self.F(1), X.F(1)), a generic
      method and inherited calls take their omitted trailing arguments from
      the declared defaults (they failed to compile) }
    procedure TestRun_DefaultParam_MethodCallForms;
    { macOS: a program binding a C library (external 'z') links with the
      internal Mach-O linker and runs -- the library gets its own
      LC_LOAD_DYLIB and its imports its ordinal.  Every import used to be
      bound to libSystem, and dyld aborted at launch ("Symbol not found:
      _zlibVersion").  A library that cannot be found is a link error naming
      the search path, not a launch-time abort. }
    procedure TestRun_MacOS_ExternalCLibrary_InternalLinker;
    { libSystem imports are checked against the SDK's real export list: a
      real function links silently, a mis-spelt one fails the link }
    procedure TestRun_MacOS_LibSystemImports_CheckedAgainstSdk;

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
    { every by-reference form on a captured variable, one and two levels
      down: field reads/writes, @R.N, @R.A[I], @I, @A[I], Inc(I), var
      arguments, string append -- on var params, by-value params and
      locals.  arm64 lowered almost none of it on a record (NotYet, or a
      segfault reading a by-value record's first word as its address);
      x86-64 crashed on @R.N, @I, Inc(I), S := S + 'x', BumpR(R) and a
      by-value array element write }
    procedure TestRun_NestedProc_CapturedByRefForms;
    { SetLength on every l-value form: a Self field, Self.R.D, a var param, a
      var record param's field, a capture, a capture's field, an object's
      field, an array element (static and dyn), P^ and P^.F (arm64 refused
      a string field of Self, a capture and P^; x86-64 refused P^ and wrote a
      captured one through an undefined global) }
    procedure TestRun_SetLength_AllLValueForms;
    { a nested routine calling a captured method pointer / closure / var
      procedural param, and indexing / resizing captured dyn arrays and
      strings (both ISAs: not captured at all, or called through a slot the
      frame did not have; x86-64 wrote through undefined globals) }
    procedure TestRun_NestedProc_ProcVarsAndDynArrays;
    { R.M() / R.F() / R.C() / R.Sum() with R a record field of Self (were
      rejected); arm64 read a Single Self field as 0.0 and refused a var
      Single param }
    procedure TestRun_SelfRecordFieldCalls_AndSingles;
    { M[I] := D / S[I] := D then dropping D: the element still owns the block
      (x86-64 read the freed, reused block); X := O.A[I] for an array field
      of Doubles / Singles (x86-64 read the field's first bytes, and refused
      a float literal store into R.A[I]); K = nil / Assigned on closures and
      method pointers, fields and elements included (x86-64 always False /
      True) }
    procedure TestRun_DynArrayElements_FloatFieldElements_FatNilTests;
    { interfaces in nested routines and through var params: a captured local,
      a captured var param and a captured by-value param read, assigned and
      passed on, two levels down (arm64 refused them; x86-64 dropped every
      assignment and crashed passing a var interface param on) }
    procedure TestRun_CapturedAndVarInterfaces;
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
    { GH #235 — scripts/build-rtl-objects.sh --exclude-defined-by, run in a
      collating locale, prints only object paths and picks the same objects
      as in the C locale.  On Ubuntu 26.04 (uutils comm) it printed comm's
      sort-order warnings, which the harness passed to the linker. }
    procedure TestBuildRtlObjects_CollatingLocale_PrintsOnlyObjects;
    procedure TestRun_TestRunner_HelpAndRejectedOptions;
    { GH #224: statements through a pointer element of an array -- an
      element of the array it points at, the whole pointee, a field of a
      record it points at -- written and read back }
    procedure TestRun_DerefAfterSubscript_Statements;
    { A class method in a unit calling through a function result,
      GetFn()(40, 2): the compiler clones such bodies, and CloneExpr had no
      case for TIndirectFuncCallExpr ("CloneExpr: unhandled expression node
      TIndirectFuncCallExpr"). }
    procedure TestRun_IndirectCallInUnitClassMethod_Clones;
    { A set-constant parameter default -- [], members, a range of a
      named-constant bound -- on a routine and a method; it was rejected
      ("must be a literal or named constant"). }
    procedure TestRun_SetConstantParamDefault;
    { ...and declared in a unit's interface, used from a program. }
    procedure TestRun_SetConstantParamDefault_InUnit;
  end;

implementation

uses
  classes, sysutils, blaise.codegen.target;

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
    var I, J, K: Int;
    begin
      I := 1; J := 2; K := 3;
      WriteLn(I, J, K)
    end.
    ''';

  SrcForBreak = '''
    program Prg;
    var I, Last: Int;
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
    function FirstPositive(X: Int): Int;
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
      TInner = record Value: Int; end;
      TOuter = record I: TInner; end;
    var O: TOuter; N: Int;
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
      TInner = record Arr: array[0..3] of Int; end;
      TOuter = record Ora: array[0..1] of TInner; end;
    var O: TOuter; x, c: Int;
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
    var X: Int;
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
    var X: Int;
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
    function DaysInMonth(M: Int): Int;
    const
      Days: array[1..12] of Int32 = (31,28,31,30,31,30,31,31,30,31,30,31);
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
    type TFn = function(X: Int): Int;
    function Twice(X: Int): Int;
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
        FVal: Int;
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
      TFn = function(const S: string): Int;
      TBox = class
        FFn: TFn;
        function Run(const S: string): Int;
      end;
    function Len2(const S: string): Int;
    begin Result := Length(S) end;
    function TBox.Run(const S: string): Int;
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
      TFn = function(A, B, C: Int): Int;
      TBox = class
        FFn: TFn;
        function Run(X: Int): Int;
      end;
    function Sum3(A, B, C: Int): Int;
    begin Result := A + B + C end;
    function TBox.Run(X: Int): Int;
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
    type TBinOp = function(X, Y: Int): Int of object;
    type
      TCalc = class
        function Add(X, Y: Int): Int;
        function GetOp: TBinOp;
      end;
    function TCalc.Add(X, Y: Int): Int;
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
    type TFn = function(X: Int): Int of object;
    type
      TCalc = class
        Base: Int;
        FStored: TFn;
        function AddBase(X: Int): Int;
        function GetFn: TFn;
        procedure StoreFn;
        function CallStored(X: Int): Int;
      end;
    function TCalc.AddBase(X: Int): Int;
    begin Result := Self.Base + X end;
    function TCalc.GetFn: TFn;
    begin Result := @Self.AddBase end;
    procedure TCalc.StoreFn;
    begin Self.FStored := Self.GetFn() end;
    function TCalc.CallStored(X: Int): Int;
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
      TFn = function(A, B, C: Int): Int;
      TBox = class
        FFn: TFn;
        function Run(X: Int): Int;
      end;
    function Sum3(A, B, C: Int): Int;
    begin Result := A + B + C end;
    function TBox.Run(X: Int): Int;
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
    function Add(A: Int; B: Int = 10): Int;
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
    procedure Swap(var A, B: Int);
    var T: Int;
    begin
      T := A; A := B; B := T
    end;
    var X, Y: Int;
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
    function Twice(const X: Int): Int;
    begin Result := X * 2 end;
    begin
      WriteLn(Twice(21))
    end.
    ''';

  SrcTypeCastIntByte = '''
    program Prg;
    var I: Int; B: Byte;
    begin
      I := 300;
      B := Byte(I);
      WriteLn(B)
    end.
    ''';

  SrcTypeCastPointerInt = '''
    program Prg;
    var I: Int; P1: Pointer;
    begin
      I  := 42;
      P1 := Pointer(I);
      WriteLn(Int32(P1))
    end.
    ''';

  { A Cardinal/UInt32 value above 2^31 must print as the large unsigned value,
    not a negative signed wrap.  3000000000 fits in UInt32 but is negative as a
    signed Int32. }
  SrcWriteUnsigned32 = '''
    program Prg;
    var c: UInt32;
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
      I: Int32;
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
      I: Int32;
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
      I: Int32;
    begin
      S := '€X';
      for I in S do
        WriteLn(I)
    end.
    ''';

  SrcForInArrayInteger = '''
    program Prg;
    var
      A: array[0..2] of Int;
      X: Int;
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
        FCurrent: Int;
        FLast: Int;
        constructor Create(AFirst, ALast: Int);
        function MoveNext: Boolean;
        function GetCurrent: Int;
        property Current: Int read GetCurrent;
      end;
      TRange = class
        FFirst: Int;
        FLast: Int;
        constructor Create(AFirst, ALast: Int);
        function GetEnumerator: TRangeEnum;
      end;
    constructor TRangeEnum.Create(AFirst, ALast: Int);
    begin
      FCurrent := AFirst - 1;
      FLast := ALast;
    end;
    function TRangeEnum.MoveNext: Boolean;
    begin
      FCurrent := FCurrent + 1;
      Result := FCurrent <= FLast;
    end;
    function TRangeEnum.GetCurrent: Int;
    begin
      Result := FCurrent;
    end;
    constructor TRange.Create(AFirst, ALast: Int);
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
      N: Int;
    begin
      R := TRange.Create(3, 5);
      for N in R do
        WriteLn(N);
      R.Free();
    end.
    ''';

procedure TE2EMiscTests.TestRun_BooleanOps_AllExpressions;
var Output: string; RCode: Int;
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
var Output: string; RCode: Int;
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
var Output: string; RCode: Int;
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
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcConstStr, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Hello', 'Hello' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_Const_LocalArrayInFunction;
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcConstLocalArrayInFunc, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('Jan Feb Dec days',
    '31' + LE + '28' + LE + '31' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_Const_IdentLedValues;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(
    '''
    program P;
    type
      TE = (eA, eB, eC);
      TC = class
        const M = 3;
        const N = M * 2;
        const Q = M;
      end;
    const
      A = 5;
      B = A;
      C = A + 1;
      F = 2.5;
      G = F;
      S = 'x';
      T = S + 'y' + S;
      KB = True;
      KE = eB;
      KT: TE = eC;
      KO = Ord(eC) + A;
    begin
      WriteLn(B, ' ', B + B, ' ', C);
      WriteLn(G + G:0:2, ' ', T, ' ', KB);
      WriteLn(Ord(KE), ' ', Ord(KT), ' ', KO, ' ', KE = eB);
      WriteLn(TC.N, ' ', TC.Q);
    end.
    ''',
    '5 10 6' + LE + '5.00 xyx True' + LE + '1 2 7 True' + LE + '6 3' + LE, 0);
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
var Output: string; RCode: Int;
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
      TF1 = function(A: Float64): Float64;
      TF9 = function(a, b, c, d, e, f, g, h, i: Float64): Float64;
      TFS = function(A: Float32; N: Int): Int;
    function Dbl(A: Float64): Float64;
    begin
      Result := A * 2.0
    end;
    function Pick(a, b, c, d, e, f, g, h, i: Float64): Float64;
    begin
      Result := i + a
    end;
    function SN(A: Float32; N: Int): Int;
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
      TFm = function(n1, n2, n3: Int; d1: Float64; n4, n5, n6: Int;
                     d2: Float64; n7: Int): Int;
    function M(n1, n2, n3: Int; d1: Float64; n4, n5, n6: Int;
               d2: Float64; n7: Int): Int;
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
      TFh = function(const S: string; a, b, c, d, e: Int; d1: Float64;
                     f, g: Int): Int;
    function H(const S: string; a, b, c, d, e: Int; d1: Float64;
               f, g: Int): Int;
    begin
      Result := Length(S) + a + b*2 + c*3 + d*4 + e*5 +
                Trunc(d1) * 100 + f*6 + g*7
    end;
    var
      PH: TFh;
      S: string;
      R: Int;
    begin
      PH := @H;
      S := 'ab';
      R := PH(S + '!', 1, 2, 3, 4, 5, 2.5, 6, 7);
      WriteLn(R)
    end.
    ''', IntToStr(3 + 1 + 4 + 9 + 16 + 25 + 200 + 36 + 49) + LE, 0);
end;

procedure TE2EMiscTests.TestRun_ProcType_OfObject_Dispatch;
var Output: string; RCode: Int;
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

procedure TE2EMiscTests.TestRun_ImplicitFieldProcField_Stmt;
const
  Src = '''
    program PFS;
    type
      TP = procedure(N: Int);
      TC = reference to procedure(N: Int);
      TM = procedure(N: Int) of object;
      TInner = class
        FP: TP;
        FC: TC;
        FM: TM;
        procedure Show(N: Int);
      end;
      TBox = class
        FInner: TInner;
        procedure Run;
      end;
    procedure TInner.Show(N: Int); begin WriteLn('m ', N); end;
    procedure Plain(N: Int); begin WriteLn('p ', N); end;
    procedure TBox.Run;
    begin
      FInner.FP(7);
      FInner.FC(8);
      FInner.FM(9);
    end;
    var B: TBox;
    begin
      B := TBox.Create(); B.FInner := TInner.Create();
      B.FInner.FP := @Plain; B.FInner.FC := @Plain; B.FInner.FM := @B.FInner.Show;
      B.Run();
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'p 7' + LE + 'p 8' + LE + 'm 9' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_ProcFieldCall_OnCallResultReceiver;
const
  Src = '''
    program R3;
    type
      TP = procedure(N: Int);
      TF = function(N: Int): Int;
      TC = reference to function(N: Int): string;
      THold = class
        FP: TP; FF: TF; FC: TC; Tag: Int;
        destructor Destroy; override;
      end;
    var Sum: Int; Arr: array of THold;
    destructor THold.Destroy; begin WriteLn('hold freed ', Tag); inherited Destroy(); end;
    function MkHold(T: Int): THold;
    begin
      Result := THold.Create(); Result.Tag := T;
      Result.FP := @Plain; Result.FF := @Twice;
      Result.FC := function(N: Int): string begin Result := 'c' + IntToStr(N) end;
    end;
    procedure Plain(N: Int); begin Sum := Sum + N; end;
    function Twice(N: Int): Int; begin Result := N * 2; end;
    begin
      MkHold(1).FP(5);
      WriteLn('after stmt');
      Sum := Sum + MkHold(2).FF(10);
      WriteLn('after expr');
      WriteLn(MkHold(3).FC(7));
      SetLength(Arr, 1); Arr[0] := MkHold(4);
      Arr[0].FP(100);
      WriteLn(Sum);
      SetLength(Arr, 0);
      WriteLn('end');
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'hold freed 1' + LE + 'after stmt' + LE + 'hold freed 2' + LE +
    'after expr' + LE + 'c7' + LE + 'hold freed 3' + LE + '125' + LE +
    'hold freed 4' + LE + 'end' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_CallThroughGetterProcProperty;
const
  Src = '''
    program P;
    type
      TFn = function(X: Int): Int;
      TProc1 = procedure(X: Int);
      TEvent = procedure(X: Int) of object;
      TClo = reference to function(X: Int): Int;
      TTrack = class
        N: Int;
        destructor Destroy; override;
      end;
      TBox = class
        FFn: TFn;
        FProc: TProc1;
        FEv: TEvent;
        FClo: TClo;
        function GetFn: TFn;
        function GetProc: TProc1;
        function GetEv: TEvent;
        function GetClo: TClo;
        property Fn: TFn read GetFn;
        property Proc: TProc1 read GetProc;
        property Ev: TEvent read GetEv;
        property Clo: TClo read GetClo;
        procedure Use;
      end;
      TSink = class
        Total: Int;
        procedure Take(X: Int);
      end;
      THost = class
        FBox: TBox;
        procedure Run;
      end;
    destructor TTrack.Destroy; begin WriteLn('free track ', N); end;
    function TBox.GetFn: TFn; begin Result := FFn; end;
    function TBox.GetProc: TProc1; begin Result := FProc; end;
    function TBox.GetEv: TEvent; begin Result := FEv; end;
    function TBox.GetClo: TClo; begin Result := FClo; end;
    procedure TSink.Take(X: Int); begin Total := Total + X; WriteLn('take ', X, ' total ', Total); end;
    function Dbl(X: Int): Int; begin Result := X * 2; end;
    procedure Shout(X: Int); begin WriteLn('shout ', X); end;
    procedure TBox.Use;
    begin
      WriteLn('use ', Fn(4), ' ', Clo(4));
      Proc(5);
      Ev(6);
    end;
    procedure THost.Run;
    begin
      WriteLn('host ', FBox.Fn(7));
      FBox.Proc(8);
      FBox.Ev(9);
    end;
    var G: TBox;
    function MkB: TBox; begin Result := G; end;
    procedure MakeClo(B: TBox);
    var T: TTrack;
    begin
      T := TTrack.Create;
      T.N := 100;
      B.FClo := function(X: Int): Int begin Result := X + T.N; end;
    end;
    var
      B: TBox;
      S: TSink;
      H: THost;
      I, R: Int;
    begin
      G := TBox.Create;
      B := G;
      S := TSink.Create;
      B.FFn := @Dbl;
      B.FProc := @Shout;
      B.FEv := @S.Take;
      MakeClo(B);
      WriteLn(B.Fn(3), ' ', B.Clo(3), ' ', MkB().Fn(10));
      B.Fn(3);
      B.Proc(1);
      B.Ev(2);
      MkB().Ev(3);
      B.Clo(1);
      R := 0;
      for I := 1 to 1000 do R := R + B.Clo(1);
      WriteLn('sum ', R);
      B.Use();
      H := THost.Create;
      H.FBox := B;
      H.Run();
      B.FClo := nil;
      WriteLn('end');
    end.
    ''';
var
  LE: string;
begin
  LE := LineEnding;
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '6 103 20' + LE +
    'shout 1' + LE +
    'take 2 total 2' + LE +
    'take 3 total 5' + LE +
    'sum 101000' + LE +
    'use 8 104' + LE +
    'shout 5' + LE +
    'take 6 total 11' + LE +
    'host 14' + LE +
    'shout 8' + LE +
    'take 9 total 20' + LE +
    'free track 100' + LE +
    'end' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_CallThroughProcProperty;
const
  Src = '''
    program P;
    type
      TNotify = procedure(Sender: TObject) of object;
      TFn = function(N: Int): Int;
      TC = reference to function(N: Int): Int;
      TBase = class
      private
        FOnChange: TNotify;
        FFn: TFn;
        FC: TC;
      public
        property OnChange: TNotify read FOnChange write FOnChange;
        property Fn: TFn read FFn write FFn;
        property C: TC read FC write FC;
      end;
      TBox = class(TBase)
        Tag: Int;
        procedure Fire;
        procedure Show(Sender: TObject);
      end;
      THolder = class
        Box: TBox;
        procedure Run;
      end;
    procedure TBox.Show(Sender: TObject); begin WriteLn('changed ', TBox(Sender).Tag); end;
    procedure TBox.Fire;
      procedure Inner;
      begin
        OnChange(Self);
      end;
    begin
      if Assigned(OnChange) then OnChange(Self);
      WriteLn(Fn(4), ' ', C(4));
      Inner();
    end;
    procedure THolder.Run;
    begin
      Box.OnChange(Box);
      WriteLn(Box.Fn(6) + Box.C(6));
    end;
    function Twice(N: Int): Int; begin Result := N * 2; end;
    var B: TBox; H: THolder;
    begin
      B := TBox.Create(); B.Tag := 7; B.OnChange := @B.Show; B.Fn := @Twice;
      B.C := function(N: Int): Int begin Result := N + 100 end;
      B.Fire();
      B.OnChange(B);
      WriteLn(B.Fn(5), ' ', B.C(5));
      H := THolder.Create(); H.Box := B;
      H.Run();
      H.Box.OnChange(B);
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'changed 7' + LE + '8 104' + LE + 'changed 7' + LE +
    'changed 7' + LE + '10 105' + LE + 'changed 7' + LE + '118' + LE +
    'changed 7' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_DefaultParam_OmitLast;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(SrcDefaultParam, '15' + LE + '25' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_MacOS_ExternalCLibrary_InternalLinker;
const
  Src = '''
    program P;
    function zlibVersion(): PChar; external 'z' name 'zlibVersion';
    function crc32(Crc: UInt64; Buf: Pointer; Len: UInt32): UInt64;
      external 'z' name 'crc32';
    var S: string;
    begin
      S := 'The quick brown fox jumps over the lazy dog';
      WriteLn(Length(string(zlibVersion())) > 0, ' ',
        crc32(0, PChar(S), Length(S)))
    end.
    ''';
  SrcMissing = '''
    program P;
    procedure nope(); external 'blaisenosuchlib' name 'nope';
    begin
      nope()
    end.
    ''';
var
  BinFile, ToolOut: string;
begin
  if HostTarget().OS <> osMacOS then
  begin
    Ignore('Mach-O dylib binding: macOS only');
    Exit;
  end;
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'True 1095738169' + LineEnding, 0);
  AssertTrue('a missing library fails the link',
    CompileNativeCLI(SrcMissing, False, '', BinFile, ToolOut) <> 0);
  AssertTrue('names the library and the fix: ' + ToolOut,
    (Pos('''blaisenosuchlib'' not found', ToolOut) >= 0) and
    (Pos('--lib-path', ToolOut) >= 0));
end;

procedure TE2EMiscTests.TestRun_MacOS_LibSystemImports_CheckedAgainstSdk;
const
  Src = '''
    program P;
    function kqueue(): Int32; external name 'kqueue';
    function close(Fd: Int32): Int32; external name 'close';
    var Q: Int32;
    begin
      Q := kqueue();
      WriteLn(Q >= 0, ' ', close(Q))
    end.
    ''';
  SrcBad = '''
    program P;
    function kqeueu(): Int32; external name 'kqeueu';
    begin
      WriteLn(kqeueu())
    end.
    ''';
var
  BinFile, ToolOut: string;
begin
  if HostTarget().OS <> osMacOS then
  begin
    Ignore('Mach-O libSystem binding: macOS only');
    Exit;
  end;
  if not FileExists('/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/lib/libSystem.tbd') then
  begin
    Ignore('no macOS SDK text stubs');
    Exit;
  end;
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertEquals('links', 0, CompileNativeCLI(Src, False, '', BinFile, ToolOut));
  AssertTrue('no libSystem note for real functions: ' + ToolOut,
    Pos('macho linker: note', ToolOut) < 0);
  AssertRunsOnAll(Src, 'True 0' + LineEnding, 0);
  AssertTrue('a mis-spelt libSystem import fails the link',
    CompileNativeCLI(SrcBad, False, '', BinFile, ToolOut) <> 0);
  AssertTrue('names the symbol: ' + ToolOut,
    (Pos('undefined symbol ''_kqeueu''', ToolOut) >= 0));
end;

procedure TE2EMiscTests.TestRun_DefaultParam_MethodCallForms;
const
  Src = '''
    program P;
    uses SysUtils;
    type
      TBase = class
        function F(A: Int; B: Int = 5): Int; virtual;
        procedure Q(A: Int; B: Int = 5); virtual;
      end;
      TA = class(TBase)
        function F(A: Int; B: Int = 50): Int; override;
        procedure Q(A: Int; B: Int = 50); override;
        function G<T>(A: T; B: Int = 7): Int;
        function H(A: Int; S: string = 'dflt'): string;
        procedure Run();
      end;
    function TBase.F(A: Int; B: Int): Int; begin Result := A + B end;
    procedure TBase.Q(A: Int; B: Int); begin WriteLn('base q ', A + B) end;
    function TA.F(A: Int; B: Int): Int;
    begin
      Result := inherited F(A) * 100 + B
    end;
    procedure TA.Q(A: Int; B: Int);
    begin
      inherited Q(A);
      WriteLn('q ', A + B)
    end;
    function TA.G<T>(A: T; B: Int): Int; begin Result := B end;
    function TA.H(A: Int; S: string): string; begin Result := S + IntToStr(A) end;
    procedure TA.Run();
    begin
      WriteLn(Self.F(1), ' ', Self.H(2), ' ', Self.H(3, 'x'))
    end;
    var X: TA;
    begin
      X := TA.Create();
      X.Run();
      WriteLn(X.F(2), ' ', X.F(2, 3), ' ', X.G<Int>(1), ' ', X.H(4));
      X.Q(1)
    end.
    ''';
begin
  AssertRunsOnAll(Src,
    '650 dflt2 x3' + LineEnding + '750 703 7 dflt4' + LineEnding +
    'base q 6' + LineEnding + 'q 51' + LineEnding, 0);
end;

procedure TE2EMiscTests.TestRun_DefaultParam_OmitMultiple;
var Output: string; RCode: Int;
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
var Output: string; RCode: Int;
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
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(SrcTypeCastPointerInt, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('42', '42' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_WriteUnsigned32_PrintsUnsigned;
var Output: string; RCode: Int;
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
        var x: Int;
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
var Output: string; RCode: Int;
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
          function Helper(X: Int): Int;
          begin
            Result := X + 1
          end;
        begin
          WriteLn(IntToStr(Helper(10)))
        end;
        procedure Second;
          function Helper(X: Int): Int;
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
var Output: string; RCode: Int;
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
          function Helper(X: Int): Int;
          begin
            Result := X + 1
          end;
        begin
          WriteLn(IntToStr(Helper(10)))
        end;
        procedure TFoo.MethodB;
          function Helper(X: Int): Int;
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
var Output: string; RCode: Int;
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
        type TRec = record A, B: Int; end;
        procedure Outer(var R: TRec);
          procedure Inner;
          var Sum: Int;
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
        var ReadBack: Int;
        procedure L1(var Q: Int);
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
        var X: Int;
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
        var Matched: Int;
        procedure L1(var Q: Float64);
          procedure L2;
          begin
            if Q = 1.25 then Matched := 1 else Matched := 0;   { read }
            Q := 3.5                                            { write }
          end;
        begin L2() end;
        var X: Float64;
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
        var V, W: Int;
          procedure L2;
          var V: Int;                { shadows L1.V }
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
        type TRec = record A, B: Int; end;
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
        type TArr = array[0..2] of Int;
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
    var B: TBox<Int>;
    begin
      B := TBox<>.Create();
      B.SetValue(99);
      WriteLn(B.GetValue())
    end.
    ''';
var Output: string; RCode: Int;
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
    var P: TPair<Int, Int>;
    begin
      P := TPair<>.Create();
      P.SetKey(3);
      P.SetVal(7);
      WriteLn(P.GetKey());
      WriteLn(P.GetVal())
    end.
    ''';
var Output: string; RCode: Int;
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
      THolder = record Items: array of Int; end;
    var
      A: array of Int;
      H: THolder;
      P: ^Int;
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
var Output: string; RCode: Int;
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
    var V: TMyVal<Int>;
    begin
      V.Value := 9;
      WriteLn(V.Value)
    end.
    ''';
var Output: string; RCode: Int;
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
    var V: TMyVal<Int>;
    begin
      V.Value := 42;
      WriteLn(V.GetValue())
    end.
    ''';
var Output: string; RCode: Int;
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
    var P: TPair<Int, Int>;
    begin
      P.Key := 10;
      P.Val := 20;
      WriteLn(P.Key);
      WriteLn(P.Val)
    end.
    ''';
var Output: string; RCode: Int;
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
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  AssertEquals('output', 'hello' + LE, Output);
end;

procedure TE2EMiscTests.TestRun_BitwiseNot_Integer;
const Src = '''
    program Prg;
    var I: Int32;
    begin
      I := 0;
      WriteLn(not I)
    end.
    ''';
var Output: string; RCode: Int;
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
var Output: string; RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile+run', CompileAndRun(Src, Output, RCode));
  AssertEquals('exit code 0', 0, RCode);
  { not keeps its operand's type: a Byte complement (see "Integer
    Expression Width") }
  AssertEquals('output', '255' + LE, Output);
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
var Output: string; RCode: Int;
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
    var Flags: Int;
    begin
      Flags := 7;
      Flags := Flags and (not MASK);
      WriteLn(Flags)
    end.
    ''';
var Output: string; RCode: Int;
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
  RCode:  Int;
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
      TFn = function(N: Int): Int of object;
      TC = class
        FBase: Int;
        function AddBase(N: Int): Int;
      end;
    function TC.AddBase(N: Int): Int;
    begin
      Result := FBase + N;
    end;
    var
      C: TC;
      F: TFn;
      X: Int;
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
        Count: Int;
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
        function V: Int; virtual;
        begin Result := 5 end;
        function Scale(F: Int): Int; virtual;
        begin Result := F * 10 end;
      end;
      TDerived = class(TBase)
        function V: Int; override;
        begin Result := inherited V() + 100 end;
        function Scale(F: Int): Int; override;
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
      TDerived = class(TBase) FX: Int; end;
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
    var outer: TBox<TBox<Int>>; inner: TBox<Int>;
    begin
      inner := TBox<Int>.Create();
      inner.SetV(7);
      outer := TBox<TBox<Int>>.Create();
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
      Tar = array[Trange] of Int;
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
      TArr = array[TSub] of Int;
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
  { DEFINE/UNDEF, IFNDEF, a predefined CPU/OS symbol, and nesting together.
    The host's CPU symbol is predefined on every target -- CPUX86_64 or
    CPUARM64 -- so either one marks the nested branch live (the test used to
    name CPUX86_64 alone and failed, correctly, on arm64). }
  Src = '''
    program P;
    {$DEFINE FOO}
    {$UNDEF FOO}
    {$IFDEF CPUX86_64}{$DEFINE HOSTCPU}{$ENDIF}
    {$IFDEF CPUARM64}{$DEFINE HOSTCPU}{$ENDIF}
    begin
      {$IFDEF FOO}WriteLn('foo'){$ELSE}WriteLn('no-foo'){$ENDIF};
      {$IFNDEF BAR}WriteLn('no-bar'){$ENDIF};
      {$IFDEF HOSTCPU}
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
    function IsEven(n: Int): Boolean; forward;
    function IsOdd(n: Int): Boolean;
    begin if n = 0 then Result := False else Result := IsEven(n - 1) end;
    function IsEven(n: Int): Boolean;
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
      Total: Int;
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
        FVal: Int;
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
      S: Int;
      A: array[0..1] of Int64;
      N: Int;
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

procedure TE2EMiscTests.TestRun_ImplicitSelfFloatCall_AllForms;
const
  Src = '''
    program P;
    type
      TBase = class
        function Half(X: Float64): Float64; virtual;
        function Third(X: Float32): Float32;
        procedure Go;
      end;
      TDer = class(TBase)
        function Half(X: Float64): Float64; override;
        procedure Go2;
      end;
    function TBase.Half(X: Float64): Float64; begin Result := X / 2.0 end;
    function TBase.Third(X: Float32): Float32; begin Result := X / 3.0 end;
    procedure TBase.Go;
    var I: Int; D: Float64;
    begin
      I := Trunc(Half(9.0));
      D := Half(5.0) + 1.0;
      WriteLn(I, ' ', D:0:1, ' ', Round(Third(9.0)))
    end;
    function TDer.Half(X: Float64): Float64; begin Result := inherited Half(X) + 1.0 end;
    procedure TDer.Go2;
    begin
      WriteLn(Trunc(Half(8.0)), ' ', Half(2.0):0:1)
    end;
    var B: TBase; D: TDer;
    begin
      B := TBase.Create(); B.Go();
      D := TDer.Create(); D.Go(); D.Go2()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '4 3.5 3' + #10 + '5 4.5 3' + #10 + '5 2.0' + #10, 0);
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
    procedure One(S: Float32);
    begin
      WriteLn(SingleToStr(S))
    end;
    procedure Dbl(D: Float64);
    begin
      WriteLn(DoubleToStr(D))
    end;
    procedure Both(D: Float64; S: Float32);
    begin
      WriteLn(DoubleToStr(D), ' ', SingleToStr(S))
    end;
    var X: Float32; Y: Float64;
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
    var Calls: Int;
    function T(V: Boolean): Boolean;
    begin
      Calls := Calls + 1;
      Result := V
    end;
    var A, B: Boolean; I: Int;
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
    var I, J: Int; S: string;
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
        Value: Int;
        procedure SetValue(AVal: Int);
        function GetValue: Int;
      end;
    procedure TBox.SetValue(AVal: Int);
    begin
      Self.Value := AVal
    end;
    function TBox.GetValue: Int;
    begin
      Result := Self.Value
    end;
    procedure PrintIt(X: Int);
    begin
      WriteLn('print ', X)
    end;
    function Add(A, B: Int): Int;
    var Tmp: Int;
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
    var X: Int;
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
      function Helper(X: Int): Int;
      begin
        Result := X + 1
      end;
    begin
      WriteLn('A ', Helper(10))
    end;
    procedure OuterB;
      function Helper(X: Int): Int;
      begin
        Result := X + 2
      end;
    begin
      WriteLn('B ', Helper(20))
    end;
    procedure TFoo.MethodA;
      function Helper(X: Int): Int;
      begin
        Result := X + 3
      end;
    begin
      WriteLn('MA ', Helper(30))
    end;
    procedure TFoo.MethodB;
      function Helper(X: Int): Int;
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
    var U: UInt64; C: UInt32; N: Int64; I: Int;
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
        procedure M(A: Int; B: Int = 4242);
        procedure M7(A, B, C, D, E: Int; F: Int = 7777);
        procedure Caller;
      end;
    procedure TFoo.M(A: Int; B: Int = 4242);
    begin
      WriteLn(A + B)
    end;
    procedure TFoo.M7(A, B, C, D, E: Int; F: Int = 7777);
    begin
      WriteLn(A + B + C + D + E, ' ', F)
    end;
    procedure TFoo.Caller;
    begin
      M(2)
    end;
    procedure Q(A: Int; B: Int = 6363);
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
      TInner = record Value: Int; end;
      TOuter = record Inner: TInner; end;
      TLeaf = class Value: Int; end;
      TMid = class Leaf: TLeaf; end;
      TTop = class
        FInner: TMid;
        function Work: Int;
      end;
    function TTop.Work: Int;
    var I, K: Int;
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
      N, X: Int32; B: Byte; W: UInt16; S: Int16; Bo: Boolean;
      U: UInt32; Q: Int64; UQ: UInt64;
    begin
      N := High(Int32); Write(N, ' ');
      N := Low(Int32); WriteLn(N);
      B := High(Byte); Write(B, ' ');
      B := Low(Byte); WriteLn(B);
      W := High(UInt16); Write(W, ' ');
      S := High(Int16); Write(S, ' ');
      S := Low(Int16); WriteLn(S);
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
        FX: Int;
      end;
    type
      TB = class
        FY: Int;
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
    '9223372036854775807 cdef' + LE +
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
      TIntFn = function: Int;
      TStrFn = function(const S: string): Int;
      TRun = reference to procedure(N: Int);
      TCnt = function(const A: array of Int): Int;
      TInts = array of Int;
      TBox = class
      public
        FFn: TStrFn;
        FRun: TRun;
        function RunQualified(const S: string): Int;
        function RunImplicit(const S: string): Int;
        procedure Drv();
      end;
      TClo = reference to procedure;
      TCloFn = reference to function(A: Int): Int;
      TPlain = procedure;
      TR = record
        Pad: Int64;
        F: TClo;
        G: TCloFn;
        H: TPlain;
      end;
    function MyFn: Int;
    begin
      Result := 42
    end;
    function StrLen(const S: string): Int;
    begin
      Result := Length(S)
    end;
    function Cnt(const A: array of Int): Int;
    var I: Int;
    begin
      Result := 0;
      for I := 0 to High(A) do
        Result := Result * 10 + A[I]
    end;
    procedure Plain;
    begin
      WriteLn('plain')
    end;
    function TBox.RunQualified(const S: string): Int;
    begin
      Result := Self.FFn(S)
    end;
    function TBox.RunImplicit(const S: string): Int;
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
      F: TIntFn; B: TBox; R: TR; Base: Int; D: TInts;
    begin
      F := @MyFn;
      WriteLn(F());
      B := TBox.Create();
      B.FFn := @StrLen;
      WriteLn(B.RunQualified('abc'), ' ', B.RunImplicit('hello'));
      Base := 100;
      B.FRun := procedure(N: Int) begin WriteLn('run ', Base + N) end;
      B.Drv();
      R.Pad := 9;
      R.F := procedure begin WriteLn('global closure') end;
      R.G := function(A: Int): Int begin Result := A * Base end;
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
      TIntFn = function: Int;
      TDblFn = function(X: Float64): Float64;
      TStrFn = function(const S: string): string;
      TCnt = function(const A: array of Int): Int;
    function One: Int; begin Result := 1 end;
    function Two: Int; begin Result := 2 end;
    function Half(X: Float64): Float64; begin Result := X / 2 end;
    function Shout(const S: string): string; begin Result := S + '!' end;
    function Cnt(const A: array of Int): Int; begin Result := Length(A) end;
    function PickDbl: TDblFn; begin Result := @Half end;
    function PickStr: TStrFn; begin Result := @Shout end;
    var
      Fns: array[0..1] of TIntFn; Cs: array[0..0] of TCnt; I, Sum: Int;
      D: array of Int; S: string;
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

procedure TE2EMiscTests.TestRun_Constants_Scalar;
const
  {
    Scalar constants end to end: untyped, typed and local (procedure,
    function, method, class) constants; folded integer expressions
    (precedence, parentheses, div / mod, unary minus, named references, shl /
    or); folded floating-point expressions, including integer bit operations
    inside a float expression (1.0 / (Z shl 53) is exactly 2^-53) and ordinal
    casts that truncate or sign-extend (Byte(300), SmallInt(40000)); typed
    constants of every basic type; casts of negative values to unsigned types;
    or-chains of literals and named constants; and a typed Double variable
    initialised from an integer expression. }
  Src = '''
    program Consts;
    const
      MaxCount = 10;
      Neg = -1;
      AppName = 'MyApp';
      First = 5;
    const
      Second = 42;
      Base = 10;
      E1 = 2 * 3;
      E2 = (2 * 3);
      E3 = 2 + 3 * 4;
      E4 = (2 + 3) * 4;
      E5 = 100 div 7;
      E6 = 100 mod 7;
      E7 = Base * 2 + 1;
      E8 = -5 * 3;
      E9 = (1 shl 4) or 3;
      FG_BLUE = 1;
      FG_GREEN = 2;
      FA = 2.0 * 3;
      FB = 5 / 2;
      FC = 1.5 + 3 - 0.5;
      FD = (1 + 2) * 3.0;
      FE = 1 + 2.0;
      Pi2 = 3.14 * 2;
      FN = -1.5 * 2;
      Z = 1;
      Eps = 1.0 / (Z shl 53);
      Eps2 = 1.0 / (UInt64(1) shl 53);
      BA = 1.0 / (255 and 15);
      BB = 1.0 / (8 or 1);
      BC = 1.0 / (12 xor 6);
      BD = 1.0 / (1024 shr 2);
      CA = 1.0 * (Byte(300) shl 1);
      CB = 1.0 * (Int16(40000) shl 1);
      TI: Int32 = 100;
      TL: Int64 = 1000000000000;
      TD: Float64 = 3.14159;
      TS: Float32 = 2.71828;
      TB: Boolean = True;
      TStr: string = 'hello';
      TND: Float64 = -3.14159;
      TNI: Int32 = -42;
      Scale: Float64 = 2.5;
      CI: Int32 = Int32(-11);
      CC: UInt32 = UInt32(-11);
      CBy: Byte = Byte(-1);
      CSi: Int16 = Int16(-1);
      CW: UInt16 = UInt16(-1);
      O1: Int32 = 1 or 2 or 4;
      O2: Int32 = FG_BLUE or FG_GREEN;
      O3: Int32 = 1 or FG_BLUE or 4;
      M1: Int32 = $FF and 15;
      S1: Int32 = 1 shl 8;
      TDX: Float64 = 2 * 3;
    type
      TThing = class
      public
        const Limit = 100;
        procedure Show;
      end;
    procedure TThing.Show;
    const Local = 55;
    begin
      WriteLn(Limit, ' ', Local)
    end;
    procedure Proc;
    const Seven = 7;
    begin
      WriteLn(Seven)
    end;
    function Func: Int;
    const Hundred = 100;
    begin
      Result := Hundred
    end;
    var V: Float64 = 2 * 3; X: Int; T: TThing;
    begin
      X := First;
      WriteLn(MaxCount, ' ', Neg, ' ', AppName, ' ', X, ' ', Second);
      Proc();
      WriteLn(Func());
      T := TThing.Create();
      T.Show();
      WriteLn(TThing.Limit);
      T.Free();
      WriteLn(E1, ' ', E2, ' ', E3, ' ', E4, ' ', E5, ' ', E6, ' ', E7, ' ', E8, ' ', E9);
      WriteLn(FA:0:1, ' ', FB:0:1, ' ', FC:0:1, ' ', FD:0:1, ' ', FE:0:1, ' ',
        Pi2:0:2, ' ', FN:0:1);
      WriteLn((Eps * 9007199254740992.0):0:1, ' ', (Eps2 * 9007199254740992.0):0:1);
      WriteLn((1 / BA):0:0, ' ', (1 / BB):0:0, ' ', (1 / BC):0:0, ' ', (1 / BD):0:0);
      WriteLn(CA:0:0, ' ', CB:0:0);
      WriteLn(TI, ' ', TL, ' ', TD:0:5, ' ', TS:0:5, ' ', TB, ' ', TStr, ' ',
        TND:0:5, ' ', TNI, ' ', (Scale * 2):0:1);
      WriteLn(CI, ' ', CC, ' ', CBy, ' ', CSi, ' ', CW);
      WriteLn(O1, ' ', O2, ' ', O3, ' ', M1, ' ', S1, ' ', TDX:0:1, ' ', V:0:1)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '10 -1 MyApp 5 42' + LE +
    '7' + LE +
    '100' + LE +
    '100 55' + LE +
    '100' + LE +
    '6 6 14 20 14 2 21 -15 19' + LE +
    '6.0 2.5 4.0 9.0 3.0 6.28 -3.0' + LE +
    '1.0 1.0' + LE +
    '15 9 10 256' + LE +
    '88 -51072' + LE +
    '100 1000000000000 3.14159 2.71828 True hello -3.14159 -42 5.0' + LE +
    '-11 4294967285 255 -1 65535' + LE +
    '7 3 5 15 256 6.0 6.0' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_Constants_Arrays;
const
  {
    Array constants end to end: string and integer elements indexed by an
    enum, Int64 elements written as hex / octal bit patterns above High(Int64),
    non-zero-based and range-indexed arrays read by constant and variable
    index, a 2-D array (row-major), a named array-type alias, an or-chain and a
    Cardinal cast as elements, class member const arrays read qualified and
    bare inside a method, and routine-local const arrays.  The bare in-method
    read had no data label: x86-64 segfaulted and arm64 rejected it. }
  Src = '''
    program AConsts;
    type
      TWeather = (Sunny, Cloudy, Rainy);
      TDir = (North, East, South, West);
      TColor = (Red, Green, Blue);
      TArr = array[0..2] of Int;
      TPalette = class
      public
        const Names: array[TColor] of string = ('Red', 'Green', 'Blue');
        const Items: array[1..3] of Int32 = (11, 12, 13);
        procedure Show;
      end;
    const
      FG_BLUE = 1;
      FG_GREEN = 2;
      WeatherNames: array[TWeather] of string = ('Sunny', 'Cloudy', 'Rainy');
      DirCost: array[TDir] of Int32 = (1, 2, 3, 4);
      B: array[0..2] of Int64 = (
        $4040404040404040,
        $8080808080808080,
        &1000000000000000000000
      );
      Vals: array[5..7] of Int32 = (50, 60, 70);
      Days: array[1..3] of string = ('Mon', 'Tue', 'Wed');
      M: array[0..1, 0..1] of Int32 = ((1, 2), (3, 4));
      AV: TArr = (10, 20, 30);
      T: array[0..1] of Int32 = (FG_BLUE or FG_GREEN, 99);
      TC: array[0..1] of UInt32 = (UInt32(-11), 42);
    procedure TPalette.Show;
    const Loc: array[0..1] of Int32 = (7, 8);
    var I: Int;
    begin
      I := 1;
      WriteLn(Names[Blue], ' ', Items[2], ' ', Loc[I])
    end;
    function DayName(D: Int): string;
    const Days: array[1..2] of string = ('Sat', 'Sun');
    begin
      Result := Days[D]
    end;
    procedure Tbl;
    const Tbl: array[0..2] of Int32 = (100, 200, 300);
    var I: Int;
    begin
      for I := 0 to 2 do Write(Tbl[I], ' ');
      WriteLn()
    end;
    var
      W: TWeather; D: TDir; I, J, Sum: Int; P: TPalette;
    begin
      for W := Sunny to Rainy do Write(WeatherNames[W], ' ');
      WriteLn();
      Sum := 0;
      for D := North to West do Sum := Sum + DirCost[D];
      WriteLn(Sum, ' ', DirCost[South]);
      WriteLn(B[0], ' ', B[1], ' ', B[2]);
      I := 6;
      WriteLn(Vals[5], ' ', Vals[I], ' ', Days[2]);
      I := 3;
      WriteLn(Days[I]);
      for I := 0 to 1 do
        for J := 0 to 1 do
          Write(M[I, J], ' ');
      WriteLn(M[1][0]);
      WriteLn(AV[0] + AV[1] + AV[2], ' ', T[0], ' ', T[1], ' ', TC[0], ' ', TC[1]);
      P := TPalette.Create();
      P.Show();
      WriteLn(P.Names[Red], ' ', TPalette.Items[3]);
      P.Free();
      WriteLn(DayName(1), ' ', DayName(2));
      Tbl()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'Sunny Cloudy Rainy ' + LE +
    '10 3' + LE +
    '4629771061636907072 -9187201950435737472 -9223372036854775808' + LE +
    '50 60 Tue' + LE +
    'Wed' + LE +
    '1 2 3 4 3' + LE +
    '60 3 99 4294967285 42' + LE +
    'Blue 12 8' + LE +
    'Red 13' + LE +
    'Sat Sun' + LE +
    '100 200 300 ' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_CodegenBasics_Combined;
const
  {
    The early code-generation basics end to end: WriteLn of a string, nothing,
    an Integer and a Boolean; Integer assignment and arithmetic; string = and
    <>; Boolean literals and functions; identifiers, fields, for-loop counters,
    routines, records and methods referenced in a different case from their
    declaration (a mis-cased symbol would not link); lowercase `result`;
    Integer / Int64 to Double and Single conversions, including into class
    fields with and without Self (2^53 + 1 rounds to 2^53 only with the full
    64-bit conversion); and Single arithmetic and comparison. }
  Src = '''
    program Basics;
    type
      TRec = record
        Val: Int;
      end;
      TFoo = class
        FVal: Int;
        FD: Float64;
        FS: Float32;
        function GetVal: Int;
        procedure DoIt;
        procedure SetD(AValue: Int64);
        procedure SetDBare(AValue: Int64);
        procedure SetS(AValue: Int);
      end;
    function TFoo.GetVal: Int; begin Result := Self.FVal end;
    procedure TFoo.DoIt(); begin WriteLn('did it') end;
    procedure TFoo.SetD(AValue: Int64); begin Self.FD := AValue end;
    procedure TFoo.SetDBare(AValue: Int64); begin FD := AValue end;
    procedure TFoo.SetS(AValue: Int); begin Self.FS := AValue end;
    function MyAdd(X, Y: Int): Int;
    begin
      result := X + Y
    end;
    function Same(A, B: string): Boolean;
    begin
      Result := A = B
    end;
    function IsOK: Boolean;
    begin
      Result := True
    end;
    procedure DoStuff(X: Int);
    begin
      WriteLn('stuff ', X)
    end;
    var
      N, X, Y, Counter, I: Int; B: Boolean; S1, S2: string;
      MyObj: TFoo; MyRec: TRec; M: Int64; D: Float64; SA, SB, SC: Float32;
    begin
      WriteLn('Hello');
      WriteLn();
      WriteLn(42);
      B := True;
      WriteLn(b);
      B := False;
      WriteLn(B, ' ', IsOK());
      x := 1;
      Y := x;
      N := 3 + 4;
      WriteLn(X, ' ', y, ' ', n, ' ', 2 * 5, ' ', MyAdd(2, 3));
      S1 := 'ab'; S2 := 'a' + 'b';
      WriteLn(S1 = S2, ' ', S1 <> S2, ' ', Same('hello', 'world'), ' ', Same('x', 'x'));
      if True then WriteLn('then');
      for counter := 1 to 3 do Write(COUNTER, ' ');
      WriteLn();
      dostuff(3);
      myrec.Val := 42;
      WriteLn(MyRec.val);
      MyObj := TFoo.Create();
      myobj.FVal := 9;
      WriteLn(MYOBJ.GetVal());
      myObj.DoIt();
      M := 123456789012345;
      D := M * 1.0;
      WriteLn(D:0:0);
      I := 42;
      D := I * 1.0;
      WriteLn(D:0:1);
      D := 4345;
      WriteLn(D:0:1);
      M := 100;
      D := M;
      SA := 4345;
      WriteLn(D:0:1, ' ', SA:0:1);
      MyObj.SetD(9007199254740993);
      WriteLn(MyObj.FD:0:0);
      MyObj.SetDBare(-7);
      MyObj.SetS(12);
      WriteLn(MyObj.FD:0:1, ' ', MyObj.FS:0:1);
      SA := 1.5; SB := 2.25;
      D := SA * 1.0;
      SC := SA + SB;
      WriteLn(D:0:2, ' ', SC:0:2);
      SC := SA * SB;
      WriteLn(SC:0:3, ' ', (SA + I):0:1, ' ', SA < SB, ' ', SB < SA);
      MyObj.Free()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    'Hello' + LE +
    '' + LE +
    '42' + LE +
    'True' + LE +
    'False True' + LE +
    '1 1 7 10 5' + LE +
    'True False False True' + LE +
    'then' + LE +
    '1 2 3 ' + LE +
    'stuff 3' + LE +
    '42' + LE +
    '9' + LE +
    'did it' + LE +
    '123456789012345' + LE +
    '42.0' + LE +
    '4345.0' + LE +
    '100.0 4345.0' + LE +
    '9007199254740992' + LE +
    '-7.0 12.0' + LE +
    '1.50 3.75' + LE +
    '3.375 43.5 True False' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_NestedProc_CapturesSpillPastRegisters;
const
  Src = '''
    program s2;
    procedure Outer;
    var A, B, C, D, E, F, G, H, I, J: Int; S: string;
      function Inner(K: Int): Int;
      begin
        Result := A + B + C + D + E + F + G + H + I + J + K;
        S := S + '!';
        J := J + 100
      end;
      function Deep: Int;
        function Deeper: Int; begin Result := A * J + Length(S) end;
      begin Result := Deeper() + Inner(1000) end;
    begin
      A := 1; B := 2; C := 3; D := 4; E := 5; F := 6; G := 7; H := 8; I := 9; J := 10; S := 'x';
      WriteLn(Inner(1000));
      WriteLn(J, ' ', S);
      WriteLn(Deep());
      WriteLn(J, ' ', S)
    end;
    begin
      Outer()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '1055' + #10 + '110 x!' + #10 + '1267' + #10 +
    '210 x!!' + #10, 0);
end;

procedure TE2EMiscTests.TestRun_ProcCalls_InterfaceAndFloatArgs;
const
  Src = '''
    program pf;
    type
      IGreet = interface function Name(): string; end;
      TGreet = class(TObject, IGreet) public function Name(): string; end;
      TShow = procedure(const G: IGreet);
      TF = function(X: Float64; N: Int): Int;
      TBox = class Show: TShow; F: TF; end;
      TR = record Show: TShow; F: TF; end;
    function TGreet.Name(): string; begin Result := 'bob' end;
    procedure Show(const G: IGreet); begin WriteLn(G.Name()) end;
    function FF(X: Float64; N: Int): Int; begin Result := Trunc(X * 10) + N end;
    var P: TShow; G: IGreet; B: TBox; R: TR;
    begin
      G := TGreet.Create(); Show(G);
      P := @Show; P(G);
      B := TBox.Create(); B.Show := @Show; B.Show(G);
      B.F := @FF; WriteLn(B.F(2.5, 3));
      R.Show := @Show; R.Show(G);
      R.F := @FF; WriteLn(R.F(1.5, 4));
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'bob' + #10 + 'bob' + #10 + 'bob' + #10 + '28' + #10 +
    'bob' + #10 + '19' + #10, 0);
end;

procedure TE2EMiscTests.TestRun_ProcFieldCalls_AllForms;
const
  Src = '''
    program pg;
    uses SysUtils;
    type
      TM = procedure(A, B, C, D, E, F, G: Int; var Z: Int) of object;
      TC = reference to function(const V: array of Int; X: Float64): string;
      TP = function(A, B, C, D, E, F, G, H: Int): Int;
      TR = record P: TP; end;
      THost = class
        K: Int;
        M: TM; C: TC; P: TP;
        procedure Worker(A, B, C, D, E, F, G: Int; var Z: Int);
        procedure Run;
      end;
    function Sum8(A, B, C, D, E, F, G, H: Int): Int; begin Result := A + H * 10 end;
    procedure THost.Worker(A, B, C, D, E, F, G: Int; var Z: Int);
    begin Z := A + G + K end;
    procedure THost.Run;
    var Z: Int;
    begin
      M(1, 2, 3, 4, 5, 6, 7, Z); WriteLn(Z);
      WriteLn(C([4, 5, 6], 1.5));
      WriteLn(P(1, 2, 3, 4, 5, 6, 7, 8));
    end;
    procedure ViaVar(var R: TR); begin WriteLn(R.P(2, 0, 0, 0, 0, 0, 0, 3)) end;
    var H: THost; Z: Int; R: TR;
    begin
      H := THost.Create(); H.K := 100;
      H.M := @H.Worker;
      H.C := function(const V: array of Int; X: Float64): string
             begin Result := IntToStr(High(V)) + ':' + IntToStr(V[2] + Trunc(X * 2) + H.K) end;
      H.P := @Sum8;
      H.M(1, 2, 3, 4, 5, 6, 7, Z); WriteLn(Z);
      WriteLn(H.C([1, 2, 3], 2.5));
      WriteLn(H.P(1, 2, 3, 4, 5, 6, 7, 8));
      H.Run();
      R.P := @Sum8; WriteLn(R.P(5, 0, 0, 0, 0, 0, 0, 1)); ViaVar(R);
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '108' + #10 + '2:108' + #10 + '81' + #10 + '108' + #10 +
    '2:109' + #10 + '81' + #10 + '15' + #10 + '32' + #10, 0);
end;

procedure TE2EMiscTests.TestRun_IntfResultArg_PastRegisters;
const
  Src = '''
    program m4;
    type
      IS1 = interface function V: Int; end;
      TS = class(TObject, IS1) N: Int; function V: Int; end;
      TBig = record A, B, C: Int64; end;
      TP = function(A, B, C, D, E: Int; const I: IS1; F: Int): Int;
      TK = class
        function M(A, B, C, D, E: Int; const I: IS1; F: Int): Int;
      end;
    function TS.V: Int; begin Result := N end;
    function MkS(K: Int): IS1; var T: TS; begin T := TS.Create(); T.N := K; Result := T end;
    function Seven(A, B, C, D, E: Int; const I: IS1; F: Int): Int;
    begin Result := A + E + I.V() * 10 + F * 1000 end;
    function SevenF(X: Float64; const I: IS1; F: Int): Int;
    begin Result := Trunc(X) + I.V() * 10 + F * 1000 end;
    function SR(const I: IS1; K: Int): TBig; begin Result.A := I.V(); Result.B := K end;
    function TK.M(A, B, C, D, E: Int; const I: IS1; F: Int): Int;
    begin Result := A + I.V() * 10 + F * 1000 end;
    var P: TP; K: TK; R: TBig;
    begin
      WriteLn(Seven(1, 2, 3, 4, 5, MkS(6), 7));
      WriteLn(SevenF(2.0, MkS(3), 4));
      R := SR(MkS(9), 8); WriteLn(R.A, ' ', R.B);
      P := @Seven; WriteLn(P(1, 2, 3, 4, 5, MkS(6), 7));
      K := TK.Create(); WriteLn(K.M(1, 2, 3, 4, 5, MkS(6), 7));
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '7066' + #10 + '4032' + #10 + '9 8' + #10 + '7066' + #10 +
    '7061' + #10, 0);
end;

procedure TE2EMiscTests.TestRun_NestedProc_CapturedByRefForms;
const
  Src = '''
    program CapForms;
    type
      PInt = ^Int;
      TArr = array[0..2] of Int;
      TRec = record N: Int; A: TArr; S: String; end;
    procedure SetVia(Q: PInt; V: Int); begin Q^ := V end;
    procedure BumpI(var X: Int); begin X := X + 100 end;
    procedure BumpR(var R: TRec); begin R.N := R.N + 1000 end;
    procedure Show(const R: TRec; I: Int; const S: String; const A: TArr);
    begin
      WriteLn(R.N, ' ', R.A[0], ' ', R.A[1], ' ', R.S, ' | ', I, ' ', S, ' | ', A[0], ' ', A[1])
    end;
    procedure ByVar(var R: TRec; var I: Int; var S: String; var A: TArr);
      procedure Inner;
        procedure Deep;
        begin
          SetVia(@R.N, R.N + 1); SetVia(@R.A[1], 7); BumpR(R);
          Inc(I); BumpI(I); SetVia(@I, I + 1); S := S + 'x';
          A[0] := A[0] + 5; SetVia(@A[1], 6)
        end;
      begin
        R.N := R.N + 10; R.S := R.S + 'v'; R.A[0] := R.A[1] + 3;
        Deep();
      end;
    begin
      Inner(); Show(R, I, S, A)
    end;
    procedure ByVal(R: TRec; I: Int; S: String; A: TArr);
      procedure Inner;
        procedure Deep;
        begin
          SetVia(@R.N, R.N + 1); SetVia(@R.A[1], 7); BumpR(R);
          Inc(I); BumpI(I); SetVia(@I, I + 1); S := S + 'x';
          A[0] := A[0] + 5; SetVia(@A[1], 6)
        end;
      begin
        R.N := R.N + 10; R.S := R.S + 'v'; R.A[0] := R.A[1] + 3;
        Deep();
      end;
    begin
      Inner(); Show(R, I, S, A)
    end;
    procedure Locals;
    var R: TRec; I: Int; S: String; A: TArr;
      procedure Inner;
        procedure Deep;
        begin
          SetVia(@R.N, R.N + 1); SetVia(@R.A[1], 7); BumpR(R);
          Inc(I); BumpI(I); SetVia(@I, I + 1); S := S + 'x';
          A[0] := A[0] + 5; SetVia(@A[1], 6)
        end;
      begin
        R.N := R.N + 10; R.S := R.S + 'v'; R.A[0] := R.A[1] + 3;
        Deep();
      end;
    begin
      R.N := 1; R.A[1] := 2; R.S := 's'; I := 1; S := 't'; A[0] := 1;
      Inner(); Show(R, I, S, A)
    end;
    var GR: TRec; GI: Int; GS: String; GA: TArr;
    begin
      GR.N := 1; GR.A[1] := 2; GR.S := 's'; GI := 1; GS := 't'; GA[0] := 1;
      ByVal(GR, GI, GS, GA); Show(GR, GI, GS, GA);
      ByVar(GR, GI, GS, GA); Show(GR, GI, GS, GA);
      Locals();
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src,
    '1012 5 7 sv | 103 tx | 6 6' + LE +
    '1 0 2 s | 1 t | 1 0' + LE +
    '1012 5 7 sv | 103 tx | 6 6' + LE +
    '1012 5 7 sv | 103 tx | 6 6' + LE +
    '1012 5 7 sv | 103 tx | 6 6' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_SetLength_AllLValueForms;
const
  Src = '''
    program SetLengthForms;
    type
      TDyn = array of Int;
      PDyn = ^TDyn;
      PStr = ^String;
      TRec = record D: TDyn; S: String; end;
      PRec = ^TRec;
      TObj = class D: TDyn; S: String; R: TRec; procedure Run; end;
    var GD: TDyn; GS: String; GR: TRec; GO: TObj; AD: array[0..1] of TDyn;
      AS2: array[0..1] of String; DD: array of TDyn; PD: PDyn; PS: PStr; PR: PRec;
    procedure Show(const D: TDyn; const S: String); begin WriteLn(Length(D), ' ', Length(S)) end;
    procedure TObj.Run;
    begin
      SetLength(D, 2); SetLength(S, 3); SetLength(Self.R.D, 4); SetLength(R.S, 5);
      Show(D, S); Show(R.D, R.S)
    end;
    procedure VarP(var D: TDyn; var S: String; var R: TRec);
    begin
      SetLength(D, 6); SetLength(S, 7); SetLength(R.D, 8); SetLength(R.S, 9)
    end;
    procedure Cap;
    var D: TDyn; S: String; R: TRec;
      procedure Inner;
      begin
        SetLength(D, 1); SetLength(S, 2); SetLength(R.D, 3); SetLength(R.S, 4)
      end;
    begin
      Inner(); Show(D, S); Show(R.D, R.S)
    end;
    procedure Run;
    var LD: TDyn; LS: String;
    begin
      GO := TObj.Create(); SetLength(DD, 2); PD := @GD; PS := @GS; PR := @GR;
      GO.Run();
      VarP(GD, GS, GR); Show(GD, GS); Show(GR.D, GR.S);
      Cap();
      SetLength(LD, 3); SetLength(LS, 2); Show(LD, LS);
      SetLength(GO.D, 3); SetLength(GO.S, 2); SetLength(GO.R.D, 4); Show(GO.D, GO.S); Show(GO.R.D, GO.S);
      SetLength(AD[1], 3); SetLength(AS2[0], 2); Show(AD[1], AS2[0]);
      SetLength(DD[1], 3); Show(DD[1], '');
      SetLength(PD^, 5); SetLength(PS^, 6); Show(GD, GS);
      SetLength(PR^.D, 1); SetLength(PR^.S, 2); Show(GR.D, GR.S);
    end;
    begin
      Run();
      WriteLn('done');
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src,
    '2 3' + LE +
    '4 5' + LE +
    '6 7' + LE +
    '8 9' + LE +
    '1 2' + LE +
    '3 4' + LE +
    '3 2' + LE +
    '3 2' + LE +
    '4 2' + LE +
    '3 2' + LE +
    '3 0' + LE +
    '5 6' + LE +
    '1 2' + LE +
    'done' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_NestedProc_ProcVarsAndDynArrays;
const
  Src = '''
    program NestedProcVarsAndArrays;
    type
      TMeth = procedure of object;
      TClos = reference to procedure;
      TDyn = array of Int;
      THold = class N: Int; procedure Hi; end;
    procedure THold.Hi; begin WriteLn('hi ', N) end;
    procedure Calls(var VM: TMeth; VC: TClos);
    var LM: TMeth;
      procedure Inner;
      begin
        LM := VM;
        LM(); VM(); VC();
      end;
    begin
      Inner(); LM();
    end;
    procedure Arrays(var V: TDyn; P: TDyn);
    var L: TDyn; S: String;
      procedure Inner;
      begin
        L[0] := 5; V[1] := 6; P[0] := 7; S := S + 'x';
        WriteLn(L[0] + V[1] + P[0], ' ', Length(L), ' ', S);
        SetLength(L, 3); L[2] := 9; SetLength(S, 1); SetLength(V, 3); V[2] := 4;
      end;
    begin
      SetLength(L, 1); S := 'q';
      Inner(); WriteLn(L[0], ' ', L[2], ' ', V[1], ' ', P[0], ' ', Length(L), ' ', S, ' ', V[2]);
    end;
    var H: THold; M: TMeth; G, D: TDyn;
    begin
      H := THold.Create(); H.N := 7; M := @H.Hi;
      Calls(M, procedure begin WriteLn('c') end);
      SetLength(G, 2); SetLength(D, 1);
      Arrays(G, D); WriteLn(G[1], ' ', D[0], ' ', Length(G), ' ', G[2]);
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src,
    'hi 7' + LE +
    'hi 7' + LE +
    'c' + LE +
    'hi 7' + LE +
    '18 1 qx' + LE +
    '5 9 6 7 3 q 4' + LE +
    '6 7 3 4' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_SelfRecordFieldCalls_AndSingles;
const
  Src = '''
    program SelfRecordFieldCalls;
    type
      TMeth = procedure of object;
      TFn = function: Int of object;
      TCl = reference to function: Int;
      THold = class N: Int; procedure Hi; function Get: Int; end;
      TRec = record A: Int; M: TMeth; F: TFn; C: TCl; function Sum: Int; procedure Bump; end;
      TObj = class R: TRec; F: Float32; procedure Run; end;
    procedure THold.Hi; begin WriteLn('hi ', N) end;
    function THold.Get: Int; begin Result := N end;
    function TRec.Sum: Int; begin Result := A + 1 end;
    procedure TRec.Bump; begin A := A + 10 end;
    procedure TObj.Run;
    var X: Int; L: Float32;
    begin
      R.M(); Self.R.M();
      X := R.F(); WriteLn(X, ' ', R.F() + 1, ' ', R.C(), ' ', Self.R.C());
      R.Bump(); X := R.Sum(); WriteLn(X, ' ', R.Sum() * 2);
      L := F; WriteLn(L:0:2, ' ', F:0:2); F := F + 1.25; WriteLn(F:0:2);
    end;
    procedure VS(var X: Float32; Y: Float32);
    var L: Float32;
      procedure Inner;
      begin
        L := X + Y; X := X * 2; Y := Y + L;
        WriteLn(L:0:2, ' ', X:0:2, ' ', Y:0:2);
      end;
    begin
      L := 0; Inner(); WriteLn(L:0:2, ' ', X:0:2, ' ', Y:0:2);
    end;
    var H: THold; O: TObj; G: Float32;
    begin
      H := THold.Create(); H.N := 7; O := TObj.Create();
      O.R.M := @H.Hi; O.R.F := @H.Get; O.R.C := function: Int begin Result := 9 end;
      O.R.A := 1; O.F := 1.5;
      O.Run(); O.R.C := nil;
      G := 1.5; VS(G, 0.25); WriteLn(G:0:2);
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src,
    'hi 7' + LE +
    'hi 7' + LE +
    '7 8 9 9' + LE +
    '12 24' + LE +
    '1.50 1.50' + LE +
    '2.75' + LE +
    '1.75 3.00 2.00' + LE +
    '1.75 3.00 2.00' + LE +
    '3.00' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_DynArrayElements_FloatFieldElements_FatNilTests;
const
  Src1 = '''
    program dd;
    type TDyn = array of Int;
    function Mk(N: Int): TDyn; begin SetLength(Result, 3); Result[1] := N end;
    var M: array of TDyn; S: array[0..1] of TDyn; D: TDyn; I: Int; X: TDyn;
    begin
      SetLength(M, 2);
      for I := 1 to 3 do
      begin
        D := Mk(I); M[0] := D; S[1] := D; SetLength(D, 0);
        X := Mk(100 + I);
        WriteLn(M[0][1], ' ', S[1][1]);
      end;
    end.
    ''';
  Src2 = '''
    program fl;
    type TObj = class A: array[0..2] of Float64; D: array of Float32; end;
    var O: TObj; X: Float64; Y: Float32;
    begin
      O := TObj.Create(); SetLength(O.D, 3);
      O.A[1] := 2.5; O.D[1] := 1.5;
      X := O.A[1]; Y := O.D[1];
      WriteLn(X:0:2, ' ', Y:0:2, ' ', O.A[1]:0:2, ' ', O.D[1]:0:2);
      WriteLn(O.A[1] + 1:0:2);
    end.
    ''';
  Src3 = '''
    program an2;
    type TClos = reference to function: Int;
      TMeth = procedure of object;
      THold = class procedure Hi; end;
      TObj = class C: TClos; M: TMeth; A: array[0..1] of TMeth; end;
    procedure THold.Hi; begin end;
    var O: TObj; K: TClos; M: TMeth; H: THold;
    begin
      O := TObj.Create(); H := THold.Create();
      WriteLn(K = nil, ' ', K <> nil, ' ', Assigned(K), ' ', Assigned(O.C), ' ', Assigned(O.M), ' ', Assigned(O.A[1]), ' ', M = nil);
      K := function: Int begin Result := 1 end; O.C := K; M := @H.Hi; O.M := M; O.A[1] := M;
      WriteLn(K = nil, ' ', K <> nil, ' ', Assigned(K), ' ', Assigned(O.C), ' ', Assigned(O.M), ' ', Assigned(O.A[1]), ' ', M = nil);
      K := nil; O.C := nil;
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src1,
    '1 1' + LE +
    '2 2' + LE +
    '3 3' + LE, 0);
  AssertRunsOnAll(Src2,
    '2.50 1.50 2.50 1.50' + LE +
    '3.50' + LE, 0);
  AssertRunsOnAll(Src3,
    'True False False False False False True' + LE +
    'False True True True True True False' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_CapturedAndVarInterfaces;
const
  Src1 = '''
    program ci;
    type
      IFoo = interface function Get: Int; end;
      THold = class(TObject, IFoo) N: Int; function Get: Int; end;
    function THold.Get: Int; begin Result := N end;
    procedure Show(const F: IFoo); begin WriteLn(F.Get()) end;
    function Mk(N: Int): IFoo; var H: THold; begin H := THold.Create(); H.N := N; Result := H end;
    procedure Outer(var V: IFoo; P: IFoo);
    var L: IFoo;
      procedure Inner;
        procedure Deep; begin WriteLn(L.Get(), ' ', V.Get(), ' ', P.Get()) end;
      begin
        L := Mk(1); Show(L); Show(V); Show(P);
        V := Mk(2); P := L; WriteLn(L <> nil, ' ', Assigned(P));
        Deep();
      end;
    begin
      Inner(); WriteLn(L.Get(), ' ', V.Get(), ' ', P.Get());
    end;
    var G: IFoo;
    begin
      G := Mk(5); Outer(G, Mk(6)); WriteLn(G.Get());
    end.
    ''';
  Src2 = '''
    program vi;
    type IFoo = interface function Get: Int; end;
      THold = class(TObject, IFoo) function Get: Int; end;
    function THold.Get: Int; begin Result := 42 end;
    procedure Show(const F: IFoo); begin WriteLn(F.Get()) end;
    procedure Outer(var V: IFoo); begin Show(V) end;
    var G: IFoo;
    begin G := THold.Create(); Outer(G) end.
    ''';
  Src3 = '''
    program vs;
    type IFoo = interface function Get: Int; end;
      THold = class(TObject, IFoo) N: Int; function Get: Int; end;
    function THold.Get: Int; begin Result := N end;
    function Mk(N: Int): IFoo; var H: THold; begin H := THold.Create(); H.N := N; Result := H end;
    procedure SetV(var V: IFoo; const W: IFoo); begin V := Mk(2); WriteLn(V.Get()); V := W; WriteLn(V.Get()); V := nil; WriteLn(V = nil) end;
    var G, H: IFoo;
    begin G := Mk(1); H := Mk(3); SetV(G, H); WriteLn(G = nil) end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src1,
    '1' + LE +
    '5' + LE +
    '6' + LE +
    'True True' + LE +
    '1 2 1' + LE +
    '1 2 1' + LE +
    '2' + LE, 0);
  AssertRunsOnAll(Src2,
    '42' + LE, 0);
  AssertRunsOnAll(Src3,
    '2' + LE +
    '3' + LE +
    'True' + LE +
    'True' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_ProcTypes_InlineParamAndReturnTypes;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(
    '''
    program P;
    type
      TPtr = procedure(P: ^Int);
      TSet = function(S: set of Byte): Boolean;
      TArr = function(N: Int): array of Int;
    procedure Bump(P: ^Int);
    begin
      P^ := P^ + 1
    end;
    function HasFive(S: set of Byte): Boolean;
    begin
      Result := 5 in S
    end;
    function Mk(N: Int): array of Int;
    var I: Int;
    begin
      SetLength(Result, N);
      for I := 0 to N - 1 do
        Result[I] := I * 10
    end;
    var
      A: TPtr;
      B: TSet;
      C: TArr;
      X: Int;
      D: array of Int;
    begin
      A := @Bump;
      B := @HasFive;
      C := @Mk;
      X := 41;
      A(@X);
      WriteLn(X);
      WriteLn(B([1, 5]), ' ', B([2]));
      D := C(3);
      WriteLn(Length(D), ' ', D[2])
    end.
    ''',
    '42' + LE + 'True False' + LE + '3 20' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_InlineProcTypes_AllPositions;
const
  Src = '''
    program P;
    type
      TCounter = class
        N: Int;
        procedure Add(K: Int);
      end;
      TRec = record
        F: function(A, B: Int): Int;
      end;
    procedure TCounter.Add(K: Int);
    begin
      N := N + K
    end;
    procedure Show(N: Int; const S: string);
    begin
      WriteLn(S, '=', N)
    end;
    function Mul(A, B: Int): Int;
    begin
      Result := A * B
    end;
    var
      G: procedure(N: Int; const S: string);
      M: procedure(K: Int) of object;
      R: reference to function(X: Int): Int;
      Rec: TRec;
      C: TCounter;
      Base: Int;
    procedure Local();
    var
      H: function(A, B: Int): Int;
    begin
      H := @Mul;
      WriteLn(H(6, 7))
    end;
    begin
      G := @Show;
      G(1, 'global');
      Local();
      Rec.F := @Mul;
      WriteLn(Rec.F(3, 5));
      C := TCounter.Create();
      M := @C.Add;
      M(4);
      M(5);
      WriteLn(C.N);
      Base := 100;
      R := function(X: Int): Int
           begin
             Result := X + Base
           end;
      WriteLn(R(23));
      G := nil;
      WriteLn(Assigned(G))
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertRunsOnAll(Src,
    'global=1' + LE + '42' + LE + '15' + LE + '9' + LE + '123' + LE +
    'False' + LE, 0);
  AssertLeakFreeOnAll(Src, '');
end;

procedure TE2EMiscTests.TestRun_InlineProcType_UnitInterfaceVar;
var
  Output: string;
  RCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  AssertTrue('compile+run: ' + Output, CompileAndRunWithUnitNative('crs',
    '''
    unit crs;

    interface

    var
      errors: Int;
      Error: procedure(nr, line, col: Int; pos: Int64);

    procedure Get(var sym: Int);

    implementation

    procedure Get(var sym: Int);
    begin
      sym := 7;
      if Assigned(Error) then
        Error(sym, 3, 9, 1234)
    end;

    end.
    ''',
    '''
    program P;
    uses crs;
    procedure Report(nr, line, col: Int; pos: Int64);
    begin
      Inc(errors);
      WriteLn('error ', nr, ' at ', line, ':', col, ' pos ', pos)
    end;
    var S: Int;
    begin
      Get(S);
      Error := @Report;
      Get(S);
      WriteLn('errors=', errors)
    end.
    ''', Output, RCode));
  AssertEquals('exit 0', 0, RCode);
  AssertEquals('stdout', 'error 7 at 3:9 pos 1234' + LE + 'errors=1' + LE, Output);
end;

procedure TE2EMiscTests.TestBuildRtlObjects_CollatingLocale_PrintsOnlyObjects;
var
  SrcFile, AsmFile, ProgObj, Script, Compiler, ObjDir: string;
  AsmText, OutLocale, OutC: string;
  Lines: TStringList;
  I, Rc: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit end;
  { A program object whose symbol list mixes case and underscores, so a
    collating sort and a byte-wise comm disagree on its order. }
  SrcFile := FScratch + '/rtlsel.pas';
  AsmFile := FScratch + '/rtlsel.s';
  ProgObj := FScratch + '/rtlsel.o';
  WriteFile(SrcFile,
    'program P;' + LE +
    'uses classes;' + LE +
    'var L: TStringList;' + LE +
    'begin' + LE +
    '  L := TStringList.Create();' + LE +
    '  WriteLn(L.Count)' + LE +
    'end.' + LE);
  Compiler := ProjectRoot() + 'compiler/target/blaise';
  { Only stdout is assembly: RunProc merges stderr into its output, and any
    compiler note there (a stale-cache recompile, say) would reach cc as a
    syntax error.  So the shell writes stdout to the .s file itself. }
  Rc := RunProc('sh',
    ['-c', '"$1" --source "$2" --unit-path "$3" --unit-path "$4" --emit-asm > "$5"',
     'sh', Compiler, SrcFile, FRTLUnitPath, FStdlibUnitPath, AsmFile], AsmText);
  AssertEquals('emit-asm: ' + AsmText, 0, Rc);
  Rc := RunProc('cc', ['-c', '-o', ProgObj, AsmFile], OutC);
  AssertEquals('cc -c: ' + OutC, 0, Rc);

  Script := ProjectRoot() + 'scripts/build-rtl-objects.sh';
  ObjDir := FScratch + '/rtlsel-obj';
  AssertEquals('script (C)', 0, RunProc('env',
    ['LC_ALL=C', Script, Compiler, ObjDir, '--exclude-defined-by', ProgObj],
    OutC));
  AssertEquals('script (en_US.UTF-8)', 0, RunProc('env',
    ['LC_ALL=en_US.UTF-8', Script, Compiler, ObjDir,
     '--exclude-defined-by', ProgObj], OutLocale));

  Lines := TStringList.Create();
  try
    Lines.Text := OutLocale;
    for I := 0 to Lines.Count - 1 do
      if Trim(Lines.Strings[I]) <> '' then
        AssertTrue('not an object path: ' + Lines.Strings[I],
          FileExists(Trim(Lines.Strings[I])));
  finally
    Lines.Free();
  end;
  AssertEquals('object selection depends on the locale', OutC, OutLocale);
end;

{ GH discussion #236: a blaise.testing runner silently ignored every option
  it did not know, so '-v' (or a misspelt '--exclude-category') quietly ran
  the whole suite.  It now answers --help / -h with usage and exit 0, and
  rejects anything else it does not know with the usage and exit 2. }
procedure TE2EMiscTests.TestRun_TestRunner_HelpAndRejectedOptions;
const
  Src = '''
    program RunnerCli;
    uses blaise.testing, blaise.testing.runner.text;
    type
      TCliTests = class(TTestCase)
      published
        procedure TestOne;
      end;
    procedure TCliTests.TestOne;
    begin
      AssertTrue('one', True)
    end;
    begin
      RegisterTest(TCliTests);
      Halt(RunAll())
    end.
    ''';
var
  BinFile, ToolOut, Output: string;
  Rc: Int;
begin
  Rc := CompileNativeCLI(Src, False, '', BinFile, ToolOut);
  AssertEquals('compile: ' + ToolOut, 0, Rc);

  AssertEquals('no arguments: exit', 0, RunProc(BinFile, [], Output));
  AssertTrue('no arguments: runs the tests: ' + Output, Pos('OK (1 tests', Output) >= 0);

  AssertEquals('--help: exit', 0, RunProc(BinFile, ['--help'], Output));
  AssertTrue('--help: lists --verbose: ' + Output, Pos('--verbose', Output) >= 0);
  AssertTrue('--help: runs no tests: ' + Output, Pos('OK (', Output) < 0);

  AssertEquals('-h: exit', 0, RunProc(BinFile, ['-h'], Output));
  AssertTrue('-h: lists --suite: ' + Output, Pos('--suite', Output) >= 0);

  AssertEquals('-v: exit', 2, RunProc(BinFile, ['-v'], Output));
  AssertTrue('-v: names the option: ' + Output,
    Pos('unknown option ''-v''', Output) >= 0);
  AssertTrue('-v: shows the usage: ' + Output, Pos('--verbose', Output) >= 0);
  AssertTrue('-v: runs no tests: ' + Output, Pos('OK (', Output) < 0);

  AssertEquals('--suite without value: exit', 2,
    RunProc(BinFile, ['--suite'], Output));
end;

procedure TE2EMiscTests.TestRun_ChainPastFieldElement;
const
  Src = '''
    program P;
    type
      TEv = procedure(A: Int) of object;
      TPr = procedure(A: Int);
      THandler = class
        procedure Go(A: Int);
      end;
      TPt = record X, Y: Int; end;
      TRow = array[0..2] of Int;
      TObj = class
        AR: array[0..1] of TPt;
        DR: array of TPt;
        A2: array[0..1] of TRow;
        AM: array[0..1] of TEv;
        PR: array[0..1] of TPr;
        H: THandler;
      end;
      TBox = class
        O: TObj;
      end;
    procedure THandler.Go(A: Int);
    begin
      WriteLn('go ', A)
    end;
    procedure Hi(A: Int);
    begin
      WriteLn('hi ', A)
    end;
    var
      O: TObj;
      B: TBox;
    begin
      O := TObj.Create();
      B := TBox.Create();
      B.O := O;
      O.H := THandler.Create();
      SetLength(O.DR, 2);
      B.O.AR[0].Y := 8;
      B.O.DR[1].X := 7;
      B.O.A2[0][1] := 6;
      B.O.A2[1][2] := 5;
      WriteLn(O.AR[0].Y, O.DR[1].X, O.A2[0][1], O.A2[1][2]);
      O.AM[1] := @O.H.Go;
      O.PR[0] := @Hi;
      O.AM[1](1);
      B.O.AM[1](2);
      B.O.PR[0](3)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '8765' + #10 + 'go 1' + #10 + 'go 2' + #10 + 'hi 3' + #10, 0);
end;

procedure TE2EMiscTests.TestRun_ProgramOverloadForward_CallsEachBody;
const
  Src = '''
    program P;
    procedure F(X: Int); overload; forward;
    procedure F(const X: string); overload; forward;
    procedure G;
    begin
      F(41);
      F('abc')
    end;
    procedure F(X: Int); overload;
    begin
      WriteLn('int ', X + 1)
    end;
    procedure F(const X: string);
    begin
      WriteLn('str ', X)
    end;
    begin
      G()
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, 'int 42' + #10 + 'str abc' + #10, 0);
end;

procedure TE2EMiscTests.TestRun_ConstArray_AliasElementWidths;
const
  Src = '''
    program P;
    type
      TMyHalf = Int16;
    const
      A: array[0..2] of Int16 = (1, 2, -3);
      Q: array[0..2] of UInt64 = (10, 20, 30);
      W: array[0..2] of UInt16 = (100, 200, 300);
      M: array[0..2] of TMyHalf = (7, 8, 9);
    var I: Int;
    begin
      for I := 1 to 2 do
        WriteLn(A[I], ' ', Q[I], ' ', W[I], ' ', M[I])
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '2 20 200 8' + #10 + '-3 30 300 9' + #10, 0);
end;


procedure TE2EMiscTests.TestRun_NestedExitReadsCapturedRecord;
const
  Src = '''
    program P;
    type
      TT = record Name: string; B: Int; end;
    function Use(const X: TT): Int; begin Result := Length(X.Name) + X.B; end;
    procedure Run();
    var T: TT; K: Int;
      function Sum(): Int;
      begin
        if K > 0 then
          Exit(Use(T) + K);
        Result := 0;
      end;
    begin
      T.Name := 'abc'; T.B := 4; K := 10;
      WriteLn(Sum());
    end;
    begin
      Run();
    end.
    ''';
begin
  AssertRunsOnAll(Src, '17' + LineEnding, 0);
end;

procedure TE2EMiscTests.TestRun_DerefAfterSubscript_Statements;
const
  Src = '''
    program P;
    const BlkSize = 12;
    type
      BufBlock = array [0 .. BlkSize - 1] of Int;
      PBlock = ^BufBlock;
      TRec = record A, B: Int; end;
      PRec = ^TRec;
      Buffer = array [0 .. 31] of PBlock;
    var
      Buf: Buffer;
      Blk, Blk2: BufBlock;
      X, N: Int;
      Recs: array of PRec;
      R: TRec;
      DP: array[0..1] of ^Int;
    begin
      Blk[0] := 2;
      Buf[0] := @Blk;
      Buf[0]^[1] := 12;
      X := Buf[0]^[1];
      WriteLn(X, ' ', Blk[1]);
      Blk2[3] := 9;
      Buf[0]^ := Blk2;
      WriteLn(Blk[3], ' ', Buf[0]^[3]);
      SetLength(Recs, 1);
      Recs[0] := @R;
      Recs[0]^.A := 5;
      Recs[0]^.B := Recs[0]^.A + 1;
      WriteLn(R.A, ' ', R.B);
      DP[1] := @N;
      DP[1]^ := 77;
      WriteLn(N)
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src, '12 12' + LE + '9 9' + LE + '5 6' + LE + '77' + LE, 0);
end;

procedure TE2EMiscTests.TestRun_IndirectCallInUnitClassMethod_Clones;
const
  UnitSrc = '''
    unit indirclone;
    interface
    type
      TFn = function(A, B: Int): Int;
      TK = class
        function Go(): Int;
        procedure Show(const S: string);
      end;
    function GetFn(): TFn;
    implementation
    function Add(A, B: Int): Int; begin Result := A + B; end;
    function GetFn(): TFn; begin Result := @Add; end;
    function TK.Go(): Int;
    begin
      Result := GetFn()(40, 2);
    end;
    procedure TK.Show(const S: string);
    var
      N: Int;
    begin
      N := GetFn()(Length(S), GetFn()(1, 1));
      WriteLn(S, ' ', N);
    end;
    end.
    ''';
  Src = '''
    program P;
    uses indirclone;
    var
      K: TK;
    begin
      K := TK.Create();
      WriteLn(K.Go());
      K.Show('abc');
      K.Free();
    end.
    ''';
var
  Output: string;
  ExitCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile + run: ' + Output,
    CompileAndRunWithUnit('indirclone', UnitSrc, Src, Output, ExitCode));
  AssertEquals('exit code', 0, ExitCode);
  AssertEquals('stdout', '42' + LineEnding + 'abc 5' + LineEnding, Output);
end;

procedure TE2EMiscTests.TestRun_SetConstantParamDefault;
const
  Src = '''
    program P;
    const
      Lo = 2;
    type
      TMod = (mShift, mCtrl, mAlt, mMeta);
      TMods = set of TMod;
      TBytes = set of Byte;
      TK = class
        procedure Key(const N: string; M: TMods = [mCtrl, mAlt]);
      end;
    procedure Show(A: Int; M: TMods = []);
    begin
      WriteLn(A, ' ', mShift in M, ' ', mCtrl in M);
    end;
    procedure Bytes(B: TBytes = [Lo..4, 9]);
    var
      I: Int;
    begin
      for I := 0 to 10 do
        if I in B then
          Write(I, ' ');
      WriteLn();
    end;
    procedure Span(M: TMods = [mShift..mAlt]);
    begin
      WriteLn(mShift in M, ' ', mAlt in M, ' ', mMeta in M);
    end;
    procedure TK.Key(const N: string; M: TMods);
    begin
      WriteLn(N, ' ', mCtrl in M, ' ', mAlt in M, ' ', mShift in M);
    end;
    var
      K: TK;
    begin
      Show(1);
      Show(2, [mShift]);
      Bytes();
      Bytes([1]);
      Span();
      K := TK.Create();
      K.Key('k');
      K.Key('s', [mShift]);
      K.Free();
    end.
    ''';
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertRunsOnAll(Src,
    '1 False False' + LineEnding + '2 True False' + LineEnding +
    '2 3 4 9 ' + LineEnding + '1 ' + LineEnding +
    'True True False' + LineEnding +
    'k True True False' + LineEnding + 's False False True' + LineEnding, 0);
end;

procedure TE2EMiscTests.TestRun_SetConstantParamDefault_InUnit;
const
  UnitSrc = '''
    unit usetdef;
    interface
    type
      TMod = (mShift, mCtrl, mAlt);
      TMods = set of TMod;
    procedure Show(const N: string; M: TMods = [mCtrl]);
    implementation
    procedure Show(const N: string; M: TMods);
    begin
      WriteLn(N, ' ', mShift in M, ' ', mCtrl in M);
    end;
    end.
    ''';
  Src = '''
    program P;
    uses usetdef;
    begin
      Show('a');
      Show('b', [mShift]);
    end.
    ''';
var
  Output: string;
  ExitCode: Int;
begin
  if not ToolchainAvailable() then begin Ignore('toolchain unavailable'); Exit; end;
  AssertTrue('compile + run: ' + Output,
    CompileAndRunWithUnit('usetdef', UnitSrc, Src, Output, ExitCode));
  AssertEquals('exit code', 0, ExitCode);
  AssertEquals('stdout', 'a False True' + LineEnding + 'b True False' + LineEnding,
    Output);
end;

initialization
  RegisterTest(TE2EMiscTests);

end.

