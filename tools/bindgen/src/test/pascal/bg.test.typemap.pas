{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Graeme Geldenhuys
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

unit bg.test.typemap;

{ Tests for Bindgen.TypeMap — clang qualType string → Blaise type name.

  Coverage:
    - C builtin types map to the ABI-equivalent Blaise primitive.
    - Qualifiers (const/volatile) and tag keywords (struct/union/enum)
      are stripped before mapping.
    - Pointer types: char* → PChar, void* → Pointer, T* → PT with a
      synthetic 'PT = ^T' alias registered on the mapper.
    - Fixed-size arrays map to 0-based static arrays.
    - Function-pointer types degrade to Pointer (slice 1). }

interface

uses
  blaise.testing, Bindgen.TypeMap;

type
  TTypeMapTests = class(TTestCase)
  private
    FMapper: TTypeMapper;
  protected
    procedure SetUp; override;
    procedure TearDown; override;
  published
    procedure TestMap_Int_IsInteger;
    procedure TestMap_UnsignedInt_IsCardinal;
    procedure TestMap_Long_IsInt64;
    procedure TestMap_UnsignedLong_IsUInt64;
    procedure TestMap_LongLong_IsInt64;
    procedure TestMap_UnsignedLongLong_IsUInt64;
    procedure TestMap_Short_IsSmallInt;
    procedure TestMap_UnsignedShort_IsWord;
    procedure TestMap_Char_IsByte;
    procedure TestMap_UnsignedChar_IsByte;
    procedure TestMap_Float_IsSingle;
    procedure TestMap_Double_IsDouble;
    procedure TestMap_Bool_IsBoolean;
    procedure TestMap_Void_IsEmpty;
    procedure TestMap_ConstQualifier_Stripped;
    procedure TestMap_StructTag_Stripped;
    procedure TestMap_CharPtr_IsPChar;
    procedure TestMap_ConstCharPtr_IsPChar;
    procedure TestMap_VoidPtr_IsPointer;
    procedure TestMap_NamedPtr_IsPName_AliasRegistered;
    procedure TestMap_CharPtrPtr_IsPPChar;
    procedure TestMap_PtrAlias_RegisteredOnlyOnce;
    procedure TestMap_PtrAlias_CaseInsensitiveDedup;
    procedure TestMap_TypedefName_PassesThrough;
    procedure TestMap_FixedArray_IsStaticArray;
    procedure TestMap_FunctionPtr_IsPointer;
    procedure TestFnPtrDecl_IntArgs_FunctionType;
    procedure TestFnPtrDecl_VoidReturn_ProcedureType;
    procedure TestFnPtrDecl_NoParams;
    procedure TestFnPtrDecl_Variadic_Fails;
    procedure TestMapCallback_RegistersNamedType;
    procedure TestMapCallback_SameSignature_Deduped;
    procedure TestMapCallback_NonFnPtr_FallsBackToMap;
    procedure TestMapCallback_CaseCollidingHint_GetsSuffix;
    procedure TestMap_SizeT_IsUInt64;
    procedure TestMap_SSizeT_IsInt64;
    procedure TestMap_StdintTypes;
    procedure TestMap_TimeT_IsInt64;
    procedure TestMap_VaList_IsPointer;
  end;

implementation

procedure TTypeMapTests.SetUp;
begin
  FMapper := TTypeMapper.Create();
end;

procedure TTypeMapTests.TearDown;
begin
  FMapper := nil;
end;

procedure TTypeMapTests.TestMap_Int_IsInteger;
begin
  AssertEquals('Integer', FMapper.Map('int'));
end;

procedure TTypeMapTests.TestMap_UnsignedInt_IsCardinal;
begin
  AssertEquals('Cardinal', FMapper.Map('unsigned int'));
end;

procedure TTypeMapTests.TestMap_Long_IsInt64;
begin
  AssertEquals('Int64', FMapper.Map('long'));
end;

procedure TTypeMapTests.TestMap_UnsignedLong_IsUInt64;
begin
  AssertEquals('UInt64', FMapper.Map('unsigned long'));
end;

procedure TTypeMapTests.TestMap_LongLong_IsInt64;
begin
  AssertEquals('Int64', FMapper.Map('long long'));
end;

procedure TTypeMapTests.TestMap_UnsignedLongLong_IsUInt64;
begin
  AssertEquals('UInt64', FMapper.Map('unsigned long long'));
end;

procedure TTypeMapTests.TestMap_Short_IsSmallInt;
begin
  AssertEquals('SmallInt', FMapper.Map('short'));
end;

procedure TTypeMapTests.TestMap_UnsignedShort_IsWord;
begin
  AssertEquals('Word', FMapper.Map('unsigned short'));
end;

procedure TTypeMapTests.TestMap_Char_IsByte;
begin
  AssertEquals('Byte', FMapper.Map('char'));
end;

procedure TTypeMapTests.TestMap_UnsignedChar_IsByte;
begin
  AssertEquals('Byte', FMapper.Map('unsigned char'));
end;

procedure TTypeMapTests.TestMap_Float_IsSingle;
begin
  AssertEquals('Single', FMapper.Map('float'));
end;

procedure TTypeMapTests.TestMap_Double_IsDouble;
begin
  AssertEquals('Double', FMapper.Map('double'));
end;

procedure TTypeMapTests.TestMap_Bool_IsBoolean;
begin
  AssertEquals('Boolean', FMapper.Map('_Bool'));
end;

procedure TTypeMapTests.TestMap_Void_IsEmpty;
begin
  { 'void' only occurs as a return type; the empty string tells the
    emitter to produce a procedure. }
  AssertEquals('', FMapper.Map('void'));
end;

procedure TTypeMapTests.TestMap_ConstQualifier_Stripped;
begin
  AssertEquals('Integer', FMapper.Map('const int'));
end;

procedure TTypeMapTests.TestMap_StructTag_Stripped;
begin
  AssertEquals('XPoint', FMapper.Map('struct XPoint'));
end;

procedure TTypeMapTests.TestMap_CharPtr_IsPChar;
begin
  AssertEquals('PChar', FMapper.Map('char *'));
end;

procedure TTypeMapTests.TestMap_ConstCharPtr_IsPChar;
begin
  AssertEquals('PChar', FMapper.Map('const char *'));
  { glibc writes restrict as a pointer suffix: 'char *restrict'. }
  AssertEquals('PChar', FMapper.Map('char *restrict'));
  AssertEquals('PChar', FMapper.Map('const char *restrict'));
end;

procedure TTypeMapTests.TestMap_VoidPtr_IsPointer;
begin
  AssertEquals('Pointer', FMapper.Map('void *'));
end;

procedure TTypeMapTests.TestMap_NamedPtr_IsPName_AliasRegistered;
begin
  AssertEquals('PDisplay', FMapper.Map('Display *'));
  AssertEquals(1, FMapper.PtrAliases.Count);
  AssertEquals('PDisplay', FMapper.PtrAliases[0].Name);
  AssertEquals('Display', FMapper.PtrAliases[0].Target);
end;

procedure TTypeMapTests.TestMap_CharPtrPtr_IsPPChar;
begin
  AssertEquals('PPChar', FMapper.Map('char **'));
  AssertEquals(1, FMapper.PtrAliases.Count);
  AssertEquals('PChar', FMapper.PtrAliases[0].Target);
end;

procedure TTypeMapTests.TestMap_PtrAlias_RegisteredOnlyOnce;
begin
  FMapper.Map('Display *');
  FMapper.Map('Display *');
  AssertEquals(1, FMapper.PtrAliases.Count);
end;

procedure TTypeMapTests.TestMap_PtrAlias_CaseInsensitiveDedup;
begin
  { SCREEN * and struct screen * fold to the same Pascal identifier —
    only one alias may be registered (Pascal is case-insensitive). }
  FMapper.Map('SCREEN *');
  FMapper.Map('screen *');
  AssertEquals(1, FMapper.PtrAliases.Count);
end;

procedure TTypeMapTests.TestMap_TypedefName_PassesThrough;
begin
  AssertEquals('XID', FMapper.Map('XID'));
end;

procedure TTypeMapTests.TestMap_FixedArray_IsStaticArray;
begin
  AssertEquals('array[0..3] of Integer', FMapper.Map('int[4]'));
end;

procedure TTypeMapTests.TestMap_FunctionPtr_IsPointer;
begin
  { Slice 1: function pointers degrade to an untyped Pointer.  A later
    slice will synthesise proper procedural types. }
  AssertEquals('Pointer', FMapper.Map('int (*)(Display *, int)'));
end;

procedure TTypeMapTests.TestFnPtrDecl_IntArgs_FunctionType;
begin
  AssertEquals('function(a0: PDisplay; a1: Integer): Integer',
    FMapper.FnPtrDecl('int (*)(Display *, int)'));
end;

procedure TTypeMapTests.TestFnPtrDecl_VoidReturn_ProcedureType;
begin
  AssertEquals('procedure(a0: Pointer)',
    FMapper.FnPtrDecl('void (*)(void *)'));
end;

procedure TTypeMapTests.TestFnPtrDecl_NoParams;
begin
  AssertEquals('function: Integer', FMapper.FnPtrDecl('int (*)(void)'));
end;

procedure TTypeMapTests.TestFnPtrDecl_Variadic_Fails;
begin
  { C varargs cannot be represented in a Blaise procedural type. }
  AssertEquals('', FMapper.FnPtrDecl('int (*)(Display *, ...)'));
end;

procedure TTypeMapTests.TestMapCallback_RegistersNamedType;
begin
  AssertEquals('TXSampleIfEvent_predicate',
    FMapper.MapCallback('int (*)(Display *, XID)', 'XSampleIfEvent_predicate'));
  AssertEquals('one synth type', 1, FMapper.ProcTypes.Count);
  AssertEquals('TXSampleIfEvent_predicate', FMapper.ProcTypes[0].Name);
  AssertEquals('function(a0: PDisplay; a1: XID): Integer',
    FMapper.ProcTypes[0].Decl);
end;

procedure TTypeMapTests.TestMapCallback_SameSignature_Deduped;
begin
  FMapper.MapCallback('int (*)(Display *, XID)', 'XSampleIfEvent_predicate');
  { An identical signature under a different hint reuses the first
    name — XIfEvent/XCheckIfEvent/XPeekIfEvent share one type. }
  AssertEquals('TXSampleIfEvent_predicate',
    FMapper.MapCallback('int (*)(Display *, XID)', 'XSampleCheckIfEvent_predicate'));
  AssertEquals(1, FMapper.ProcTypes.Count);
end;

procedure TTypeMapTests.TestMapCallback_NonFnPtr_FallsBackToMap;
begin
  AssertEquals('Integer', FMapper.MapCallback('int', 'ignored'));
  AssertEquals('Pointer', FMapper.MapCallback('int (*)(int, ...)', 'vararg_cb'));
end;

procedure TTypeMapTests.TestMapCallback_CaseCollidingHint_GetsSuffix;
begin
  { Hints differing only in case would synthesise Tfoo_cb and TFOO_CB —
    the same Pascal identifier.  The second must get a numeric suffix. }
  AssertEquals('Tfoo_cb',
    FMapper.MapCallback('int (*)(int)', 'foo_cb'));
  AssertEquals('TFOO_CB2',
    FMapper.MapCallback('void (*)(void *)', 'FOO_CB'));
  AssertEquals(2, FMapper.ProcTypes.Count);
end;

procedure TTypeMapTests.TestMap_SizeT_IsUInt64;
begin
  { size_t & friends are declared in system headers the file filter
    excludes, so the mapper must know them as builtins (LP64). }
  AssertEquals('UInt64', FMapper.Map('size_t'));
end;

procedure TTypeMapTests.TestMap_SSizeT_IsInt64;
begin
  AssertEquals('Int64', FMapper.Map('ssize_t'));
  AssertEquals('Int64', FMapper.Map('ptrdiff_t'));
end;

procedure TTypeMapTests.TestMap_StdintTypes;
begin
  AssertEquals('Byte', FMapper.Map('uint8_t'));
  AssertEquals('SmallInt', FMapper.Map('int16_t'));
  AssertEquals('Word', FMapper.Map('uint16_t'));
  AssertEquals('Integer', FMapper.Map('int32_t'));
  AssertEquals('Cardinal', FMapper.Map('uint32_t'));
  AssertEquals('Int64', FMapper.Map('int64_t'));
  AssertEquals('UInt64', FMapper.Map('uint64_t'));
  AssertEquals('Int64', FMapper.Map('intptr_t'));
  AssertEquals('UInt64', FMapper.Map('uintptr_t'));
end;

procedure TTypeMapTests.TestMap_TimeT_IsInt64;
begin
  AssertEquals('Int64', FMapper.Map('time_t'));
  AssertEquals('Int64', FMapper.Map('off_t'));
end;

procedure TTypeMapTests.TestMap_VaList_IsPointer;
begin
  AssertEquals('Pointer', FMapper.Map('va_list'));
end;

initialization
  RegisterTest(TTypeMapTests);

end.
