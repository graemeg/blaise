{
  Blaise stdlib - TOML reader
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ Blaise stdlib - TOML reader facade.

  GetTOML parses a TOML document string into the Toml.Types tree by driving
  the Toml.Parser engine, and returns the root table.  The caller owns the
  returned root (parent-owns-child); releasing it frees the whole tree.
  ETOMLParseError (with Line and Column) is raised on malformed input.
}

unit Toml.Reader;

interface

uses
  Toml.Types, Toml.Parser;

{ Parse AText into a TOML tree.  Raises ETOMLParseError on malformed input. }
function GetTOML(const AText: string): TTOMLTable;

implementation

function GetTOML(const AText: string): TTOMLTable;
var
  P: TTOMLParser;
begin
  P := TTOMLParser.Create(AText);
  try
    Result := P.Parse();
  finally
    P.Free();
  end;
end;

end.
