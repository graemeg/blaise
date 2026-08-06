{
  Blaise - An Object Pascal Compiler
  Copyright (c) 2026 Andrew Haines
  SPDX-License-Identifier: Apache-2.0 WITH Swift-exception
  Licensed under the Apache License v2.0 with Runtime Library Exception.
  See LICENSE file in the project root for full license terms.
}

{ uCompilerId — single source of truth for the compiler's identity
  string.  Stamped into every .bif written by this compiler.

  When a .bif is loaded and the matching source .pas isn't available
  on the unit-path, an exact COMPILER_ID match is the only signal
  the .bif is safe to trust.  Bumping COMPILER_ID forces re-emit of
  every .bif (since old ones won't match), which is what we want
  any time codegen or the .bif schema changes in a way the iface
  alone doesn't capture.

  Convention: 'blaise-<semver>+<short-suffix>'.  Bump the suffix on
  codegen-affecting changes; bump semver on language-level changes. }

unit uCompilerId;

interface

const
  COMPILER_ID = 'blaise-0.14.0+bif4';

implementation

end.
