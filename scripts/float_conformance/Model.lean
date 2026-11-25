/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Init
import Init.Data.Float.Model

-- Core-only runtime diagnostic. See README.md for author/source provenance.
@[noinline] def modelAdd (a b : UInt64) : UInt64 :=
  (Float.Model.add (Float.Model.ofBits a) (Float.Model.ofBits b)).toBits

@[noinline] def modelMul (a b : UInt64) : UInt64 :=
  (Float.Model.mul (Float.Model.ofBits a) (Float.Model.ofBits b)).toBits

def main (args : List String) : IO Unit := do
  let [input] := args | throw (IO.userError "expected input file")
  let text ← IO.FS.readFile input
  let mut count := 0
  for line in text.splitOn "\n" do
    if line.isEmpty then continue
    let [index, aText, bText] := line.splitOn " "
      | throw (IO.userError s!"invalid row: {line}")
    let some a := aText.toNat? | throw (IO.userError "invalid a")
    let some b := bText.toNat? | throw (IO.userError "invalid b")
    unless a < 2^64 && b < 2^64 do throw (IO.userError "not UInt64")
    let x := UInt64.ofNat a
    let y := UInt64.ofNat b
    IO.println s!"{index}|{a}|{b}|{modelAdd x y}|{modelMul x y}"
    count := count + 1
  unless count > 0 do throw (IO.userError "empty input")
