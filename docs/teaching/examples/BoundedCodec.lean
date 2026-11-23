/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
Clause map for the bounded length-prefixed codec (teaching example; not a
production protocol, not a parser framework).

Format: a byte is `BitVec 8`, read unsigned via `BitVec.toNat` (0-255).
A payload is any list of bytes of length `n`. A frame is exactly `n + 2`
bytes: header bytes `H0 = byte (n / 256)` and `H1 = byte (n % 256)`
(unsigned 16-bit big-endian length), then the payload in order. There is
no escaping, terminator, padding, or checksum.

Domain: payload lengths `n ≤ 65535`. `encode` returns `none` exactly
when `65535 < p.length`.

Full-input decoding: `decode` consumes the whole input list and never
returns a remainder. Fewer than two bytes gives `none`; otherwise, with
`L = H0.toNat * 256 + H1.toNat`, it returns the body exactly when the
body length equals `L`. A truncated body and trailing bytes are both
plain `none` (no error taxonomy).

Out of scope: streaming or remainder decoding, concatenated frames,
`n ≥ 65536`, `UInt8`/`ByteArray` runtime types, text/UTF-8/JSON, and any
wire-protocol claim.
-/

namespace BoundedCodec

abbrev Byte := BitVec 8

def encode (p : List Byte) : Option (List Byte) :=
  if p.length ≤ 65535 then
    some (BitVec.ofNat 8 (p.length / 256) :: BitVec.ofNat 8 (p.length % 256) :: p)
  else
    none

def decode : List Byte → Option (List Byte)
  | [] => none
  | [_] => none
  | hi :: lo :: rest =>
    if rest.length = hi.toNat * 256 + lo.toNat then some rest else none

theorem encode_eq_none_iff (p : List Byte) :
    encode p = none ↔ 65535 < p.length := by
  unfold encode
  by_cases h : p.length ≤ 65535 <;> simp [h] <;> omega

#print axioms encode_eq_none_iff

theorem encode_length (p bs : List Byte) (h : encode p = some bs) :
    bs.length = p.length + 2 := by
  unfold encode at h
  by_cases hc : p.length ≤ 65535
  · simp [hc] at h
    subst h
    simp only [List.length_cons] <;> omega
  · simp [hc] at h

#print axioms encode_length

theorem header_toNat (n : Nat) (h : n ≤ 65535) :
    (BitVec.ofNat 8 (n / 256)).toNat * 256 + (BitVec.ofNat 8 (n % 256)).toNat = n := by
  have h8 : (2 : Nat) ^ 8 = 256 := by decide
  simp only [BitVec.toNat_ofNat, h8]
  omega

#print axioms header_toNat

theorem header_ofNat (hi lo : Byte) :
    BitVec.ofNat 8 ((hi.toNat * 256 + lo.toNat) / 256) = hi ∧
    BitVec.ofNat 8 ((hi.toNat * 256 + lo.toNat) % 256) = lo := by
  have h8 : (2 : Nat) ^ 8 = 256 := by decide
  have hhi : hi.toNat < 256 := by
    have hlt := BitVec.isLt hi
    rw [h8] at hlt
    exact hlt
  have hlo : lo.toNat < 256 := by
    have hlt := BitVec.isLt lo
    rw [h8] at hlt
    exact hlt
  constructor
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, h8]
    omega
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, h8]
    omega

#print axioms header_ofNat

theorem decode_nil : decode [] = none :=
  rfl

#print axioms decode_nil

theorem decode_singleton (b : Byte) : decode [b] = none :=
  rfl

#print axioms decode_singleton

theorem decode_cons_cons (hi lo : Byte) (rest : List Byte) :
    decode (hi :: lo :: rest) =
      (if rest.length = hi.toNat * 256 + lo.toNat then some rest else none) :=
  rfl

#print axioms decode_cons_cons

theorem decode_eq_some_iff (bs p : List Byte) :
    decode bs = some p ↔
      ∃ hi lo : Byte, bs = hi :: lo :: p ∧ p.length = hi.toNat * 256 + lo.toNat := by
  cases bs with
  | nil =>
    simp [decode_nil]
  | cons b bs =>
    cases bs with
    | nil =>
      simp [decode_singleton]
    | cons c cs =>
      rw [decode_cons_cons]
      constructor
      · intro hsome
        by_cases h : cs.length = b.toNat * 256 + c.toNat
        · simp [h] at hsome
          subst hsome
          exact ⟨b, c, rfl, h⟩
        · simp [h] at hsome
      · rintro ⟨hi, lo, heq, hlen⟩
        simp at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        simp [hlen]

#print axioms decode_eq_some_iff

theorem decode_encode (p bs : List Byte) (h : encode p = some bs) :
    decode bs = some p := by
  unfold encode at h
  by_cases hc : p.length ≤ 65535
  · simp [hc] at h
    subst h
    rw [decode_cons_cons]
    split
    · simp
    · simp
      have hh := header_toNat p.length hc
      omega
  · simp [hc] at h

#print axioms decode_encode

theorem decode_encode_of_le (p : List Byte) (h : p.length ≤ 65535) :
    (encode p).bind decode = some p := by
  have he : encode p = some (BitVec.ofNat 8 (p.length / 256) ::
      BitVec.ofNat 8 (p.length % 256) :: p) := by
    unfold encode
    simp [h]
  rw [he, Option.bind_some, decode_cons_cons]
  split
  · simp
  · simp
    have hh := header_toNat p.length h
    omega

#print axioms decode_encode_of_le

theorem encode_decode (bs p : List Byte) (h : decode bs = some p) :
    encode p = some bs := by
  obtain ⟨hi, lo, rfl, hlen⟩ := (decode_eq_some_iff bs p).mp h
  have h8 : (2 : Nat) ^ 8 = 256 := by decide
  have hhi : hi.toNat < 256 := by
    have hlt := BitVec.isLt hi
    rw [h8] at hlt
    exact hlt
  have hlo : lo.toNat < 256 := by
    have hlt := BitVec.isLt lo
    rw [h8] at hlt
    exact hlt
  have hle : p.length ≤ 65535 := by omega
  have he : encode p = some (BitVec.ofNat 8 (p.length / 256) ::
      BitVec.ofNat 8 (p.length % 256) :: p) := by
    unfold encode
    simp [hle]
  have ho := header_ofNat hi lo
  rw [hlen, ho.1, ho.2] at he
  exact he

#print axioms encode_decode

theorem decode_eq_none_of_length_ne (hi lo : Byte) (rest : List Byte)
    (h : rest.length ≠ hi.toNat * 256 + lo.toNat) :
    decode (hi :: lo :: rest) = none := by
  rw [decode_cons_cons]
  simp [h]

#print axioms decode_eq_none_of_length_ne

-- W1
example : encode [] = some [0, 0] := by decide

-- W2
example : decode [0, 1, 7] = some [7] := by decide

-- W3
#guard (encode (List.replicate 255 0)).map (List.take 2) == some [0, 255]

-- W4
#guard (encode (List.replicate 256 0)).map (List.take 2) == some [1, 0]

-- W5
example : (encode (List.replicate 65535 (0 : Byte))).bind decode
    = some (List.replicate 65535 0) :=
  decode_encode_of_le (List.replicate 65535 0) (by simp only [List.length_replicate]; decide)

#guard (encode (List.replicate 65535 (0 : Byte))).map (List.take 2) == some [255, 255]

-- W6
example : encode (List.replicate 65536 (0 : Byte)) = none :=
  (encode_eq_none_iff (List.replicate 65536 0)).mpr
    (by simp only [List.length_replicate]; decide)

#guard encode (List.replicate 65536 (0 : Byte)) == none

-- W7
example : decode ([] : List Byte) = none := by decide
example : decode [0] = none := by decide

-- W8
example : decode [0, 1] = none := by decide

#guard decode ([1, 0] ++ List.replicate 255 0) == none

-- W9
example : decode [0, 1, 7, 9] = none := by decide

-- W10
example : decode [1, 0, 7] = none := by decide

end BoundedCodec
