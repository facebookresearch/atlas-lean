# Decoding a pair of naturals fails exactly on a malformed first frame

Pair Nat decoding fails exactly when the first frame is malformed;
both raw field payloads use Mathlib's total Nat decoder.
