# The stars-and-bars count of monotone tuples

For all `n,m : ℕ`, `Fintype.card {f : Fin n → Fin m // Monotone f} = Nat.choose (m+n-1) n`,
with subtraction in `ℕ`. The empty tuple is included; when `m=0` and `n>0`, no such tuple
exists.
