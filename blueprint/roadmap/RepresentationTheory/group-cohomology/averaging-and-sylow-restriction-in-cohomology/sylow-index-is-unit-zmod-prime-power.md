# Sylow index is a unit modulo a prime power

Let `G : Type` be a finite group, `p : ℕ` prime, `P : Sylow p G`, and `d : ℕ` with `0 < d`.
Then `IsUnit (P.index : ZMod (p ^ d))`; equivalently, the subgroup index `[G:P]` is invertible
modulo `p^d`, since `p` does not divide this index.
