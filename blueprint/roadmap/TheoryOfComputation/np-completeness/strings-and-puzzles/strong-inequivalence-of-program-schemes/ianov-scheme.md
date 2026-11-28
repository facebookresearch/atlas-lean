# Ianov schemes

In STRONG INEQUIVALENCE OF IANOV SCHEMES, an Ianov scheme is a list `I₁, …, Iₘ` of instructions, each encoded as a quadruple of natural numbers (type `List (ℕ × ℕ × ℕ × ℕ)`): `(0, r, 0, 0)` is the assignment `x ← f_r(x)`, `(1, r, j, k)` is the test `if p_r(x) then goto Iⱼ else goto Iₖ`, and `(2, 0, 0, 0)` is `halt`.
