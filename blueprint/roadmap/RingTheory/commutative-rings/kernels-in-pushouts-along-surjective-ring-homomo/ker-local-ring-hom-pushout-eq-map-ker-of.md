# The pushout kernel after prime localization

Let `R,A,B,P` be commutative rings and `f,g,inl,inr` form the pushout square `R → A`, `R → B`,
`A → P`, `B → P`. Assume `g` and `inl` are surjective. Let `pB : Ideal B` and `pP : Ideal P`
be prime ideals with `g⁻¹(pB) = f⁻¹(inl⁻¹(pP))`.

Put `qR = g⁻¹(pB)` and `qA = inl⁻¹(pP)`. For the induced localization maps `g_loc : R_qR →
B_pB`, `inl_loc : A_qA → P_pP`, and `f_loc : R_qR → A_qA`, the kernel formula is `ker(inl_loc)
= (ker g_loc).map f_loc`.
