# The kernel after prime localization

Let `A,B` be commutative semirings, `φ : A →+* B` a surjective homomorphism, and `p : Ideal B`
a prime ideal. Put `q = p.comap φ`. The induced prime-localization homomorphism `φ_loc :
Localization.AtPrime q → Localization.AtPrime p` satisfies `RingHom.ker φ_loc = (RingHom.ker
φ).map (algebraMap A (Localization.AtPrime q))`.
