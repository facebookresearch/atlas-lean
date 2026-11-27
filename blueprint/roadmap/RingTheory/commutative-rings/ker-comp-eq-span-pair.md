# The composite kernel has two defining equations

Let `A,B,C` be commutative rings, `f : A →+* B` a surjective homomorphism, and `g : B →+* C` a
homomorphism. For `a,b : A`, suppose `RingHom.ker f = Ideal.span {a}` and `RingHom.ker g =
Ideal.span {f b}`. Then `RingHom.ker (g.comp f) = Ideal.span {a,b}`.
