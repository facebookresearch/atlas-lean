# Polynomial splitting transported by tensor pushout

Let `k,K` be commutative rings with `Algebra k K`, `P` a simplicial `k`-algebra, and `s :
PolynomialSplitting k P`. The pushed-out simplicial algebra `P ⋙ algebraFunctor k K` has a
polynomial splitting obtained by mapping `s.splitting`. Its variable types remain `s.variables
n`, and its coordinates are `E(s.polynomialIso n)` followed by `freeAlgebraIso` on those
variables.
