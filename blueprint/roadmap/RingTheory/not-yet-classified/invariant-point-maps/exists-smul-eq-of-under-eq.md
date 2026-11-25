# Primes with the same contraction to an invariant ring are conjugate

If `A → B` is an
invariant extension for a finite group `G`, two primes of `B` with the same contraction to `A`
differ by an element of `G`. Unlike Mathlib's `Algebra.IsInvariant.exists_smul_of_under_eq`, the
action of `G` need not commute with `A`: the argument runs over the fixed subring of `B`, which
lies in the image of `A` and on which `G` acts trivially.
