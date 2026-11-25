# THREE-DIMENSIONAL STABLE MATCHING is NP-complete

The THREE-DIMENSIONAL STABLE MATCHING decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: three disjoint sets `A` (women), `B` (men) and `D` (dogs) with `|A| = |B| = |D| = n`; every woman `a ∈ A` has a strict total order over the pairs `B × D`, every man over `A × D`, and every dog over `A × B`. A family is a triple `abd` with `a ∈ A`, `b ∈ B`, `d ∈ D`; a marriage is a set of `n` pairwise disjoint families, so that every agent lies in exactly one family. A triple `abd` is unstable for a marriage `M` if `a`, `b` and `d` each strictly prefer the triple `abd` to their assigned family in `M`: `a` prefers `bd` to its partners in `M`, `b` prefers `ad` to its partners, and `d` prefers `ab` to its partners. Question: is there a stable marriage, i.e., a marriage with no unstable triple?

## Sources

- C. Ng and D. S. Hirschberg, "Three-dimensional stable matching problems", SIAM Journal on Discrete Mathematics 4 (1991), 245-252, doi:10.1137/0404023.
- problem definition as restated by R. Ostrovsky and W. Rosenbaum, "It's not easy being three: the approximability of three-dimensional stable matching problems", arXiv:1412.1130 (2014), Section 2.1.
