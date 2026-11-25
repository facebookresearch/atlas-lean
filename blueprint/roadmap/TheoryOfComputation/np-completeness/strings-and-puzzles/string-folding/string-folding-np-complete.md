# STRING FOLDING is NP-complete

The STRING FOLDING decision problem in dimension `3` (foldings into the cubic lattice `ℤ³`) lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a finite alphabet `Σ`, a finite string `s` over `Σ`, and a positive integer `K`. Question: is there a folding of `s` in the cubic lattice `ℤ³`, i.e., a mapping of the symbols of `s` into `ℤ³` such that adjacent symbols of `s` are adjacent in the lattice and no site is occupied by more than one symbol, with at least `K` pairs of equal symbols that lie at adjacent lattice sites, excluding pairs that are adjacent in `s`?

## Sources

- M. Paterson and T. Przytycka, "On the complexity of string folding", Discrete Applied Mathematics 71 (1996), 217-230, doi:10.1016/S0166-218X(96)00065-0.
- P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000), problem MAXIMUM STRING FOLDING (decision version).
