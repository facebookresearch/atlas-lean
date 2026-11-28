# OPDC is UEOPL-complete, even on the Boolean hypercube, and its promise version is PromiseUEOPL-complete

There is a polynomial-time promise-preserving reduction from UNIQUE-EOPL to OPDC whose output has point set $P=\{0,1\}^n$. Hence OPDC is UEOPL-complete, the violation-free variant of OPDC is PromiseUEOPL-complete, and OPDC is the first non-trivial UEOPL-complete problem. Producing such instances in which every slice, not only every $i$-slice, has a unique fixpoint would be a necessary step towards UEOPL-hardness of contraction or of USO; for contraction one would further have to turn the discrete instance into a continuous contraction map.

## Proof sketch

Normalise the UNIQUE-EOPL instance so that every edge raises the potential by exactly one and every line end has potential $2^n-1$ (dummy chains, with $n$ large enough). Embed the main line of length $2^n$ into the hypercube recursively: its second half goes into one designated sub-cube and its first half into the others, and each half is split again. The only fixpoint of the resulting orientation is the end of the line; if the source instance has violations the embedding can fail, but every failure is converted back into a UNIQUE-EOPL violation.

## Depends on

- [One-Permutation Discrete Contraction (OPDC): direction functions on a grid with unique fixpoints on i-slices](one-permutation-discrete-contraction.md)
- [UNIQUE-EOPL, the class UEOPL and PromiseUEOPL: one potential line certified by violation solutions](unique-eopl-and-ueopl.md)

## Proof depends on

- [OPDC lies in UEOPL under promise-preserving reductions via a surface-walking line with a lexicographic potential](opdc-in-ueopl.md)

## Sources

- John Fearnley, Spencer Gordon, Ruta Mehta and Rahul Savani, "Unique End of Potential Line", ICALP (2019), arXiv:1811.03841.
