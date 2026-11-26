# The P-matrix linear complementarity problem lies in UEOPL, giving an expected 2^(n/2) poly(n)-time algorithm

Given $M\in\mathbb{Q}^{n\times n}$ and $q\in\mathbb{Q}^n$, the LCP asks for $z\ge0$ with $w=Mz+q\ge0$ and $z^{\top}w=0$. If $M$ is a P-matrix (all principal minors positive) the solution exists and is unique. Two total variants of P-LCP are considered: one accepting a solution or a non-positive principal minor together with violations that are other short certificates that $M$ is not a P-matrix, and one accepting a solution, a non-positive principal minor, or a third violation type modelled on the USO property. Whether the two variants are polynomial-time equivalent is not known. Both variants lie in UEOPL under promise-preserving reductions, so the promise version lies in PromiseUEOPL. Applying Aldous's algorithm to the produced instance solves P-LCP in expected time $2^{n/2}\mathrm{poly}(n)$.

## Proof sketch

Two different promise-preserving reductions are given, one for each variant. The difficulty is that the (UV2) and (UV3) violations of the produced instance, which certify several lines, do not map easily to non-positive principal minors; they do map to other short certificates that $M$ is not a P-matrix, in the first case, or to the USO-inspired violation, in the second. For a genuine P-matrix the produced instance has a single line ending at the unique LCP solution. Aldous's algorithm samples random vertices and follows the line from the best sample, using expected $2^{n/2}\mathrm{poly}(n)$ steps on a line with exact potential.

## Depends on

- [Unique Sink Orientations of cubes lie in UEOPL](unique-sink-orientation-in-ueopl.md)
- [UNIQUE-EOPL, the class UEOPL and PromiseUEOPL: one potential line certified by violation solutions](unique-eopl-and-ueopl.md)

## Proof depends on

- [Unique Sink Orientations of cubes lie in UEOPL](unique-sink-orientation-in-ueopl.md)
- [OPDC lies in UEOPL under promise-preserving reductions via a surface-walking line with a lexicographic potential](opdc-in-ueopl.md)

## Sources

- John Fearnley, Spencer Gordon, Ruta Mehta and Rahul Savani, "Unique End of Potential Line", ICALP (2019), arXiv:1811.03841.
