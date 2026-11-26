# Inverse-free Solovay-Kitaev compilation

Let $\mathcal{G} \subset \mathrm{SU}(d)$ be a finite set generating a dense subgroup, not necessarily closed under inverses, and containing an irreducible representation of a non-abelian finite group (up to phases) or more generally satisfying the hypothesis of Bouland and Giurgica-Tiron. Then every $U \in \mathrm{SU}(d)$ is approximated within $\varepsilon$ by a product of $O(\log^{c}(1/\varepsilon))$ elements of $\mathcal{G}$ for an absolute constant $c$ (about $8.62$), computable in polylogarithmic time.

## Proof sketch

Inverses are replaced by approximate inverses built from words whose product averages to a small multiple of the identity, using a finite group subset to symmetrize errors. A refined recursion based on group commutators of approximate inverses keeps error propagation polynomial, at the price of a larger polylogarithmic exponent.

## Depends on

- [Dense inverse-closed gate sets and epsilon-nets in SU(d)](dense-gate-sets-and-epsilon-nets.md)

## Proof depends on

- [Solovay-Kitaev theorem](solovay-kitaev-theorem.md)

## Sources

- Adam Bouland, Tudor Giurgica-Tiron, "Efficient universal quantum compilation: an inverse-free Solovay-Kitaev algorithm", arXiv:2112.02040 (2021).
