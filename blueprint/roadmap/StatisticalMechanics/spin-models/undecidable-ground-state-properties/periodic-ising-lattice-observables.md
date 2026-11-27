# Macroscopic ground-state observables of periodic Ising lattices are undecidable

For two-dimensional periodic Ising lattices whose spins along one edge are fixed by an external field, the ground-state magnetization, correlation length, finite-range correlations and zero-temperature partition function cannot in general be computed from the lattice's interactions.

**Setting (Gu, Weedbrook, Perales and Nielsen).** An Ising lattice on the square grid has spins $s_{\mathbf x} \in \{0, 1\}$ and energy

$$
H = \sum c_{\mathbf x, \mathbf y}\, s_{\mathbf x} s_{\mathbf y} + \sum M_{\mathbf x}\, s_{\mathbf x},
$$

where only adjacent spins interact ($c_{\mathbf x, \mathbf y} = 0$ unless $|\mathbf x - \mathbf y|_1 = 1$) and $M_{\mathbf x}$ is an external field; ground states are configurations minimizing $H$. The lattice is *periodic* if it is a tessellation of copies of one $K \times K$ block with the same Hamiltonian $H_K$, adjacent blocks sharing a row or column. The source considers macroscopic lattices of this kind in which the spins of a one-dimensional edge are fixed by a spatially varying external field. A *macroscopic property* is a function $P$ from configurations to real numbers; it is *averaging* if, for some tessellation into $C \times D$ blocks and some non-constant function $f$ of a block's configuration, each value of $P$ excludes the block average of $f$ from some nondegenerate interval $[a, b]$.

**Theorem (Gu, Weedbrook, Perales and Nielsen).** For every averaging macroscopic property $P$, the value of $P$ at the ground state of such a periodic Ising lattice cannot in general be computed from the block Hamiltonian $H_K$: no algorithm computes it correctly for all such lattices. In particular the ground-state magnetization, the correlation length, finite-range correlations $\langle s_{l,m} s_{l,m+r}\rangle$ and $\langle s_{l,m} s_{l+r,m}\rangle$, and the partition function at zero temperature (determined by the ground-state degeneracy) are not computable in this sense.

The results concern infinite lattices. For finite Ising lattices, Gu and Perales relate these emergent properties to the NP-completeness of finding ground states of finite Ising spin glasses.

## Depends on

None.

## Proof depends on

- [Cellular automata on ℤ^d](../../../TheoryOfComputation/equivalence-of-models/cellular-automata/cellular-automata-on-z-d.md)
- [Halting is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The proof encodes the evolution of any one-dimensional cellular automaton in the ground states of a two-dimensional periodic Ising lattice built from "designer" Ising blocks that implement logic gates, with the fixed edge holding the initial condition; this encoding has no page here. Using a universal cellular automaton, the *prosperity* of the automaton (the long-run proportion of live cells) depends on the result of an encoded Turing machine and is therefore undecidable, a form of Rice's theorem without a page here. Replacing the fan-out blocks by large "magnifier" blocks whose ground states have very different values of $f$ makes the block average of $f$ reveal whether the prosperity is below $1/2$, so a decision procedure for $P$ would decide it. For the correlation length the source instead reduces from whether the encoded automaton eventually has no live cells, a result of Wolfram without a page here.

## Sources

- Mile Gu, Christian Weedbrook, Álvaro Perales and Michael A. Nielsen, "More really is different", *Physica D: Nonlinear Phenomena* 238(9–10), 2009, pp. 835–839, doi:[10.1016/j.physd.2008.12.016](https://doi.org/10.1016/j.physd.2008.12.016), with an erratum in *Physica D* 239(6), 2010, p. 340, doi:[10.1016/j.physd.2009.12.001](https://doi.org/10.1016/j.physd.2009.12.001) (not read); read in the author version arXiv:0809.0151v1, <https://arxiv.org/abs/0809.0151v1>: the sections "Reductionism and the Periodic Ising Lattice", "The Cellular Automata Encoding" and "Undecidable Macroscopic Observables", and the "Discussion and Conclusion".
- Mile Gu and Álvaro Perales, "Encoding universal computation in the ground states of Ising lattices", *Physical Review E* 86(1), 2012, 011116, doi:[10.1103/PhysRevE.86.011116](https://doi.org/10.1103/PhysRevE.86.011116); read as arXiv:1204.1084v2, <https://arxiv.org/abs/1204.1084v2>: the abstract and Section V ("Computational Complexity and Emergence"), for the finite-lattice contrast.
- A. Perales-Eceiza, T. Cubitt, M. Gu, D. Pérez-García and M. M. Wolf, "Undecidability in physics: a review", *Physics Reports* 1138, 2025, pp. 1–29, doi:[10.1016/j.physrep.2025.06.004](https://doi.org/10.1016/j.physrep.2025.06.004); read as arXiv:2410.16532v2, <https://arxiv.org/abs/2410.16532v2>: Section 5.1.1 ("Classical Systems"), which presents both results as established.
