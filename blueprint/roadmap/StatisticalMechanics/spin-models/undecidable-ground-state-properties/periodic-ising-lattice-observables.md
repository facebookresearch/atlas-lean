# Ground-state magnetization of periodic Ising lattices is undecidable

No algorithm decides, given a periodic Ising lattice on the half-plane, with integer interactions and a prescribed edge row, and a rational $p$, whether every ground state has magnetization $p$; this is the source's main example of an undecidable macroscopic observable.

**Setting (Gu, Weedbrook, Perales and Nielsen).** Spins $s_{\mathbf x} \in \{0, 1\}$ sit at the sites $\mathbf x$ of the half-plane $\mathbb Z \times \mathbb N$, whose row $\mathbb Z \times \{0\}$ is the *edge*. A finite Ising block is a $K \times K$ square of sites with a Hamiltonian
$$
H_K = \sum c_{\mathbf x, \mathbf y}\, s_{\mathbf x} s_{\mathbf y} + \sum M_{\mathbf x}\, s_{\mathbf x},
$$
in which only adjacent sites interact ($c_{\mathbf x, \mathbf y} = 0$ unless $|\mathbf x - \mathbf y|_1 = 1$); here the couplings $c_{\mathbf x, \mathbf y}$ and fields $M_{\mathbf x}$ are integers. The *periodic Ising lattice* with block Hamiltonian $H_K$ tessellates the half-plane by copies of the block, adjacent blocks sharing a row or column, every copy carrying $H_K$. The external field on the edge prescribes the edge spins: the edge row is fixed to an eventually periodic configuration $e \in \{0,1\}^{\mathbb Z}$, given by a finite word together with the periodic words it repeats to the left and to the right. The energy of the infinite lattice, a sum of infinitely many block energies, need not converge; following the source's construction from blocks whose energies are minimized simultaneously, a configuration $s$ is a *ground state* if it agrees with $e$ on the edge and the restriction of $s$ to every copy of the block minimizes $H_K$. The *magnetization* of $s$ is the density of $1$-spins,
$$
m(s) = \lim_{n \to \infty} \frac{\#\{\mathbf x \in [-n, n] \times [0, n] : s_{\mathbf x} = 1\}}{(2n+1)(n+1)},
$$
when this limit exists.

**Theorem (Gu, Weedbrook, Perales and Nielsen).** No algorithm decides, given a block Hamiltonian $H_K$ with integer couplings and fields, the finite description of an eventually periodic edge configuration $e$, and a rational number $p$, whether every ground state $s$ of the resulting periodic Ising lattice has a magnetization $m(s)$ and $m(s) = p$.

The source states its result as a "Rice's theorem for physical systems" (section "Undecidable Macroscopic Observables"): a macroscopic property $P$, a real-valued function of configurations, is *averaging* if for some tessellation into $C \times D$ blocks and some non-constant function $f$ of a block's configuration with block average $A(s)$, each value of $P$ excludes $A(s)$ from some interval, and then the source asserts that whether $P(s) = p$ at a ground state is undecidable. As printed the condition does not require the excluded interval to meet the range of $A$, so constant properties satisfy it; the magnetization, the case proved by the magnetization magnifier blocks, is the statement recorded here. The source applies the same method to finite-range correlations $\langle s_{l,m} s_{l,m+r} \rangle$ and $\langle s_{l,m} s_{l+r,m} \rangle$, where $\langle \cdot \rangle$ is the average over all lattice sites, and to the ground-state degeneracy, which determines the partition function at zero temperature; for the correlation length, the rate at which $\lim_{r \to \infty} \langle s_{l,m} s_{l,m+r} \rangle$ is approached, it uses a different reduction, from whether the encoded cellular automaton eventually has no live cells.

For finite Ising lattices, Gu and Perales relate these emergent properties to the NP-completeness of the ground-state decision problem for finite Ising lattices: whether a given Hamiltonian has a state of energy at most $0$.

## Depends on

- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Cellular automata on ℤ^d](../../../TheoryOfComputation/equivalence-of-models/cellular-automata/cellular-automata-on-z-d.md)
- [Halting is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)
- [Rule 110 is computationally universal](../../../TheoryOfComputation/equivalence-of-models/cellular-automata/rule-110-is-computationally-universal.md)

## Expansion

The proof encodes the evolution of a one-dimensional cellular automaton in the ground states of a two-dimensional periodic Ising lattice built from "designer" Ising blocks that implement the automaton's update rule, a three-way fan-out and a swap, with the edge row holding the initial condition; every ground state then encodes the run of the automaton from that initial condition (section "The Cellular Automata Encoding" and Appendix A of the source). With a universal automaton such as Rule 110, the *prosperity* of the run, the proportion of live cells averaged over all time steps, depends on the result of an encoded Turing machine, and the source infers that whether it is below $1/2$ is undecidable. Replacing the fan-out blocks by large "magnifier" blocks whose ground states are all $0$ or all $1$ according to their input makes the magnetization of the ground states reveal whether the prosperity is below $1/2$, so a decision procedure for the magnetization would decide it. A good expansion links pages for the designer-block encoding of a one-dimensional cellular automaton in Ising ground states, for the undecidability of the prosperity of a universal automaton, which universality alone does not give, and for the magnifier construction.

## Sources

- Mile Gu, Christian Weedbrook, Álvaro Perales and Michael A. Nielsen, "More really is different", *Physica D: Nonlinear Phenomena* 238(9–10), 2009, pp. 835–839, doi:[10.1016/j.physd.2008.12.016](https://doi.org/10.1016/j.physd.2008.12.016), with an erratum in *Physica D* 239(6), 2010, p. 340, doi:[10.1016/j.physd.2009.12.001](https://doi.org/10.1016/j.physd.2009.12.001) (not read); read in the author version arXiv:0809.0151v1, <https://arxiv.org/abs/0809.0151v1>: the sections "Reductionism and the Periodic Ising Lattice", "The Cellular Automata Encoding" and "Undecidable Macroscopic Observables", Appendix A ("Universality of Ising blocks"), and the "Discussion and Conclusion".
- Mile Gu and Álvaro Perales, "Encoding universal computation in the ground states of Ising lattices", *Physical Review E* 86(1), 2012, 011116, doi:[10.1103/PhysRevE.86.011116](https://doi.org/10.1103/PhysRevE.86.011116); read as arXiv:1204.1084v2, <https://arxiv.org/abs/1204.1084v2>: the abstract and Section V ("Computational Complexity and Emergence"), for the finite-lattice contrast.
- A. Perales-Eceiza, T. Cubitt, M. Gu, D. Pérez-García and M. M. Wolf, "Undecidability in physics: a review", *Physics Reports* 1138, 2025, pp. 1–29, doi:[10.1016/j.physrep.2025.06.004](https://doi.org/10.1016/j.physrep.2025.06.004); read as arXiv:2410.16532v2, <https://arxiv.org/abs/2410.16532v2>: Section 5.1.1 ("Classical Systems"), which presents both results as established.
