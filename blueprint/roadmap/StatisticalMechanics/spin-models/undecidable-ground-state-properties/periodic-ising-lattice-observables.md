# Periodic Ising lattices with a prescribed edge

A periodic Ising lattice on the half-plane tessellates copies of one finite Ising block, with the spins of its edge row prescribed by an external field; its ground states are the configurations minimizing every block, and its magnetization is the density of $1$-spins.

**Definition (after Gu, Weedbrook, Perales and Nielsen).** Spins $s_{\mathbf x} \in \{0, 1\}$ sit at the sites $\mathbf x$ of the half-plane $\mathbb Z \times \mathbb N$, whose row $\mathbb Z \times \{0\}$ is the *edge*. A finite Ising block is a $K \times K$ square of sites with a Hamiltonian
$$
H_K = \sum c_{\mathbf x, \mathbf y}\, s_{\mathbf x} s_{\mathbf y} + \sum M_{\mathbf x}\, s_{\mathbf x},
$$
in which only adjacent sites interact ($c_{\mathbf x, \mathbf y} = 0$ unless $|\mathbf x - \mathbf y|_1 = 1$); here the couplings $c_{\mathbf x, \mathbf y}$ and fields $M_{\mathbf x}$ are integers. The *periodic Ising lattice* with block Hamiltonian $H_K$ tessellates the half-plane by copies of the block, adjacent blocks sharing a row or column, every copy carrying $H_K$. The external field on the edge prescribes the edge spins: the edge row is fixed to an eventually periodic configuration $e \in \{0,1\}^{\mathbb Z}$, given by a finite word together with the periodic words it repeats to the left and to the right. The energy of the infinite lattice, a sum of infinitely many block energies, need not converge; following the source's construction from blocks whose energies are minimized simultaneously, a configuration $s$ is a *ground state* if it agrees with $e$ on the edge and the restriction of $s$ to every copy of the block minimizes $H_K$. The *magnetization* of $s$ is the density of $1$-spins,
$$
m(s) = \lim_{n \to \infty} \frac{\#\{\mathbf x \in [-n, n] \times [0, n] : s_{\mathbf x} = 1\}}{(2n+1)(n+1)},
$$
when this limit exists.

Gu, Weedbrook, Perales and Nielsen encode the run of a one-dimensional cellular automaton in the ground states of such lattices, the edge holding the initial condition, and conclude that macroscopic ground-state observables such as the magnetization are undecidable (section "Undecidable Macroscopic Observables", item 1); the review of Perales-Eceiza et al. (Section 5.1.1) presents this as established. The source asks whether "$P(s) = p$ at ground state $s$" without fixing which ground states are meant, how the infinite-volume density is taken, or how the edge is given. These choices matter: for $H_K = 0$ and the all-zero edge, both the all-zero configuration and the one equal to $1$ everywhere above the edge minimize every block, with densities $0$ and $1$. The source thus states no precise decision problem about the magnetization. The source treats finite-range correlations $\langle s_{l,m} s_{l,m+r} \rangle$ and $\langle s_{l,m} s_{l+r,m} \rangle$, with $\langle \cdot \rangle$ the average over all sites, and the ground-state degeneracy in the same way, and the correlation length by a separate reduction, from whether the encoded automaton eventually has no live cells. Its general "Rice's theorem for physical systems" for *averaging* properties needs a condition tying the excluded interval to the range of the block average, since as printed constant properties satisfy it.

For finite Ising lattices, Gu and Perales relate these emergent properties to the NP-completeness of the ground-state decision problem: given an explicitly encoded finite square-lattice Ising Hamiltonian with integer coefficients and an integer threshold $E$, does some configuration have energy at most $E$? A threshold, or equivalently an additive constant in the Hamiltonian, is part of the input; with the threshold fixed at $0$ and no constant the all-zero configuration always has energy $0$ (Gu and Perales, Sections I and V, after Barahona).

## Depends on

None.

## Proof depends on

None.

## Expansion

In the source's construction (section "The Cellular Automata Encoding" and Appendix A), "designer" Ising blocks implement the automaton's update rule, a three-way fan-out and a swap, and every ground state encodes the run of the automaton from the initial condition on the edge. With a universal automaton (the source names Rule 110 among universal automata, and the Game of Life and Life without Death in its discussion of prosperity), the *prosperity* of the run, the proportion of live cells averaged over all time steps, depends on the result of an encoded Turing machine. Replacing the fan-out blocks by large "magnifier" blocks whose ground states are all $0$ or all $1$ according to their input makes the magnetization reveal whether the prosperity is below $1/2$. Stating the result as a theorem requires a source that fixes the decision problem: the encoding of the edge, the ground states quantified over, and the limit defining the density.

## Sources

- Mile Gu, Christian Weedbrook, Álvaro Perales and Michael A. Nielsen, "More really is different", *Physica D: Nonlinear Phenomena* 238(9–10), 2009, pp. 835–839, doi:[10.1016/j.physd.2008.12.016](https://doi.org/10.1016/j.physd.2008.12.016), with an erratum in *Physica D* 239(6), 2010, p. 340, doi:[10.1016/j.physd.2009.12.001](https://doi.org/10.1016/j.physd.2009.12.001) (not read); read in the author version arXiv:0809.0151v1, <https://arxiv.org/abs/0809.0151v1>: the sections "Reductionism and the Periodic Ising Lattice", "The Cellular Automata Encoding" and "Undecidable Macroscopic Observables", Appendix A ("Universality of Ising blocks"), and the "Discussion and Conclusion".
- Mile Gu and Álvaro Perales, "Encoding universal computation in the ground states of Ising lattices", *Physical Review E* 86(1), 2012, 011116, doi:[10.1103/PhysRevE.86.011116](https://doi.org/10.1103/PhysRevE.86.011116); read as arXiv:1204.1084v2, <https://arxiv.org/abs/1204.1084v2>: the abstract and Section V ("Computational Complexity and Emergence"), for the finite-lattice contrast.
- A. Perales-Eceiza, T. Cubitt, M. Gu, D. Pérez-García and M. M. Wolf, "Undecidability in physics: a review", *Physics Reports* 1138, 2025, pp. 1–29, doi:[10.1016/j.physrep.2025.06.004](https://doi.org/10.1016/j.physrep.2025.06.004); read as arXiv:2410.16532v2, <https://arxiv.org/abs/2410.16532v2>: Section 5.1.1 ("Classical Systems"), which presents both results as established.
