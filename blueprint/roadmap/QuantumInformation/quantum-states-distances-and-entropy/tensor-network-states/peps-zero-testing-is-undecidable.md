# Zero testing of projected entangled pair states is undecidable

No algorithm decides, given a PEPS tensor with entries in $\{0, 1\}$, whether some choice of boundary conditions makes the state it generates nonzero on every patch size. The problem stays undecidable for tensors without a physical index.

**Theorem (Scarpa, Molnár, Ge, García-Ripoll, Schuch, Pérez-García and Iblisdir).** The following problem is undecidable, already for tensors with entries in $\{0, 1\}$: given a tensor $A$ of a [projected entangled pair state](projected-entangled-pair-states.md), is there a choice of boundary conditions, allowed to depend on the patch size, such that the PEPS $\lvert\Psi_{N_h,N_v}\rangle$ constructed from $A$ is nonzero for every patch size $N_h \times N_v$? (Undecidable problem 1 of the source.)

The source notes that the result holds even for PEPS without a physical index, and for PEPS that represent a product state when they are nonzero. A negative answer means that the tensor has no well-defined thermodynamic limit. The source derives from it further undecidable problems: whether a PEPS is invariant under a given on-site symmetry in the thermodynamic limit, whether two PEPS tensors describe the same PEPS, in the sense that the reduced density matrices of the two states on a fixed region become indistinguishable as the boundaries are taken to infinity, and whether the parent Hamiltonian of a PEPS is gapped.

## Depends on

- [Projected entangled pair states](projected-entangled-pair-states.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Remarks

Given a finite set $\mathcal{T}$ of Wang tiles $t = (c_l, c_u, c_r, c_d)$, take the physical dimension equal to $\lvert\mathcal{T}\rvert$ and set $A^{t}_{\alpha_l\alpha_u\alpha_r\alpha_d} = 1$ if $t = (\alpha_l, \alpha_u, \alpha_r, \alpha_d)$ and $0$ otherwise. Contracting the virtual indices forces the colors on shared edges to agree, so $\mathcal{C}_A(\boldsymbol{t}) = 0$ unless $\boldsymbol{t}$ is a valid tiling of the patch, and otherwise $\mathcal{C}_A(\boldsymbol{t})$ is the overlap of the boundary condition with the boundary colors of $\boldsymbol{t}$. If $\mathcal{T}$ cannot tile the plane, there is a patch size above which no valid tiling exists, and the PEPS vanishes there for every boundary condition. If $\mathcal{T}$ tiles the plane, the uniform superposition of colors as boundary condition gives a nonzero PEPS for every size. The variant $\tilde{A}^{i}_{\alpha_l\alpha_u\alpha_r\alpha_d} = 1$ when $i = 0$ and $(\alpha_l, \alpha_u, \alpha_r, \alpha_d) \in \mathcal{T}$, and $0$ otherwise, gives a PEPS of the product state $\lvert 0\rangle^{\otimes N}$ whose norm counts valid tilings. In both constructions the tensors have entries $0$ and $1$.

## Sources

- G. Scarpa, A. Molnár, Y. Ge, J. J. García-Ripoll, N. Schuch, D. Pérez-García and S. Iblisdir, "Projected entangled pair states: fundamental analytical and numerical limitations", *Physical Review Letters* 125(21), 210504, 2020, doi:[10.1103/PhysRevLett.125.210504](https://doi.org/10.1103/PhysRevLett.125.210504). Numbering of the version read, arXiv:1802.08214v2: Undecidable problem 1 (PEPS zero testing), Equation (1) (the tensor from a tile set) and the discussion following it, and Undecidable problems 2, 3 and 4.
