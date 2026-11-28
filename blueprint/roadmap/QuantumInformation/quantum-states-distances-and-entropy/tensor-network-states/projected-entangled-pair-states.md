# Projected entangled pair states

A translation-invariant projected entangled pair state (PEPS) on a square grid places one fixed five-index tensor at every site, contracts the virtual indices of neighboring sites, and closes the virtual indices on the boundary with a boundary condition; the result is a vector on the physical sites.

**Tensor.** A PEPS tensor is $A = \bigl(A^{i}_{\alpha_l \alpha_u \alpha_r \alpha_d}\bigr)$ with a *physical index* $i \in [d]$ and four *virtual indices* $\alpha_l, \alpha_u, \alpha_r, \alpha_d \in [D]$, for left, up, right and down.

**State on a patch.** For a patch of $N_h \times N_v$ sites, place a copy of $A$ at every site. Contract (identify and sum over) the right index of each site with the left index of its right neighbor, and the down index of each site with the up index of the site below it. The virtual indices that point out of the patch remain open; contract them with a *boundary condition*, a vector $\lvert b\rangle$ in the tensor product of the spaces $\mathbb{C}^D$ of the open boundary indices. The result is a coefficient $\mathcal{C}_A(\boldsymbol{i})$ for each assignment $\boldsymbol{i} = (i_{1,1}, \dots, i_{N_h,N_v})$ of physical indices, and the PEPS is

$$
\lvert \Psi_{N_h, N_v}\rangle = \sum_{\boldsymbol{i}} \mathcal{C}_A(\boldsymbol{i})\, \lvert \boldsymbol{i}\rangle \in (\mathbb{C}^d)^{\otimes N_h N_v}.
$$

The boundary condition may depend on the size of the patch. A PEPS without physical index ($d = 1$) is a scalar tensor network.

## Depends on

None.

## Proof depends on

None.

## Remarks

The family $\{\lvert\Psi_{N_h,N_v}\rangle\}$ describes states on arbitrarily large patches, and through them on the infinite plane. For a meaningful limit, properties in the bulk must become independent of the boundary condition, apart from selecting a symmetry-broken sector. If $\lvert\Psi_{N_h,N_v}\rangle = 0$ for every boundary condition, the tensor describes no normalizable state on that patch. One-dimensional matrix product states are the special case of a chain.

## Sources

- G. Scarpa, A. Molnár, Y. Ge, J. J. García-Ripoll, N. Schuch, D. Pérez-García and S. Iblisdir, "Projected entangled pair states: fundamental analytical and numerical limitations", *Physical Review Letters* 125(21), 210504, 2020, doi:[10.1103/PhysRevLett.125.210504](https://doi.org/10.1103/PhysRevLett.125.210504). Numbering of the version read, arXiv:1802.08214v2: the review of the PEPS formalism before the tiling problem, and Figure 1.
