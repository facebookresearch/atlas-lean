# The identity component of the logical product unitaries acts on the code as a phase

Let $\mathcal{H} = \mathcal{H}_1 \otimes \dots \otimes \mathcal{H}_n$ be finite-dimensional, let $P$ project onto a code
that detects every error on a single subsystem ($P E P \in \mathbb{C} P$ for every $E$ acting on one $\mathcal{H}_j$), and
let $C$ be the identity component of the [Lie group of logical product unitaries](logical-unitaries-in-a-lie-group-form-a-lie-subgroup.md).
Then every $V \in C$ acts on the code as a scalar: $V P = e^{i\phi} P$ for some $\phi \in \mathbb{R}$.

Proof: each element of $C$ is a product of exponentials $e^{iD_k}$ with $D_k$ in the Lie algebra $\mathfrak{c}$ of $C$,
and $e^{i\epsilon D} \in C$ is logical for all real $\epsilon$, so differentiating $(I - P) e^{i\epsilon D} P = 0$ at
$\epsilon = 0$ gives $(I - P) D P = 0$. Since $\mathfrak{c}$ lies in the Lie algebra of the product unitaries,
$D = \sum_j \alpha_j H_j$ with $H_j$ Hermitian acting on $\mathcal{H}_j$ only, and local error detection gives
$P H_j P \in \mathbb{C} P$. Hence $D P = P D P \in \mathbb{C} P$, so each $e^{iD_k}$, and $V$, acts on the code as a
scalar, of modulus one because $V$ is unitary. Consequently, if $G$ is the group of logical product unitaries and $\mathcal{F}$ contains one element of each coset of
$C$ in $G$, which are finitely many because $G$ is compact and $C$ is open in it, then every $U \in G$ satisfies
$U P = e^{i\phi} F P$ for some $F \in \mathcal{F}$ and $\phi \in \mathbb{R}$: up to a global phase, the logical product
unitaries induce only finitely many distinct operators on the code.

## Depends on

- [The logical unitaries in a compact Lie group form a Lie subgroup](logical-unitaries-in-a-lie-group-form-a-lie-subgroup.md)

## Proof depends on

- [Lie groups: the exponential map, closed subgroups and maximal compact subgroups](../../../RepresentationTheory/lie-and-topological-representations/lie-groups-exponential-map-and-maximal-compact-subgroups.md): the exponential image contains a neighbourhood of the identity, so the subgroup it generates is open and equals the identity component
- [The logical unitaries in a compact Lie group form a Lie subgroup](logical-unitaries-in-a-lie-group-form-a-lie-subgroup.md): the identity component is a connected Lie subgroup of finite index

## Sources

- B. Eastin and E. Knill, *Restrictions on transversal encoded quantum gate sets*, Phys. Rev. Lett. 102 (2009), 110502, arXiv:0811.4262, proof of Theorem 1, which leaves the global phase implicit.
