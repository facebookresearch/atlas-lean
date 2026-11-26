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
scalar, of modulus one because $V$ is unitary. Consequently the logical product unitaries induce on the code at most as
many distinct operators as $B / C$ has cosets, a finite number by compactness.

## Depends on

- [The logical unitaries in a compact Lie group form a Lie subgroup](logical-unitaries-in-a-lie-group-form-a-lie-subgroup.md)

## Proof depends on

- [The logical unitaries in a compact Lie group form a Lie subgroup](logical-unitaries-in-a-lie-group-form-a-lie-subgroup.md)

## Sources

- B. Eastin and E. Knill, *Restrictions on transversal encoded quantum gate sets*, Phys. Rev. Lett. 102 (2009), 110502, arXiv:0811.4262, proof of Theorem 1.
