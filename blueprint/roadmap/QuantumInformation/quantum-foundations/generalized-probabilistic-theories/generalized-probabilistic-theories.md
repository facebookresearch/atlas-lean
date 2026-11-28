# Generalized probabilistic theories and consistency of transformations

A single-party generalized probabilistic theory is a pair of state and effect sets in $\mathbb{R}^{d+1}$ whose pairings are probabilities; a finite set of normalization-preserving linear maps is consistent when some such theory stays valid under every product of the maps.

**Single-party GPTs.** Let $C(\mathcal{S}), C(\mathcal{E}) \subset \mathbb{R}^{d+1}$ be proper cones (convex, closed, pointed and generating) with $e^\top \omega \ge 0$ for all $e \in C(\mathcal{E})$ and $\omega \in C(\mathcal{S})$, and let $u$ be an interior point of $C(\mathcal{E})$, the *unit effect*. The normalized states are $\mathcal{S} = \{\omega \in C(\mathcal{S}) : u^\top \omega = 1\}$ and the physical effects are $\mathcal{E} = C(\mathcal{E}) \cap (u - C(\mathcal{E}))$; the probability of effect $e$ in state $\omega$ is $e^\top \omega$. A pair $(\mathcal{S}_0, \mathcal{E}_0)$ of normalized states and physical effects satisfying these axioms is a *single-party GPT* when the states have affine dimension $d$ and the effects span $\mathbb{R}^{d+1}$ (the generated cones are full dimensional).

**Candidate transformations.** A *generating set of candidate transformations* is a finite set $\mathcal{T}_0 = \{T_1, \dots, T_K\}$ of linear maps of $\mathbb{R}^{d+1}$ with $u^\top T_i = u^\top$ for all $i$. For a word $w = k_1 \cdots k_L \in \{1, \dots, K\}^L$ ($L \ge 0$) let $T_w = T_{k_L} \cdots T_{k_1}$, the empty word giving the identity, and let $\mathcal{T}_{\mathrm{gen}}$ be the set of all $T_w$.

**Consistency.** A triple $(\mathcal{S}_0, \mathcal{E}_0, \mathcal{T}_0)$, with $(\mathcal{S}_0, \mathcal{E}_0)$ a single-party GPT, is *consistent* if $(\mathcal{S}_{\mathrm{gen}}, \mathcal{E}_0)$ is a single-party GPT, where $\mathcal{S}_{\mathrm{gen}}$ is the closed convex hull of $\{T_w \omega : \omega \in \mathcal{S}_0, w \text{ a word}\}$; equivalently,

$$
e^\top T_w \omega \ge 0 \quad \text{for all } \omega \in \mathcal{S}_0,\ e \in \mathcal{E}_0 \text{ and words } w.
$$

The set $\mathcal{T}_0$ alone is *consistent* if there exist a normalized state space $\mathcal{S}_0$ of affine dimension $d$ and a full-dimensional physical effect space $\mathcal{E}_0$ such that $(\mathcal{S}_0, \mathcal{E}_0, \mathcal{T}_0)$ is consistent.

## Depends on

None.

## Proof depends on

None.

## Sources

- Serge Massar, "Undecidability of consistency of generalized probabilistic theories", *Physical Review A* 114(4):042201, 2026, doi:[10.1103/42zl-6wmw](https://doi.org/10.1103/42zl-6wmw). Numbering of the version read, arXiv:2603.07002v4: Section II.A (single systems), Section II.B (transformations) and Section IV.A (definitions and consistency conditions).
