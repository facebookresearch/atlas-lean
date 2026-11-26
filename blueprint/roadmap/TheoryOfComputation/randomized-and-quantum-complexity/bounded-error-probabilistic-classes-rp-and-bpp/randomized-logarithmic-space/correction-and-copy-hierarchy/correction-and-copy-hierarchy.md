# The correction-and-copy hierarchy

Fix a rate base $q=2^{c+1}$, a copy count $m$, and for each stage $l$ two families of random **retention channels** $X_l,Y_l$ over the vertices, each retaining a vertex with probability about $q^{-l}$. Starting from $C_0=S$ on $V_0=V$, stage $l+1$ lives on $V_{l+1}\cong V_l\times\{0,\dots,m\}$ ordered by parent then copy index; its transition matrix $C_{l+1}$ is obtained from $C_l$ by subtracting a **correction** whose entries are chosen by column detectors (exact expectations over the channel seeds of how much mass flows into heavily loaded columns) and redistributing the corrected mass over copies, and the reward vector of $C_l$ is transported along the copy maps. All stages are deterministic functions of $S$, the parameters and the channel laws.

## Depends on

- [Absorption rewards of strictly upper-triangular substochastic matrices](absorption-rewards.md)
- [Pairwise-independent hashing by affine maps over GF(2)](../../../../counting-complexity/counting-and-the-polynomial-hierarchy/pairwise-independent-hashing-by-affine-maps.md)

## Sources

- OpenAI, "Exact Derandomization of Logarithmic Space: L = RL = BPL", Preprint, 2026.
