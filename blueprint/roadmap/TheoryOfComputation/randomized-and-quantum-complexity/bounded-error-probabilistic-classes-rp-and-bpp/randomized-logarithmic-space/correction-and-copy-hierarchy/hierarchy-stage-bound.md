# Stage bound for the correction-and-copy hierarchy

In the correction-and-copy hierarchy with $q=2^{c+1}$ and retention channels at rate $q^{-l}$ at every stage $l$ (satisfying the retention-channel moment conditions), every stage matrix $C_l$ is strictly upper triangular, nonnegative and substochastic with all entries at most $q^{-l}$, the number of active vertices at most doubles from one stage to the next, and if $(1-S)p=e_t$ with $0\le p\le1$, then the transported reward $W_l$ at the all-primary copy $\bar x_l$ of every base vertex $x$ satisfies

$$
0\le p_x-W_l(\bar x_l)\le |V|\cdot 2^{-c\,l}.
$$

## Proof sketch

Each stage's correction removes only mass that the detectors certify as excess, which preserves the upper-triangular substochastic invariant and shrinks the maximal entry by a factor $q$; the reward lost at one stage is bounded by the mass removed, which is at most $|V|2^{-c}$ of the previous loss, and the losses telescope.

## Depends on

- [The correction-and-copy hierarchy](correction-and-copy-hierarchy.md)

## Proof depends on

- [Affine hash families give retention channels](affine-retention-channels.md)

## Sources

- OpenAI, "Exact Derandomization of Logarithmic Space: L = RL = BPL", Preprint, 2026, Proposition 4.7.
