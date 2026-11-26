# Khot–Tulsiani–Worah characterization of strong approximation resistance

Assume the Unique Games Conjecture. A predicate $P \subseteq \{-1,1\}^k$ is **strongly approximation resistant** (no efficient algorithm can find an assignment whose value deviates from $\rho(P)$ by more than $\varepsilon$ in either direction on almost-satisfiable instances) if and only if there is a probability measure $\Lambda$ on the polytope $C(P)$ of first and second moment vectors $(\mathbb{E}x_i, \mathbb{E}x_ix_j)$ of distributions supported on $P$ that vanishes: for every $1 \le t \le k$ the signed measure $\Lambda^{(t)} = \mathbb{E}_{|S|=t}\,\mathbb{E}_{\pi}\,\mathbb{E}_{b \in \{-1,1\}^t}\bigl[\bigl(\prod_{i} b_i\bigr)\hat{P}(S)\,\Lambda_{S,\pi,b}\bigr]$ is identically zero. Otherwise $P$ is weakly approximable; the deviation may have either sign.

## Proof sketch

The “if” direction constructs a dictatorship test from a measure on moment vectors via the invariance principle as in Raghavendra's theorem. The “only if” direction designs an SDP-based rounding algorithm whose advantage is a polynomial in the moment vectors; if no vanishing measure exists, a minimax argument produces a rounding scheme whose value on every almost-satisfiable instance deviates from $\rho(P)$ by at least a positive constant, above or below it.

## Depends on

- [Approximation-resistant predicates and balanced pairwise independence](approximation-resistance.md)

## Proof depends on

- [Raghavendra's theorem: the basic SDP is UGC-optimal for every CSP](raghavendra-optimality.md)

## Sources

- S. Khot, M. Tulsiani, P. Worah, "A characterization of strong approximation resistance", STOC (2014), doi:10.1145/2591796.2591817; arXiv:1305.5500v1.
