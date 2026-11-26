# Read-once branching programs and the rectangle bound

A *layered read-once nondeterministic branching program* reads the coordinates of $x\in U^\iota$ in disjoint blocks $X_1,X_2,\dots,X_T$ (each coordinate once), with state sets $Q_0,\dots,Q_T$ of sizes $w_t$. If it accepts a $K$-rectangle-free set $S$ with $|S|\ge K$, then $|S|\le(K-1)^2\sum_t w_tw_{t+1}|U|^{|X_{t+1}|}$. In particular a program of width $w$ reading one coordinate per layer accepts at most $(K-1)^2\,T\,w^2|U|$ elements of a $K$-rectangle-free set.

## Proof sketch

States reached after layer $t$ are messages of a sweep (paths through the same state can be spliced), and transitions are triples (state, state, revealed block); apply the frontier counting lemma.

## Depends on

- [Rectangle-free sets and rectangle bias](rectangle-free-sets-and-rectangle-bias.md)

## Proof depends on

- [Sweeps and the frontier counting lemma](sweeps-and-the-frontier-counting-lemma.md)

## Sources

- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
- Serge Gaspers, "Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms", 2026.
