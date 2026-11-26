# Sweeps and the frontier counting lemma

A *sweep* of $S\subseteq U^\iota$ reveals coordinates in stages $\emptyset=X_0\subseteq X_1\subseteq\cdots\subseteq X_T=\iota$, and assigns to each $x\in S$ and time $t$ a *message* $\mu_t(x)$ such that splicing is allowed: if $x,y\in S$ and $\mu_t(x)=\mu_t(y)$ then the input agreeing with $x$ on $X_t$ and with $y$ elsewhere lies in $S$; the final message is constant on $S$. The *transition* of $x$ at step $t$ is $(\mu_t(x),\mu_{t+1}(x),x|_{X_{t+1}\setminus X_t})$. If $S$ is $K$-rectangle-free and $|S|\ge K$, then

$$
|S|\le (K-1)^2\sum_{t=0}^{T-1}\#\{\text{transitions taken at step } t\}.
$$

## Proof sketch

Charge each input to the first time $t+1$ at which the inputs sharing its message have at least $K$ distinct revealed parts. By splicing, inputs sharing a message form a rectangle-like set; rectangle-freeness bounds by $(K-1)^2$ the number of inputs charged to any single transition.

## Depends on

- [Rectangle-free sets and rectangle bias](rectangle-free-sets-and-rectangle-bias.md)

## Sources

- Serge Gaspers, "Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms", 2026.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
