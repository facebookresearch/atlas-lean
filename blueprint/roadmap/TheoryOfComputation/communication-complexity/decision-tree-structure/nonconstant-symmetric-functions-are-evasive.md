# Nonconstant symmetric functions are evasive

Every nonconstant symmetric function $f : \{0,1\}^n \to \{0,1\}$ (one depending only on the Hamming weight) has decision tree complexity $n$. In particular threshold functions $\mathrm{Th}^n_j$ with $1 \le j \le n$, majority and parity are evasive, although the sensitivity of majority is only about $n/2$.

## Proof sketch

Write $f(x)=F(|x|)$ and choose $k$ with $F(k)\ne F(k+1)$, $0\le k<n$. The adversary answers $1$ to the first $k$ distinct variables queried and $0$ to the next $n-k-1$. Before the last variable is read, the inputs consistent with the answers have weight $k$ or $k+1$, so the value is still undetermined and every tree must read all $n$ variables on this input.

## Depends on

- [Decision-tree depth and degree of a Boolean function](../query-and-communication-measures/decision-tree-depth-and-degree-of-a-boolean.md)

## Sources

- S. Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
