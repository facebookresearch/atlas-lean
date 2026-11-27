# Nechiporuk's lower bound for rectifier circuits of k-free matrices

If a Boolean matrix $A$ is $K$-free ($K\ge2$), then every rectifier circuit realizing $A$ has at least $|A|/(K-1)^2$ edges: $|A|\le(K-1)^2\,\mathrm{OR}(A)$. In particular, if $A$ is $2$-free then $\mathrm{OR}(A)=\mathrm{OR}_d(A)=|A|$ for every depth $d\ge1$.

## Proof sketch

Pippenger's argument: for an edge $e=(u,v)$ let $s_u$ be the number of inputs reaching $u$ and $t_v$ the number of outputs reachable from $v$; the inputs reaching $u$ and the outputs reachable from $v$ span an all-ones submatrix. Call $e$ eligible if $s_u\le K-1$ and $t_v\le K-1$. On an input-to-output path for a one-entry, the counts $s$ increase and $t$ decrease along the path; at the last node with $s\le K-1$ the next node has $s\ge K$, hence $t\le K-1$ by $K$-freeness, so the edge between them is eligible and covers the entry. Each eligible edge covers at most $(K-1)^2$ one-entries.

## Depends on

- [Rectifier (OR) circuits for Boolean matrices](rectifier-or-circuits.md)
- [k-free (rectangle-free) Boolean matrices](k-free-boolean-matrices.md)

## Sources

- E. I. Nechiporuk, "On the Topological Principles of Self-Correction", Problemy Kibernetiki 21, 5–102, 1969.
- Nicholas Pippenger, "On Another Boolean Matrix", Theoretical Computer Science 11(1), 49–56, 1980.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012 (Section 13.6, rectifier networks).
- Stasys Jukna, Igor Sergeev, "Complexity of Linear Boolean Operators", Foundations and Trends in Theoretical Computer Science 9(1), 1–123, 2013.
