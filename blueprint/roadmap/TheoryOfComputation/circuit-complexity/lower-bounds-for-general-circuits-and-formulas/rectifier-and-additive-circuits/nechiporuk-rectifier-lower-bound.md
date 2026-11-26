# Nechiporuk's lower bound for rectifier circuits of k-free matrices

If a Boolean matrix $A$ is $K$-free ($K\ge2$), then every rectifier circuit realizing $A$ has at least $|A|/(K-1)^2$ edges: $|A|\le(K-1)^2\,\mathrm{OR}(A)$. In particular, if $A$ is $2$-free then $\mathrm{OR}(A)=\mathrm{OR}_d(A)=|A|$ for every depth $d\ge1$.

## Proof sketch

Pippenger's threshold-edge argument: charge each one-entry $(i,j)$ to an edge on its path where the set of inputs reaching the edge and the set of outputs reachable from it both exceed or fall below the threshold $K-1$; the inputs and outputs of an edge span an all-ones rectangle, so each edge is charged at most $(K-1)^2$ times.

## Depends on

- [Rectifier (OR) circuits for Boolean matrices](rectifier-or-circuits.md)
- [k-free (rectangle-free) Boolean matrices](k-free-boolean-matrices.md)

## Sources

- E. I. Nechiporuk, "On the Topological Principles of Self-Correction", Problemy Kibernetiki, 1970.
- Stasys Jukna, Igor Sergeev, "Complexity of Linear Boolean Operators", Foundations and Trends in Theoretical Computer Science, 2013.
