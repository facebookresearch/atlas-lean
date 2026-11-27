# Query measures of threshold functions

For $1 \le j \le n$ and the threshold function $\mathrm{Th}^n_j(x) = [|x| \ge j]$: a coordinate is sensitive at $x$ iff $|x| = j$ and $x_i = 1$, or $|x| = j - 1$ and $x_i = 0$. Consequently

$$s(\mathrm{Th}^n_j) = bs(\mathrm{Th}^n_j) = C(\mathrm{Th}^n_j) = \max(j,\ n + 1 - j),$$

while $D(\mathrm{Th}^n_j) = n$. For majority on $n$ bits all three measures equal $\lfloor n/2 \rfloor + 1$, and parity has $s = bs = C = D = n$.

## Proof sketch

Count sensitive coordinates at weights $j$ and $j - 1$; certificates use $j$ true bits or $n + 1 - j$ false bits; $s \le bs \le C$ closes the chain. Evasiveness follows from symmetry.

## Depends on

- [Decision-tree depth and degree of a Boolean function](../query-and-communication-measures/decision-tree-depth-and-degree-of-a-boolean.md)

## Proof depends on

- [Certificate complexity, degree and decision-tree depth](../query-and-communication-measures/certificate-complexity-degree-and-decision-tree.md)
- [Nonconstant symmetric functions are evasive](../decision-tree-structure/nonconstant-symmetric-functions-are-evasive.md)

## Sources

- H. Buhrman and R. de Wolf, "Complexity Measures and Decision Tree Complexity: A Survey", Theoretical Computer Science 288(1), 2002.
