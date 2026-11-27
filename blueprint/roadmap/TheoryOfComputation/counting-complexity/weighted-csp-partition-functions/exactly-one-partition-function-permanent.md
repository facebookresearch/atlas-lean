# Exactly-one partition functions count perfect matchings and permanents

With the exactly-one weighting (a local assignment has weight $1$ if exactly one of its values is true and $0$ otherwise), the partition function of a Boolean CSP instance whose scopes have pairwise distinct variables counts the sets $S$ of occurring variables that meet every scope in exactly one variable. (With a repeated variable this fails: on the scope $(x,x)$ the set $S=\{x\}$ meets it in one variable, but the local assignment $(1,1)$ has weight $0$; in general the partition function counts the sets $S$ such that exactly one position of every scope holds a variable of $S$.) For a $0/1$ matrix $A$ of order $n$, the instance with a variable for each nonzero entry and an exactly-one constraint for every row and every column on its nonzero entries has partition function equal to the permanent $\mathrm{per}(A)$; for a graph with one variable per edge and one constraint per vertex on its incident edges it counts perfect matchings.

## Proof sketch

Exactly-one sets meeting every row and every column once are the permutations supported on the nonzero entries.

## Depends on

- [Partition function of a weighted CSP](partition-function-of-a-weighted-csp.md)
- [The 0-1 permanent counts perfect matchings](../complexity-of-the-permanent/permanent-boole-eq-card.md)

## Sources

- L. G. Valiant, "The Complexity of Computing the Permanent", Theoretical Computer Science 8(2), 189–201, 1979.
