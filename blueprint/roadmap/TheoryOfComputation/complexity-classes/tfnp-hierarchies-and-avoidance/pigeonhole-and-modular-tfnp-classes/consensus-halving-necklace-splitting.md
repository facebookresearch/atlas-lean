# ε-CONSENSUS-HALVING, NECKLACE-SPLITTING and DISCRETE HAM SANDWICH as explicit total search problems

**$\varepsilon$-CONSENSUS-HALVING.** For each agent $i\in[n]$ a non-negative measure $\mu_i$ on an interval $A=[0,x]$ integrating to $1$ is given as an explicit step function (endpoints and values of its constant pieces, in binary), together with $\varepsilon\ge0$ in binary. A solution is a set of $n$ cut points dividing $A$ into at most $n+1$ subintervals, each labelled $A_+$ or $A_-$, such that $|\mu_i(A_+)-\mu_i(A_-)|\le\varepsilon$ for every $i$. Totality is the Hobby–Rice theorem (Simmons–Su).

**$k$-NECKLACE-SPLITTING.** An open necklace (a string) has $ka_i$ beads of colour $i$ for $1\le i\le n$; cut it in $(k-1)n$ places and distribute the pieces into $k$ collections with exactly $a_i$ beads of colour $i$ each (Alon). NECKLACE-SPLITTING is the case $k=2$.

**DISCRETE HAM SANDWICH.** Given $n$ finite sets of integer points in $\mathbb R^n$, find a hyperplane splitting each set into two equal halves (points on the hyperplane may be assigned to either side).

## Depends on

- [Search problems: FNP, FP and TFNP](../../total-search-problems/search-problems-fnp-fp-and-tfnp.md)

## Sources

- Aris Filos-Ratsikas and Paul W. Goldberg, "Consensus Halving is PPA-Complete", STOC (2018), arXiv:1711.04503.
- Aris Filos-Ratsikas and Paul W. Goldberg, "The Complexity of Splitting Necklaces and Bisecting Ham Sandwiches", STOC (2019), arXiv:1805.12559.
