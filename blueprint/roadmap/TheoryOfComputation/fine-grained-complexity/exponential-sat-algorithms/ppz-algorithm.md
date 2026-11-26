# Paturi–Pudlák–Zane: the satisfiability coding lemma and PPZ

PPZ processes the variables of a $k$-CNF $\varphi$ on $n$ variables in a uniformly random order, setting a variable to satisfy a unit clause on it if one exists ('forced'), and uniformly at random otherwise. If $\varphi$ is satisfiable, one round outputs a satisfying assignment with probability at least $2^{-(1-1/k)n}$. Hence $k$-SAT is solvable by a randomized algorithm in time $2^{(1-1/k)n}\mathrm{poly}(n)$.

## Proof sketch

Coding lemma: for an isolated satisfying assignment $a$, each variable has a critical clause (only it is true under $a$), and in a random order it is forced whenever it comes after the other $k-1$ variables of that clause, which happens with probability $\ge1/k$. So the expected number of guessed variables is $\le(1-1/k)n$, and the success probability is $\ge 2^{-\mathbb{E}[\text{guesses}]}$ by Jensen; non-isolated solutions are handled by averaging over the solution set.

## Depends on

- [The exponents s_k of k-SAT and #k-SAT](../sat-exponents-and-hypotheses/k-sat-exponents.md)

## Sources

- Ramamohan Paturi, Pavel Pudlák and Francis Zane, "Satisfiability Coding Lemma", 38th Annual Symposium on Foundations of Computer Science (FOCS), 1997.
- Ramamohan Paturi, Pavel Pudlák and Francis Zane, "Satisfiability Coding Lemma", Chicago Journal of Theoretical Computer Science 1999(11), 1999.
