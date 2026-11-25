# Håstad's switching lemma

Let $F$ be a $k$-DNF or a $k$-CNF formula on $n$ variables and $p \in (0, 1/5)$ with $pn$ an integer. Let $\rho$ be a random restriction that chooses uniformly a set of $pn$ variables to leave free and sets each other variable to $0$ or $1$ independently and uniformly. Then for every $t \ge 1$, with probability greater than $1 - (10pk)^t$, the restricted function $F|_\rho$ is equivalent both to a $t$-DNF formula and to a $t$-CNF formula.

## Depends on

- [Evaluation of a flat Boolean circuit](../../complexity-classes/time-and-space-complexity-classes/circuit-eval.md)

## Sources

- J. Håstad, "Almost optimal lower bounds for small depth circuits", *Proceedings of the 18th ACM STOC*, 1986
- R. Williams, *CS294 lecture notes: the AC0 switching lemma*, 2018, <https://people.csail.mit.edu/rrw/cs294-2018/ac0-switching-lemma.txt>
