# A $k$-CNF has at most $2^{(1-1/k)n}$ isolated solutions

Let $\varphi$ be a CNF formula on $n$ variables with all clauses of width at most $k$. Then $\varphi$ has at most $2^{(1-1/k) n}$ isolated solutions (solutions all of whose $n$ neighbours are non-solutions).

## Proof sketch

Average the coding inequality $\sum_x 2^{|F_\pi(x)|} \le 2^n$ over a uniformly random order and apply Jensen: each isolated solution has $n$ critical variables, so $\mathbb{E}_\pi|F_\pi(x)| \ge n/k$ and the number of isolated solutions times $2^{n/k}$ is at most $2^n$. (Derived.) The same averaging shows more generally that if $s_j$ denotes the number of solutions with exactly $j$ critical variables, then $\sum_j s_j 2^{j/k} \le 2^{n}$.

## Depends on

- [Forced variables with respect to an order](forced-variables.md)

## Proof depends on

- [Satisfiability coding lemma](satisfiability-coding-lemma.md)

## Sources

- R. Paturi, P. Pudlák and F. Zane, "Satisfiability Coding Lemma", Chicago Journal of Theoretical Computer Science 1999(11), 1999, Lemma 4 (with Lemma 2 and Fact 3 in its proof).
