# Satisfiability coding lemma

Let $\varphi$ be a CNF formula over $N$ variables. For a fixed order $\pi$, the sets of words agreeing with distinct solutions off their forced variables are disjoint, hence $\sum_{x} 2^{|F_\pi(x)|} \le 2^{N}$ where the sum is over solutions and $F_\pi(x)$ is the set of variables forced on $x$. If $x$ is a solution at which $j$ variables are critical and $\varphi$ has clause width at most $k$, then a uniformly random order forces each critical variable with probability at least $1/k$, so $\mathbb{E}_\pi |F_\pi(x)| \ge j/k$.

## Proof sketch

A solution is determined by its unforced values listed in $\pi$-order, giving a prefix-free code; the agreement set of $x$ has $2^{|F_\pi(x)|}$ words, and disjointness inside $\{0,1\}^N$ gives the inequality. For a critical variable with witnessing clause of width at most $k$, the variable is forced whenever it comes last among that clause's variables, an event of probability at least $1/k$.

## Depends on

- [Forced variables with respect to an order](forced-variables.md)

## Sources

- R. Paturi, P. Pudlák and F. Zane, "Satisfiability Coding Lemma", Chicago Journal of Theoretical Computer Science 1999(11), 1999, Section 2 (Lemmas 1 and 2).
