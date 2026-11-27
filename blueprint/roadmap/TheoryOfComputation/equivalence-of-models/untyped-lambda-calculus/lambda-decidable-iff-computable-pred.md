# Lambda calculus computes exactly the computable predicates

The following holds. For every predicate $P$ on $\mathbb{N}$, these are equivalent:

1. $P$ is lambda-decidable: some untyped lambda term $t$ satisfies $t\,\overline{n} \twoheadrightarrow_\beta \lambda.\,\lambda.\,\underline{1}$ (Church true) whenever $P(n)$ holds and $t\,\overline{n} \twoheadrightarrow_\beta \lambda.\,\lambda.\,\underline{0}$ (Church false) whenever it fails, where $\overline{n}$ is the Church numeral of $n$ and $\twoheadrightarrow_\beta$ is multi-step beta reduction;
2. $P$ is a computable predicate.

## Sources

- A. Church, "The calculi of lambda-conversion", *Annals of Mathematics Studies* 6 (1941).
- S. C. Kleene, "Lambda-definability and recursiveness", *Duke Mathematical Journal* 2 (1936), 340–353.
- R. I. Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Theorem 2.3.
