# Lambda-decidable predicates

A predicate $P$ on $\mathbb{N}$ is lambda-decidable when there is an untyped lambda term $t$ (with de Bruijn indices) such that for every $n \in \mathbb{N}$,

$$t\, \overline{n} \twoheadrightarrow_\beta \begin{cases} \lambda.\,\lambda.\,\underline{1} & \text{if } P(n), \\ \lambda.\,\lambda.\,\underline{0} & \text{if not } P(n), \end{cases}$$

where $\overline{n} = \lambda.\,\lambda.\,\underline{1}(\cdots(\underline{1}\,\underline{0})\cdots)$ (with $n$ occurrences of $\underline{1}$) is the Church numeral of $n$, $\lambda.\,\lambda.\,\underline{1}$ and $\lambda.\,\lambda.\,\underline{0}$ are the Church booleans true and false, and $\twoheadrightarrow_\beta$ is the reflexive-transitive closure of one-step beta reduction (with congruence under application and abstraction).

## Sources

- H. P. Barendregt, *The Lambda Calculus: Its Syntax and Semantics*, North-Holland, 1984, Defs. 6.2.2 and 6.4.4 (truth values and Church numerals) and §3.1 (compatible beta reduction).
- R. I. Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Theorem 2.3.
