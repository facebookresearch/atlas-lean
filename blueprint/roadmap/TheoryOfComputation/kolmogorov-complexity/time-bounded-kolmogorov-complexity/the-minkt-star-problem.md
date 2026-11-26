# Partial-string time-bounded Kolmogorov problem MINKT*

A *partial string* is $x \in \{0, 1, *\}^n$; a total string $y \in \{0,1\}^n$ is *consistent* with $x$ if $y_i = x_i$ whenever $x_i \ne *$. *MINKT\** is the language of triples $(x, 1^t, 1^s)$ with $x$ a partial string such that some program $p$ with $|p| \le s$ makes the universal machine output, within $t$ steps, a total string consistent with $x$. For total $x$ it coincides with MINKT; it is the Kolmogorov analogue of Partial MCSP.

## Depends on

- [The time-bounded Kolmogorov complexity problem MINKT](the-minkt-problem.md)

## Sources

- S. Hirahara, "NP-Hardness of Learning Programs and Partial MCSP", FOCS 2022.
