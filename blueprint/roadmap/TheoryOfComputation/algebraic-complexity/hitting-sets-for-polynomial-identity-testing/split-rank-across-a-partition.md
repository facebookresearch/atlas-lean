# Split rank of a polynomial across a variable partition

For a set $Y$ of variables, a polynomial $f$ has *split rank at most $w$ across $Y$* if $f=\sum_{j=1}^{w}g_j\,h_j$ with each $g_j$ depending only on the variables in $Y$ and each $h_j$ only on the variables outside $Y$ (equivalently, its coefficient matrix with rows indexed by monomials in $Y$ and columns by monomials outside $Y$ has rank at most $w$). Polynomials computed by width-$w$ ROABPs in an order in which $Y$ is a prefix have split rank at most $w$ across $Y$.

## Depends on

- [Read-once oblivious algebraic branching programs](../algebraic-circuit-lower-bound-methods/read-once-oblivious-abps.md)

## Sources

- Michael A. Forbes, Ramprasad Saptharishi, Amir Shpilka, "Hitting Sets for Multilinear Read-Once Algebraic Branching Programs, in any Order", Proceedings of the 46th Annual ACM Symposium on Theory of Computing, 2014.
