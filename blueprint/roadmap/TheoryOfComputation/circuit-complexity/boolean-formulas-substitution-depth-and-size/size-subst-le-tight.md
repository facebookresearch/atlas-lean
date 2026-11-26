# Size of a substituted formula, tight form

For a [Boolean formula](boolean-formula.md) $g$ over $n$ inputs (binary AND and OR, unary NOT) and formulas $w_0, \dots, w_{n-1}$ with at most $D$ gates each, the [substituted formula](subst.md) has at most $\mathrm{size}(g)(D + 1) + D = \mathrm{size}(g) + (\mathrm{size}(g) + 1) D$ gates. The gates of $g$ remain; since every gate has at most two children, $g$ has at most $\mathrm{size}(g) + 1$ leaves, and only its input leaves are replaced, each by at most $D$ gates, while constant leaves stay unchanged.
