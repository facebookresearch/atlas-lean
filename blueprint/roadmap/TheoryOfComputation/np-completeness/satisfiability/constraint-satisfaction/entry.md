# Tuple entries with constants

An entry of a tuple is a pair of natural numbers. The legal entries are the variables $(0, x)$ and the constants $T = (1, 1)$ and $F = (1, 0)$; well-formed instances use only these, with $x$ below the number of variables. Under a truth assignment $t$, an entry $(0, x)$ has value $t(x)$, and every entry $(a, b)$ with $a \ne 0$ has value true exactly when $b = 1$. So $(2, 1)$ is raw entry data that evaluates to true but is not a legal constant.
