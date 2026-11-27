# Church booleans

Untyped lambda terms with de Bruijn indices are written $\underline{k}$ (the variable with index $k \in \mathbb{N}$), $t\,u$ (application) and $\lambda.\,t$ (abstraction).

The Church booleans are

$$\mathrm{true} = \lambda.\, \lambda.\, \underline{1}, \qquad \mathrm{false} = \lambda.\, \lambda.\, \underline{0},$$

that is, $\lambda x.\, \lambda y.\, x$ and $\lambda x.\, \lambda y.\, y$ in named notation.

## Sources

- H. P. Barendregt, *The Lambda Calculus: Its Syntax and Semantics*, North-Holland, 1984, Def. 6.2.2 (the truth values).
