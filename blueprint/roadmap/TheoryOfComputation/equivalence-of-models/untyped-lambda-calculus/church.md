# Church numerals

Untyped lambda terms with de Bruijn indices are written $\underline{k}$ (the variable with index $k \in \mathbb{N}$), $t\,u$ (application) and $\lambda.\,t$ (abstraction).

The Church numeral of $n \in \mathbb{N}$ is

$$\overline{n} = \lambda.\, \lambda.\, \underbrace{\underline{1}\,(\underline{1}\,(\cdots(\underline{1}}_{n}\;\underline{0})\cdots)),$$

that is, $\lambda f.\, \lambda x.\, f^n(x)$ in named notation; in particular $\overline{0} = \lambda.\,\lambda.\,\underline{0}$.

## Sources

- H. P. Barendregt, *The Lambda Calculus: Its Syntax and Semantics*, North-Holland, 1984, Def. 6.4.4 (the Church numerals).
