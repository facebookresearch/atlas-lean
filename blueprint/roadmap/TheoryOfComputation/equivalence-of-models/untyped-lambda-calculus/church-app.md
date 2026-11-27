# Body of a Church numeral

Untyped lambda terms with de Bruijn indices are written $\underline{k}$ (the variable with index $k \in \mathbb{N}$), $t\,u$ (application) and $\lambda.\,t$ (abstraction).

For $n \in \mathbb{N}$, the term $A_n$ is defined by

$$A_0 = \underline{0}, \qquad A_{n+1} = \underline{1}\; A_n,$$

so $A_n = \underline{1}\,(\underline{1}\,(\cdots(\underline{1}\;\underline{0})\cdots))$ with $n$ occurrences of $\underline{1}$. Inside two binders, $\underline{1}$ plays the role of $f$ and $\underline{0}$ the role of $x$, so $A_n$ is $f^n(x)$.

## Sources

- H. P. Barendregt, *The Lambda Calculus: Its Syntax and Semantics*, North-Holland, 1984, Def. 6.4.4 (the Church numerals and their bodies).
