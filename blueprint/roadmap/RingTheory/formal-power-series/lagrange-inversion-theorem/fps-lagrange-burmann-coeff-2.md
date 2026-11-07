# Lagrange–Bürmann formula, coefficient form

Let $R$ be a commutative ring and let $A$,
$\varphi$ and $g$ be formal power series over $R$ such that the constant term of $A$ is
nilpotent, $\varphi$ has nonzero constant term, and $A = X\,\varphi(A)$, where $\varphi(A)$ and
$g(A)$ denote the substitution of $A$ into $\varphi$ and $g$. Write $[X^m]H$ for the coefficient
of $X^m$ in a power series $H$ and $g'$ for the formal derivative of $g$. Then for every
natural number $n \ge 1$,

$$n\, [X^n]\, g(A) = [X^{n-1}]\left(g' \varphi^n\right).$$

This is the division-free form over a commutative ring: no division by $n$ is required.

## Sources

- Alexander M. Haupt, "Enumeration of S-omino Towers and Row-Convex k-omino Towers," JIS 24 (2021), proposition at lines 400–407, https://cs.uwaterloo.ca/journals/JIS/VOL24/Haupt/haupt4.tex, file SHA-256 `1b412146e9dba7d9302d274268baf3e35239b8369473faf57f086f918e3b66af`, span SHA-256 `ba6bf0dfa1cffa8a22bf10e4f7528c86dbe5ced596286dee93a765f5db3774cf`. Corroborating power specialization: Dmitry Kruchinin and Vladimir Kruchinin, "A Method for Obtaining Generating Functions for Central Coefficients of Triangles," JIS 15 (2012), lines 199–210, https://cs.uwaterloo.ca/journals/JIS/VOL15/Kruchinin/kruchinin5.tex, file SHA-256 `abb875f7d7951467436cf43c9c7d0dd662fdfd05382952f542ad53b2ebfcea8f`, span SHA-256 `805d5ab3e7352b021e119fb2bec5cfd477f4a01469758b601fb7a9ea4c5f0d36`. Source concept `jis_grounded_b2a0ba5cfa34a62aa3e66f0f`; variants `formal_implicit_composition` and `formal_power_specialization`.
