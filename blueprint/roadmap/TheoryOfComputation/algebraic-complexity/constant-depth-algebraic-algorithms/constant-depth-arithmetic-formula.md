# Arithmetic AC0: constant-depth arithmetic circuits with division and piecewise computation

Over a field $\mathbb{F}$, an **arithmetic circuit** is a directed acyclic graph whose input gates are labeled by variables $x_i$ or field constants and whose internal gates are labeled by $+$, $\times$ or $\div$; each gate computes a rational function in $\mathbb{F}(x)$, and no gate divides by the identically zero function. Its size is the number of wires and its depth the length of a longest input-output path. A family $\{f_n\}$ of rational functions (or tuples of them) is in **arithmetic $\mathrm{AC}^0$**, written $\mathrm{AC}^0_{\mathbb{F}}$, if $f_n$ is computed by circuits of unbounded fan-in, size $\operatorname{poly}(n)$ and depth $O(1)$.

Functions such as the GCD are not rational: $\gcd(x - \alpha, x - \beta)$ is $x - \alpha$ if $\alpha = \beta$ and $1$ otherwise. A **piecewise arithmetic circuit** also has gates $\mathrm{select}(y_1, \dots, y_m)$, which output the first nonzero $y_i$ (or $0$ if all vanish); its gates compute functions $\mathbb{F}^n \to \mathbb{F}$, and no division by zero may occur on any input. For example $\gcd(x - \alpha, x - \beta) = \mathrm{select}(\alpha - \beta, x - \alpha)$. A family is **computable piecewise in $\mathrm{AC}^0_{\mathbb{F}}$** if it is computed by piecewise circuits of unbounded fan-in, size $\operatorname{poly}(n)$ and depth $O(1)$. Univariate inputs and outputs are given by their coefficient vectors.

Neither extension adds power for polynomials of polynomial degree. A piecewise circuit computing a rational function $f$ can be replaced by an ordinary circuit of the same size, depth and fan-in, and over an infinite field a polynomial of degree $n^{O(1)}$ in $\mathrm{AC}^0_{\mathbb{F}}$ has a division-free $\mathrm{AC}^0_{\mathbb{F}}$ circuit (Strassen's division elimination in constant depth). Division-free circuits of constant depth and polynomial size can be unfolded into formulas of polynomial size, so for such polynomials $\mathrm{AC}^0_{\mathbb{F}}$ is the class of families computed by polynomial-size, constant-depth formulas with unbounded fan-in addition and multiplication gates and field constants on the edges.

## Depends on

- [Arithmetic circuit](../arithmetic-circuits/arithmetic-circuit.md)

## Sources

- R. Andrews, A. Wigderson, "Constant-depth arithmetic circuits for linear algebra problems", FOCS (2024), arXiv:2404.10839 (Section 2.2: Definitions 2.1-2.4, Lemma 2.5; Theorem 2.13).
- N. Limaye, S. Srinivasan, S. Tavenas, "Superpolynomial lower bounds against low-depth algebraic circuits", FOCS (2021); Communications of the ACM 65 (2022), ECCC TR21-081.
