# First-order and quantifier-free projections (Immerman-Landau)

A $k$-dimensional full-tuple interpretation ($k \ge 1$) is a first-order projection if each defining formula has the form

$$
\varphi_{R'}(\bar x) \equiv \bigvee_{i=1}^{s} \big(\alpha_i(\bar x) \wedge \lambda_i(\bar x)\big),
$$

where the guards $\alpha_i$ are mutually exclusive formulas mentioning only the numeric predicates ($\le$, $\mathrm{BIT}$, $0$, $1$, $\max$) and no input relation, and each $\lambda_i$ is an input literal (an atomic $L$-formula or its negation) or a constant truth value. So each output bit is an input bit, its negation or a constant, selected by numeric information alone, as in Valiant's projections. It is a quantifier-free projection if moreover the guards are quantifier-free formulas over $\le$, successor, $0$ and $\max$ only (no $\mathrm{BIT}$). Write $K \le_{\mathrm{fop}} K'$ ($K \le_{\mathrm{qfp}} K'$) if $K$ reduces to $K'$ by a first-order (quantifier-free) projection. Dimension $0$ is excluded.

## Depends on

- [First-order reductions between queries on ordered structures](first-order-reductions-on-ordered-structures.md)

## Sources

- Neil Immerman and Susan Landau, "The Complexity of Iterated Multiplication", Information and Computation 116(1), 1995.
- Neil Immerman, "Descriptive Complexity", Graduate Texts in Computer Science, Springer, 1999.
