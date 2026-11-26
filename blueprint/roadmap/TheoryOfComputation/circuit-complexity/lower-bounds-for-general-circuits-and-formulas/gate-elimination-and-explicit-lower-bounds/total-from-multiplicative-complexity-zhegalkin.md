# Total complexity from multiplicative complexity over the Zhegalkin basis

For every $\varepsilon>0$ there is $M_0$ such that every Boolean function $f$ of $n$ variables with multiplicative complexity $M\ge M_0$ over $\{\oplus,\wedge,1\}$ has a circuit over $\{\oplus,\wedge,1\}$ with at most $M$ conjunction gates and at most

$$
\Bigl(\tfrac12+\varepsilon\Bigr)\frac{M(M+2n)}{\log_2 M}
$$

gates in total.

## Proof sketch

In a circuit with $M$ conjunctions, every conjunction input is an affine form in the inputs and earlier conjunction outputs; the linear part is a Boolean matrix with $M$ rows and $M+n$ columns, synthesized in stages by the active-square additive matrix bound, which saves the logarithmic factor.

## Depends on

- [The Zhegalkin basis and multiplicative complexity](../../circuit-models-and-classes/circuit-models-and-complexity-measures/zhegalkin-basis-and-multiplicative-complexity.md)

## Proof depends on

- [Sergeev's active-square bound for additive matrix synthesis](../rectifier-and-additive-circuits/sergeev-active-square-additive-bound.md)

## Sources

- Igor S. Sergeev, "A relation between additive and multiplicative complexity of Boolean functions", 2013.
