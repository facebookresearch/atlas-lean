# Blum's speedup theorem

For every Blum measure $\Phi$ and every total computable $r:\mathbb{N}^2\to\mathbb{N}$, there is a total computable $0/1$-valued function $f$ such that for every program $c$ computing $f$ there is another program $c'$ computing $f$ with

$$
r\bigl(n,\Phi_{c'}(n)\bigr)<\Phi_c(n)\quad\text{for almost all } n.
$$

Thus $f$ has no fastest program, even up to the speedup $r$.

## Proof sketch

Build $f$ by a priority construction with a uniform family of approximations $f_u$ that agree with $f$ beyond the first $u$ inputs and become cheaper as $u$ grows: at each stage cancel programs that are too fast relative to a bound defined via $r$-iterates; programs for $f$ must then be slow, while the approximations $f_u$, patched by finite tables, run faster by the factor $r$.

## Depends on

- [Blum complexity measure](../blum-measure.md)

## Proof depends on

- [Arbitrarily complex computable functions; complexity classes are proper](arbitrarily-complex-functions.md)
- [Blum: any two complexity measures are recursively related](recursive-relatedness.md)

## Sources

- Manuel Blum, "A Machine-Independent Theory of the Complexity of Recursive Functions", Journal of the ACM 14(2), 1967.
- Piergiorgio Odifreddi, "Classical Recursion Theory, Volume II", North-Holland, 1999.
