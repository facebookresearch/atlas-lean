# Truly supercritical depth trade-offs for monotone circuits

There are $N$-variate monotone functions $f_N$ with either of the following properties:

1. $f_N$ has monotone circuits of size $s = \operatorname{poly}(N)$, but every monotone real circuit of size at most $s^{1.4}$ computing $f_N$ has depth at least $N^{2.4}$;
2. $f_N$ has monotone circuits of size $s = \operatorname{quasipoly}(N)$, but every monotone real circuit of size at most $s \cdot \exp\bigl((\log N)^{1.9}\bigr)$ computing $f_N$ has depth superpolynomial in $N$.

Every monotone function on $N$ variables has a monotone circuit of depth $O(N)$, so these depths exceed the worst case. The same work proves size-depth trade-offs for cutting planes and resolution refutations that are supercritical in the size of the refuted formula, not only in its number of variables.

## Proof sketch

Start from a supercritical width-depth trade-off for resolution, obtained by refining a compression scheme for the cops-and-robber game on suitable graphs, and transfer it to monotone circuits and cutting planes through improved dag-like lifting theorems that preserve depth: a shallow small circuit would yield a resolution refutation of the base formula that is both narrow and shallow, contradicting the base trade-off.

## Depends on

- [Resolution refutation](../../../Logic/propositional-logic/resolution-size-and-width/is-resolution-refutation.md)

## Proof depends on

- [Garg–Göös–Kamath–Sokolov: dag-like lifting from resolution width](../../communication-complexity/randomized-and-dag-like-lifting/ggks-dag-lifting.md)

## Sources

- S. F. de Rezende, N. Fleming, D. Janett, J. Nordström, S. Pang, "Truly supercritical trade-offs for resolution, cutting planes, monotone circuits, and Weisfeiler-Leman", STOC (2025), arXiv:2411.14267.
