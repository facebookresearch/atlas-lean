# Truly supercritical depth trade-offs for monotone circuits

There are explicit monotone functions $f_N$ on $N$ variables computable by monotone circuits of size $N^{O(1)}$ such that every monotone circuit computing $f_N$ with size below a superpolynomial threshold has depth superlinear in $N$, and in some parameter ranges superpolynomial in $N$, far exceeding the worst-case linear depth needed by any monotone function with unbounded size. Analogous truly supercritical size-depth trade-offs hold for cutting planes and resolution refutations, measured in terms of formula size.

## Proof sketch

Start from a supercritical width-depth trade-off for resolution, obtained by refining a compression scheme for the cops-and-robber game on suitable graphs, and transfer it to monotone circuits and cutting planes through improved dag-like lifting theorems that preserve depth: a shallow small circuit would yield a resolution refutation of the base formula that is both narrow and shallow, contradicting the base trade-off.

## Depends on

- [Garg–Göös–Kamath–Sokolov: dag-like lifting from resolution width](../../communication-complexity/randomized-and-dag-like-lifting/ggks-dag-lifting.md)

## Proof depends on

- [Garg–Göös–Kamath–Sokolov: dag-like lifting from resolution width](../../communication-complexity/randomized-and-dag-like-lifting/ggks-dag-lifting.md)

## Sources

- S. F. de Rezende, N. Fleming, D. Janett, J. Nordström, S. Pang, "Truly supercritical trade-offs for resolution, cutting planes, monotone circuits, and Weisfeiler-Leman", STOC (2025), arXiv:2411.14267.
