# Unique-SAT is easy iff polynomial-time C and CD complexity coincide

Printing a string costs no more than recognizing it, up to an additive constant and a polynomial change of time bound, exactly when satisfying assignments of uniquely satisfiable formulas can be found in polynomial time. The equivalence is due to Fortnow and Kummer.

*Unique-SAT is easy* means that there is a polynomial-time algorithm $\mathcal{A}$ such that for every Boolean formula $\varphi$ with exactly one satisfying assignment, $\mathcal{A}(\varphi)$ outputs that assignment. The following are equivalent:

1. Unique-SAT is easy.
2. For every polynomial $p$ there are a polynomial $q$ and a constant $c$ such that for all strings $x$ and $y$, $C^q(x\mid y)\le \mathrm{CD}^p(x\mid y)+c$.

In particular, if Unique-SAT is easy then for every polynomial $p$ there are $q$ and $c$ with $C^q(x)\le\mathrm{CD}^p(x)+c$ for all $x$. The reverse inequality $\mathrm{CD}^{t}(x)\le C^t(x)+O(1)$ holds unconditionally. Unique-SAT being easy implies $\mathrm{NP}=\mathrm{RP}$ and $\mathrm{P}=\mathrm{UP}$, and there are oracles relative to which Unique-SAT is easy while $\mathrm{P}\ne\mathrm{NP}$.

## Expansion

From 1 to 2: a distinguishing program for $x$ given $y$ accepts exactly one string, so "the program accepts $z$ within the time bound" becomes, after the Cook–Levin translation, a formula with a unique satisfying assignment encoding $z=x$; the Unique-SAT algorithm then prints $x$, and the wrapper adds only a constant to the program length. From 2 to 1: with $y=\varphi$ uniquely satisfiable, its satisfying assignment $x$ has $\mathrm{CD}^p(x\mid\varphi)=O(1)$ (check that the input satisfies $y$), so $C^q(x\mid\varphi)=O(1)$, and trying the constantly many short programs for $q$ steps finds $x$.

## Depends on

- [Distinguishing complexity CD^t](distinguishing-complexity-cdt.md)
- [Time-bounded Kolmogorov complexity K^t and Levin's Kt](../../time-bounded-kolmogorov-complexity/time-bounded-kolmogorov-complexity-and-levin-kt.md)

## Proof depends on

- [Cook–Levin theorem: SAT is NP-complete](../../../np-completeness/cook-levin/cook-levin-sat-np-complete.md)

## Sources

- Lance Fortnow, "Kolmogorov Complexity and Computational Complexity", in *Complexity of Computations and Proofs* (J. Krajíček, ed.), Quaderni di Matematica 13, 2004, [author copy](https://lance.fortnow.com/papers/files/quaderni.pdf) (Definition 3.2, Theorems 3.1, 3.3 and 3.4).
