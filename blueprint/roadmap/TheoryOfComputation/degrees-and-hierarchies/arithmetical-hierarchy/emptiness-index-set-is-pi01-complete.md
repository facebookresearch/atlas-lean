# The emptiness index set is Π⁰₁-complete

The set of indices of programs that halt on no input is $\Pi^0_1$-complete under many-one reductions: it is co-recursively enumerable, and every $\Pi^0_1$ set reduces to it by a computable function.

Fix an acceptable numbering $(\varphi_e)_{e\in\mathbb N}$ of the partial computable functions and write $W_e=\mathrm{dom}(\varphi_e)$. A set $B\subseteq\mathbb N$ *many-one reduces* to $A$, written $B\le_m A$, if some total computable $f$ satisfies $x\in B\iff f(x)\in A$ for all $x$. For a class $\Gamma$ of the [arithmetical hierarchy](is-pi.md), $A$ is *$\Gamma$-m-complete* if $A\in\Gamma$ and $B\le_m A$ for every $B\in\Gamma$.

**Theorem.** The [emptiness index set](../../computability/emptiness-and-equivalence-problems-for-programs/empty-code.md)

$$
\mathrm{EMP}=\{e\in\mathbb N : W_e=\emptyset\}
$$

is $\Pi^0_1$-m-complete (Proposition 40.1 of the notes).

So the emptiness problem is exactly as hard as the complement of the halting problem: it is co-recursively enumerable, and the complement of every recursively enumerable set reduces to it.

## Depends on

- [The arithmetical class $\Pi_n$](is-pi.md)
- [Codes with empty domain](../../computability/emptiness-and-equivalence-problems-for-programs/empty-code.md)
- [Co-recognizability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-co-recognizable.md)

## Proof depends on

- [Parametrized s-m-n theorem](../../computability/exists-computable-code.md)

## Remarks

Membership: $e\in\mathrm{EMP}$ iff for all $x$ and all $s$, the computation of $\varphi_e(x)$ has not halted within $s$ steps, a universal quantifier over a computable relation. Hardness: if $A$ is $\Pi^0_1$, there is a computable $R$ with $A(x)\iff\forall y\,R(x,y)$; by the s-m-n theorem there is a total computable $f$ with $W_{f(x)}=\{y:\neg R(x,y)\}$, and then $x\in A\iff f(x)\in\mathrm{EMP}$.

## Sources

- Arnold W. Miller, *Lecture Notes in Computability Theory*, lecture notes for Math 773, University of Wisconsin–Madison, version of December 3, 2008; read in the [open-access copy](https://people.math.wisc.edu/~awmille1/old/m773-07/cmpthy.pdf): Section 40 ("EMP, TOT, FIN, and REC"), Proposition 40.1 and its proof.
- Hartley Rogers Jr., *Theory of Recursive Functions and Effective Computability*, McGraw-Hill, 1967 (reprinted by MIT Press, 1987), the standard reference for index sets in the arithmetical hierarchy; not read, cited beside the notes above.
