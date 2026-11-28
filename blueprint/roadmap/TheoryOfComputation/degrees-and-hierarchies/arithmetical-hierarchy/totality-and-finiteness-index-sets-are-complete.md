# TOT is Π⁰₂-complete and FIN is Σ⁰₂-complete

The set of indices of programs that halt on every input is $\Pi^0_2$-complete, and the set of indices of programs that halt on only finitely many inputs is $\Sigma^0_2$-complete, both under many-one reductions.

Fix an acceptable numbering $(\varphi_e)_{e\in\mathbb N}$ of the partial computable functions, write $W_e=\mathrm{dom}(\varphi_e)$, and use many-one reductions $\le_m$ and $\Gamma$-m-completeness as on the page on the [emptiness index set](emptiness-index-set-is-pi01-complete.md).

**Theorem.**
1. The [totality index set](../../computability/totality-problem-for-programs/total-code.md) $\mathrm{TOT}=\{e : W_e=\mathbb N\}$ is $\Pi^0_2$-m-complete.
2. The [finiteness index set](../../computability/finiteness-problem-for-programs/finite-code.md) $\mathrm{FIN}=\{e : W_e\text{ is finite}\}$ is $\Sigma^0_2$-m-complete.

(Proposition 40.2 of the notes.)

Neither set is recognizable nor co-recognizable ([totality is not recognizable](../../computability/totality-problem-for-programs/not-tm2-recognizable-total.md), [totality is not co-recognizable](../../computability/totality-problem-for-programs/not-tm2-co-recognizable-total.md)); the theorem locates both exactly in the hierarchy.

## Depends on

- [The arithmetical class $\Pi_n$](is-pi.md)
- [The arithmetical class $\Sigma_n$](is-sigma.md)
- [Total codes](../../computability/totality-problem-for-programs/total-code.md)
- [Codes with finite domain](../../computability/finiteness-problem-for-programs/finite-code.md)

## Proof depends on

- [Parametrized s-m-n theorem](../../computability/exists-computable-code.md)

## Expansion

Membership: $e\in\mathrm{TOT}$ iff $\forall x\,\exists s$ ($x$ is enumerated into $W_e$ within $s$ steps), and $e\in\mathrm{FIN}$ iff $\exists x\,\forall y\,\forall s$ (if $y$ is enumerated within $s$ steps then $y<x$). Hardness for both at once: every $\Pi^0_2$ set $A$ can be written $A(x)\iff\exists^\infty s\,P(s,x)$ with $P$ computable; by the s-m-n theorem a total computable $f$ has $W_{f(x)}=\{t:\exists s>t\ P(s,x)\}$. If $A(x)$ then $W_{f(x)}=\mathbb N$, and otherwise $W_{f(x)}$ is finite, so the single function $f$ reduces $A$ to $\mathrm{TOT}$ and the complement of $A$ to $\mathrm{FIN}$.

## Sources

- Arnold W. Miller, *Lecture Notes in Computability Theory*, lecture notes for Math 773, University of Wisconsin–Madison, version of December 3, 2008; read in the [open-access copy](https://people.math.wisc.edu/~awmille1/old/m773-07/cmpthy.pdf): Section 40 ("EMP, TOT, FIN, and REC"), Proposition 40.2 and its proof.
- Hartley Rogers Jr., *Theory of Recursive Functions and Effective Computability*, McGraw-Hill, 1967 (reprinted by MIT Press, 1987), the standard reference for index sets in the arithmetical hierarchy; not read, cited beside the notes above.
