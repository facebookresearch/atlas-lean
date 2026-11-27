# The index set of computable c.e. sets is Σ⁰₃-complete

Deciding whether the recursively enumerable set enumerated by a given program is in fact computable is $\Sigma^0_3$-complete under many-one reductions, two quantifier levels above the halting problem.

Fix an acceptable numbering $(\varphi_e)_{e\in\mathbb N}$ of the partial computable functions, write $W_e=\mathrm{dom}(\varphi_e)$, and use many-one reductions $\le_m$ and $\Gamma$-m-completeness as on the page on the [emptiness index set](emptiness-index-set-is-pi01-complete.md).

**Theorem.** The set

$$
\mathrm{REC}=\{e\in\mathbb N : W_e\text{ is computable}\}
$$

is $\Sigma^0_3$-m-complete.

## Depends on

- [The arithmetical class $\Sigma_n$](is-sigma.md)

## Proof depends on

- [Parametrized s-m-n theorem](../../computability/exists-computable-code.md)
- [The cofiniteness index set is Σ⁰₃-complete](cofiniteness-index-set-is-sigma03-complete.md)
- [The halting set](../turing-reducibility/halting-set.md)

## Expansion

Membership: $W_e$ is computable iff its complement is c.e., that is, iff $\exists e'\,(W_e\cup W_{e'}=\mathbb N\wedge W_e\cap W_{e'}=\emptyset)$; the union condition is $\Pi^0_2$ and the disjointness condition $\Pi^0_1$. Hardness reuses the moving-marker construction of the cofiniteness proof with one more reason to bump the $e$-th marker: whenever $\varphi_e(e)$ converges, the marker is bumped so that its final position $p_e$ bounds the halting time. If $B_x$ ends up coinfinite, then $\varphi_e(e)$ converges iff it converges within $p_e$ steps, so the halting set is computable from $B_x$ and $B_x$ is not computable; if $B_x$ is cofinite it is computable. Hence $A(x)\iff f(x)\in\mathrm{REC}$ for the same kind of computable $f$.

## Sources

- Arnold W. Miller, *Lecture Notes in Computability Theory*, lecture notes for Math 773, University of Wisconsin–Madison, version of December 3, 2008; read in the [open-access copy](https://people.math.wisc.edu/~awmille1/old/m773-07/cmpthy.pdf): Section 40 ("EMP, TOT, FIN, and REC"), Proposition 40.4 and its proof, which modifies the proof of Proposition 40.3.
- Hartley Rogers Jr., *Theory of Recursive Functions and Effective Computability*, McGraw-Hill, 1967 (reprinted by MIT Press, 1987), the standard reference for index sets in the arithmetical hierarchy; not read, cited beside the notes above.
