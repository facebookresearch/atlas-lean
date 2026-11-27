# The cofiniteness index set is Σ⁰₃-complete

The set of indices of programs whose domain is cofinite, that is, which fail to halt on only finitely many inputs, is $\Sigma^0_3$-complete under many-one reductions.

Fix an acceptable numbering $(\varphi_e)_{e\in\mathbb N}$ of the partial computable functions, write $W_e=\mathrm{dom}(\varphi_e)$, and use many-one reductions $\le_m$ and $\Gamma$-m-completeness as on the page on the [emptiness index set](emptiness-index-set-is-pi01-complete.md).

**Theorem.** The set

$$
\mathrm{COF}=\{e\in\mathbb N : \mathbb N\setminus W_e\text{ is finite}\}
$$

is $\Sigma^0_3$-m-complete.

## Depends on

- [The arithmetical class $\Sigma_n$](is-sigma.md)

## Proof depends on

- [Parametrized s-m-n theorem](../../computability/exists-computable-code.md)

## Expansion

Membership: $e\in\mathrm{COF}$ iff $\exists n\,\forall m>n\,\exists s$ ($m$ is enumerated into $W_e$ within $s$ steps). Hardness: a $\Sigma^0_3$ set has the form $A(x)\iff\exists n\,\exists^\infty m\,P(n,m,x)$ with $P$ computable. For each $x$ a c.e. set $B_x$ is built with movable markers $p_{0,s}<p_{1,s}<\cdots$ listing its complement at stage $s$: at stage $s$, for the least $n<s$ with $P(n,s,x)$, marker $n$ is bumped, that is, $p_{n,s}$ is enumerated into $B_x$. If $A(x)$ holds, some marker is bumped infinitely often, so all later markers move off to infinity and $B_x$ is cofinite; otherwise every marker settles and $B_x$ is coinfinite. The s-m-n theorem gives a total computable $f$ with $W_{f(x)}=B_x$, so $A(x)\iff f(x)\in\mathrm{COF}$.

## Sources

- Arnold W. Miller, *Lecture Notes in Computability Theory*, lecture notes for Math 773, University of Wisconsin–Madison, version of December 3, 2008; read in the [open-access copy](https://people.math.wisc.edu/~awmille1/old/m773-07/cmpthy.pdf): Section 40 ("EMP, TOT, FIN, and REC"), Proposition 40.3 and its proof (the set displayed there as having $W_e$ finite is the cofinite one, as its proof shows).
- Hartley Rogers Jr., *Theory of Recursive Functions and Effective Computability*, McGraw-Hill, 1967 (reprinted by MIT Press, 1987), the standard reference for index sets in the arithmetical hierarchy; not read, cited beside the notes above.
