# Circuit lower-bound tautologies and proof-size lower-bound formulas

The tautology $\mathrm{tt}(f, s)$ expresses that a Boolean function $f$, given by its truth table, has no circuit of size $s$; the formula $\mathrm{lb}_R(\varphi, s)$ expresses that a formula $\varphi$ has no $R$-proof of size $s$. Together they let proof systems state circuit and proof complexity lower bounds.

Let $f \colon \{0,1\}^n \to \{0,1\}$ and $s \ge 1$. Then $\mathrm{tt}(f, s)$ is a propositional DNF formula of size $\tilde{O}(2^n s^3)$ over $\tilde{O}(s)$ variables, namely

$$
\mathrm{tt}(f, s) = \bigvee_{y \in \{0,1\}^n} \big(f(y) \ne C(y)\big),
$$

where $C$ is a circuit of size $s$ encoded by $\mathrm{poly}(s)$ variables and each predicate $f(y) \ne C(y)$ is written as a DNF of size $\tilde{O}(s^3)$; it is a tautology if and only if $f$ has no circuit of size $s$.

A propositional proof system with $a$ bits of advice is a polynomial-time relation $R(x, y, z)$ such that for each $n$ there is $w_n \in \{0,1\}^{a(n)}$ with: for every $x \in \{0,1\}^n$, $x$ encodes a DNF tautology if and only if $R(x, y, w_n)$ holds for some $y$. For such $R$, a formula $\varphi$, a size $s$ and an advice string $w$, $\mathrm{lb}_R(\varphi, s, w)$ is a DNF of size $\mathrm{poly}(|\varphi| + s)$ expressing that no string of length $s$ is an $R$-proof of $\varphi$ with advice $w$ (without advice, $\mathrm{lb}_R(\varphi, s)$). A system is polynomially bounded if every tautology has proofs of polynomial size; $\mathsf{NP} = \mathsf{coNP}$ if and only if a polynomially bounded system exists, and $\mathsf{NP} \subseteq \mathsf{coNP}/\mathrm{poly}$ if and only if one exists with polynomial advice.

## Context

Because most functions are hard, $\mathrm{tt}(f_n, n^k)$ is a tautology for a random truth table with high probability, which makes these formulas a natural candidate source of hard tautologies; non-uniform proof systems, modelled by advice, correspond to proofs verifiable by polynomial-size circuits.

## Depends on

- [Cook–Reckhow propositional proof systems](../../../../Logic/propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)
- [Circuit complexity of a Boolean function and truth tables](../../../circuit-complexity/minimum-circuit-size-problem/circuit-complexity-of-a-boolean-function.md)
- [The Cook–Reckhow theorem](../../../../Logic/propositional-logic/propositional-proof-complexity/cookreckhow-theorem.md)

## Proof depends on

None.

## Sources

- Ján Pich and Rahul Santhanam, "Why are Proof Complexity Lower Bounds Hard?", *FOCS* 2019, DOI 10.1109/FOCS.2019.00080 (Definitions 1 to 5 and Propositions 1 and 2, Sections 2.1 and 2.2, in the authors' full version of 5 April 2019, <https://ora.ox.ac.uk/objects/uuid:b038d171-928d-4dfe-abf5-a6fdb03217b2>).
