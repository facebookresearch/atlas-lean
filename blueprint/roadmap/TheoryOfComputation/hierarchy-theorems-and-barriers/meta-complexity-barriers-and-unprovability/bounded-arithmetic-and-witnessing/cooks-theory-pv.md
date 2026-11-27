# Cook's theory PV of polynomial-time reasoning

$\mathsf{PV}$ (written $\mathsf{PV}_1$ for its first-order form) is the bounded-arithmetic theory of polynomial-time reasoning: its language has a function symbol for every polynomial-time algorithm, defined through Cobham's recursion, and it is a universal theory whose induction is limited to polynomial-time predicates.

The language $\mathcal{L}_{\mathsf{PV}}$ contains a function symbol for each polynomial-time function $f \colon \mathbb{N}^k \to \mathbb{N}$; these symbols and their defining equations are introduced inductively following Cobham's characterization of the polynomial-time functions. Cook's original $\mathsf{PV}$ is an equational theory; its first-order conservative extension $\mathsf{PV}_1$ (the theory meant by $\mathsf{PV}$ in current usage) has as axioms universal sentences containing all equations provable in equational $\mathsf{PV}$, together with axioms replacing induction for open formulas (an induction scheme simulating binary search). It proves induction for quantifier-free formulas, that is, for polynomial-time predicates, and it admits an axiomatization in which every axiom has the form $\forall \vec{x}\, \phi(\vec{x})$ with $\phi$ quantifier-free, so $\mathsf{PV}$ is a universal theory. Its intended model is $\mathbb{N}$ with the standard interpretation.

Bounded formulas are classified as follows: $\Sigma^b_0 = \Pi^b_0$ are the formulas with only sharply bounded quantifiers $\exists x \le |t|$, $\forall x \le |t|$, and $\Sigma^b_{i+1}$, $\Pi^b_{i+1}$ close $\Pi^b_i$, $\Sigma^b_i$ under positive Boolean combinations, sharply bounded quantifiers and bounded quantifiers $\exists x \le t$, respectively $\forall x \le t$. For $i \ge 1$ a predicate is in $\Sigma^p_i$ exactly when it is defined over $\mathbb{N}$ by a $\Sigma^b_i$-formula.

## Context

Despite its weak axioms, $\mathsf{PV}$ formalizes the Cook–Levin theorem, resolution lower bounds and the PCP theorem, and $\mathsf{PV}$ is essentially equivalent to Buss's $\mathsf{T}^0_2$ under a suitable vocabulary. Because it is universal, the Herbrand and KPT witnessing theorems apply to it directly and turn proofs of $\forall\exists$ and $\forall\exists\forall$ sentences into polynomial-time algorithms or interactive student–teacher protocols.

## Depends on

- [Polynomial time on multi-tape machines](../../../complexity-classes/time-and-space-classes-on-multi-tape-machines/p.md)
- [The polynomial hierarchy](../../../complexity-classes/time-and-space-complexity-classes/ph.md)

## Proof depends on

None.

## Sources

- Igor C. Oliveira, "SIGACT News Complexity Theory Column 124: Meta-Mathematics of Computational Complexity Theory", *ACM SIGACT News* 56(1), 2025, DOI 10.1145/3726856.3726862, arXiv:2504.04416v1 (Section 2.2.1 on PV and Section 2.2.2 on the bounded-formula hierarchy).
- Ján Pich and Rahul Santhanam, "Strong Co-Nondeterministic Lower Bounds for NP Cannot be Proved Feasibly", *STOC* 2021, DOI 10.1145/3406325.3451117 (Section 2.1, Bounded arithmetic, in the authors' full version of March 2021, <https://users.ox.ac.uk/~coml0742/papers/stoc-final.pdf>).
