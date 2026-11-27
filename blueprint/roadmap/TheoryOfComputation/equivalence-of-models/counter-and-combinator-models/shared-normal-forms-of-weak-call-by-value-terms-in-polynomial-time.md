# Weak call-by-value normal forms are computed in polynomial time as shared representations

There is a Turing machine that, given a closed term $s$ of the [weak call-by-value λ-calculus](weak-call-by-value-lambda-calculus-and-its-cost-measures.md) that has a normal form $t$, computes a heap $H$ and a closure $g$ that represents $t$ relative to $H$, in time polynomial in $\|s\|$ and $\|s\|_T$ and in space $O(\|s\|_S)$.

The output is a shared representation, not the term $t$ itself. Size explosion is the reason: the closed terms $s_E\,\bar n$ of the source normalize in $\Theta(n)$ β-steps but pass through an intermediate term of size $\Omega(2^n)$, so a simulation that writes every term out explicitly can take time exponential in the number of β-steps.

## Depends on

- [The weak call-by-value λ-calculus and its time and space measures](weak-call-by-value-lambda-calculus-and-its-cost-measures.md)

## Proof depends on

The required machines and bounds are listed in Expansion. Decision-class definitions for Boolean outputs are not prerequisites for this heap-and-closure computation.

## Expansion

This page becomes ready once:

- Heaps, closures and the unfolding relation by which a closure represents a term (Forster, Kunze and Roth, Section 2.3, Definitions 12 and 13) (statement prerequisite; not yet stated)
- The substitution machine and the heap machine with their step and state-size bounds (same source, Theorems 14 to 17) (proof prerequisite; not yet stated)
- The time-space inequality $\log \|s\|_T \in O(\|s\|_S)$ used in the hybrid simulation (same source, Theorem 21) (proof prerequisite; not yet stated)
- The two Turing-machine simulations and their interleaving (same source, Theorems 18 and 19 and the proof of Theorem 20) (proof prerequisite; not yet stated)

## Sources

- Yannick Forster, Fabian Kunze and Marc Roth, "The Weak Call-By-Value λ-Calculus is Reasonable for Both Time and Space", POPL 2020; arXiv:1902.07515: Theorem 20, with the size-explosion example $s_E\,\bar n$ in Section 1.
- Ugo Dal Lago and Simone Martini, "On Constructor Rewrite Systems and the Lambda Calculus", Logical Methods in Computer Science 8(3), 2012; arXiv:1208.0515: Theorem 18 (the normal form of a term-graph translation is computed in time polynomial in the term size and the number of β-steps) and the remark after it that reading back a λ-term from a term graph can take exponential time.
