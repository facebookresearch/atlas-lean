# Nonperiodic morphisms preserve primitivity of binary words

A nonperiodic morphism maps every primitive word over two letters, in which both letters occur at least twice, to a primitive word.

Let $W \in \{y, z\}^*$ be a [primitive word](../../../../Combinatorics/combinatorics-on-words/finite-words/lyndon-and-primitive-words/is-primitive-word.md) in which each of the letters $y$ and $z$ occurs at least twice, and let $\alpha : \{y, z\}^* \to \Sigma^*$ be a morphism with $\alpha(yz) \neq \alpha(zy)$. Then $\alpha(W)$ is primitive.

The hypothesis on occurrences is needed: for $W = yz$ and $\alpha(y) = a$, $\alpha(z) = bab$ we get $\alpha(W) = (ab)^2$.

## Depends on

- [Primitive word](../../../../Combinatorics/combinatorics-on-words/finite-words/lyndon-and-primitive-words/is-primitive-word.md)

## Proof depends on

None.

## Expansion

This generalises the theorem of R. C. Lyndon and M.-P. Schützenberger that $x^k = y^m z^p$ with $k, m, p \ge 2$ has only periodic solutions. It was proved by J.-C. Spehner and, independently, by E. Barbin-Le Rest and M. Le Rest.

This page becomes ready once a proof is a page of its own; the shorter published proof cited by Saarela is in A. Saarela, "Studying word equations by a method of weighted frequencies", Fundamenta Informaticae 162(2–3) (2018), 223–235, https://doi.org/10.3233/FI-2018-1722.

## Sources

- Aleksi Saarela, "Hardness Results for Constant-Free Pattern Languages and Word Equations", ICALP 2020, LIPIcs 168, Article 140 (2020), https://doi.org/10.4230/LIPIcs.ICALP.2020.140, Theorem 7 (Section 2), with the attribution to Spehner, Barbin-Le Rest and Le Rest, and Saarela
