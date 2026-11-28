# Commuting words are powers of a common word

Two words commute exactly when both are powers of one common word.

Let $\Sigma$ be an alphabet and $u, v \in \Sigma^*$. Then $uv = vu$ if and only if there are a word $w \in \Sigma^*$ and natural numbers $p, q$ with $u = w^p$ and $v = w^q$.

## Depends on

None.

## Proof depends on

- [Length-directed Levi's lemma](../string-constraints-and-word-equations/levi-of-le.md)

## Expansion

If $u = w^p$ and $v = w^q$ then $uv = w^{p+q} = vu$. Conversely, argue by induction on $|u| + |v|$. If $u$ or $v$ is empty, take $w$ to be the other word (or $w$ empty) with exponent $1$ and $0$. Otherwise assume $|u| \le |v|$; from $uv = vu$ and the length-directed Levi lemma there is a word $t$ with $v = ut$, and then $u \cdot ut = ut \cdot u$ gives $ut = tu$ after cancelling the leading $u$. Since $|u| + |t| < |u| + |v|$, by induction $u = w^p$ and $t = w^s$ for some $w$, so $v = w^{p+s}$.

As a derived consequence, a word commuting with a [primitive word](../../../Combinatorics/combinatorics-on-words/finite-words/lyndon-and-primitive-words/is-primitive-word.md) $u$ is a power of $u$: in $u=w^p$, primitivity forces $p=1$ and $w=u$. In particular, a word commuting with a letter $a$ lies in $a^*$. A letter $a$ and a word of the form $a^i b$ with $b\ne a$ are primitive. These specializations are consequences of the main theorem, not additional statements attributed to the cited locators.

## Sources

- Joel D. Day, Vijay Ganesh, Paul He, Florin Manea and Dirk Nowotka, "The Satisfiability of Word Equations: Decidable and Undecidable Theories", Reachability Problems (RP 2018), LNCS 11123, pp. 15–29, 2018, <https://doi.org/10.1007/978-3-030-00250-3_2>, Lemma 1 (Commutativity Equation).
- Joel D. Day, Vijay Ganesh, Nathan Grewal, Matthew Konefal and Florin Manea, "A Closer Look at the Expressive Power of Logics Based on Word Equations", *Theory of Computing Systems* 68:322–379, 2024, <https://doi.org/10.1007/s00224-023-10154-8>, Section 2, Lemma 1 (two-variable consequence of the defect theorem, citing M. Lothaire, *Combinatorics on Words*, Theorem 1.2.5 and Corollary 1.2.6). The induction above is the standard proof, written out here.
