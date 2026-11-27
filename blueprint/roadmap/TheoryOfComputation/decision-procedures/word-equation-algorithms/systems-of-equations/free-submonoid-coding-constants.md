# A free submonoid that codes constants by two variables


Words $C_0, \dots, C_{k-1}$ over two letters $a, b$ can be chosen so that, under every nonperiodic morphism, they map into the basis of the free monoid of words that begin and end with the image of a fixed word $B$, a monoid closed under taking commuting partners.

Let $k \ge 1$ and let $a, b$ be letters. Define

$$
A_i = a^i\, b^2\, a^{k - i + 1} \quad (0 \le i \le k + 1), \qquad B = A_k^2\, A_{k+1}^2\, A_k^2, \qquad C_i = B A_i B \quad (0 \le i \le k - 1) .
$$

Let $\beta : \{a, b\}^* \to \Sigma^*$ be a morphism with $\beta(ab) \neq \beta(ba)$, and let

$$
M = \big( \beta(B)\, \Sigma^* \cap \Sigma^*\, \beta(B) \big) \cup \{\varepsilon\} .
$$

Here a submonoid of $\Sigma^*$ is free if there is a set $B_M \subseteq M \setminus \{\varepsilon\}$, its basis, such that every element of $M$ has exactly one factorisation as a finite product of elements of $B_M$. Then:

1. $\beta(A_0), \dots, \beta(A_{k+1})$ and $\beta(B)$ are primitive;
2. $M$ is a free monoid;
3. $\beta(C_0), \dots, \beta(C_{k-1})$ belong to the basis of $M$;
4. if $U \in M \setminus \{\varepsilon\}$ and $UV = VU$, then $V \in M$.


## Depends on

- [Primitive word](../../../../Combinatorics/combinatorics-on-words/finite-words/lyndon-and-primitive-words/is-primitive-word.md)

## Proof depends on

- [Nonperiodic morphisms preserve primitivity of binary words](primitive-images-of-binary-primitive-words.md)
- [Stable submonoids of a free monoid are free](free-submonoids-and-stability.md)
- [Commuting words are powers of a common word](../../word-equations-with-length/commuting-words-are-powers-of-a-common-word.md)
- [Unique primitive root of a word](unique-primitive-root.md)
- [Nontrivial rotations move a primitive word](../../../../Combinatorics/combinatorics-on-words/finite-words/lyndon-and-primitive-words/rotate-ne-of-is-primitive-word.md)

## Expansion

1. Each $A_i = a^i b^2 a^{k-i+1}$ is primitive and has $k + 1 \ge 2$ occurrences of $a$ and two of $b$, so $\beta(A_i)$ is primitive; $\beta(B)$ is the image of the primitive word $001100$ under $0 \mapsto \beta(A_k)$, $1 \mapsto \beta(A_{k+1})$, a nonperiodic morphism because $\beta$ is injective (a morphism of $\{a, b\}^*$ with $\beta(ab) \neq \beta(ba)$ is injective; Saarela, Theorem 1(4)) and $A_k A_{k+1} \neq A_{k+1} A_k$, so $\beta(B)$ is primitive by the same theorem.
2. $M$ is a monoid. If $U, VW, UV, W \in M$ and $0 < |V| < |\beta(B)|$, then $\beta(B)$ occurs in $\beta(B)^2$ at a position strictly between $0$ and $|\beta(B)|$, which is a nontrivial rotation of $\beta(B)$ equal to $\beta(B)$, against primitivity; if $V = \varepsilon$ or $|V| \ge |\beta(B)|$, then $V \in M$ directly. So $M$ is stable, hence free by the characterisation of free submonoids by stability, whose basis is the set of nonempty elements that are not products of two nonempty elements.
3. If some $\beta(C_i)$ were a product of two nonempty elements of $M$, it would contain $\beta(B)^2$ and hence $\beta(A_k)^4$ as a factor; comparing positions modulo $|\beta(A_k)| = |\beta(A_j)|$ either forces $\beta(A_k) = \beta(A_{k+1})$ or $\beta(A_k) = \beta(A_i)$, against the injectivity of $\beta$, or makes $\beta(A_k)$ equal to a nontrivial rotation of itself, against primitivity.
4. If $V = \varepsilon$ or $|V| \ge |\beta(B)|$, then $V \in M$ directly. If $0 < |V| < |\beta(B)|$, then $U$ and $V$ are powers of a common word, hence of a common primitive word $R$ with $|R| \le |V| < |\beta(B)|$; as $\beta(B)$ is a prefix of $U$, $\beta(B) = R^j R'$ with $j \ge 1$ and $R'$ a proper prefix of $R$, nonempty because $\beta(B)$ is primitive; as $\beta(B)$ is also a suffix of $U \in R^+$, its suffix of length $|R|$ is both $R$ and a nontrivial rotation of $R$, against primitivity.

This page becomes ready once the injectivity of a morphism $\beta : \{a, b\}^* \to \Sigma^*$ with $\beta(ab) \neq \beta(ba)$ (Saarela, ICALP 2020, Theorem 1(4)) is a page of its own.

## Sources

- Aleksi Saarela, "Hardness Results for Constant-Free Pattern Languages and Word Equations", ICALP 2020, LIPIcs 168, Article 140 (2020), https://doi.org/10.4230/LIPIcs.ICALP.2020.140, Lemma 15 and its proof (Section 5, "Noncommuting satisfiability"), with Theorem 1(4) and Theorem 2 (Section 2)
