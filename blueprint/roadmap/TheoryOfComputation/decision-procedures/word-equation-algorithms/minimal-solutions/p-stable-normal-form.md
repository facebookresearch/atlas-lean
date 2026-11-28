# p-stable normal form of a word

For a primitive word $p$, the $p$-stable normal form of a word is a shortest factorisation into factors and powers of $p$, with boundary conditions saying which factors may begin or end with $p$.

Let $A$ be an alphabet and $p \in A^+$ a primitive word. The $p$-stable normal form of a word $w \in A^*$ is a shortest sequence $(u_0, \alpha_1, u_1, \dots, \alpha_k, u_k)$ with $k \ge 0$, words $u_0, \dots, u_k \in A^*$ and natural numbers $\alpha_1, \dots, \alpha_k$, such that

1. $w = u_0\, p^{\alpha_1}\, u_1 \cdots p^{\alpha_k}\, u_k$;
2. $k = 0$ if and only if $p^2$ is not a factor of $w$;
3. if $k \ge 1$, then $u_0 \in A^* p \setminus A^* p^2 A^*$, $u_i \in (A^* p \cap p A^*) \setminus A^* p^2 A^*$ for $1 \le i < k$, and $u_k \in p A^* \setminus A^* p^2 A^*$.

Every word has a $p$-stable normal form, and it is unique: two $p$-stable normal forms $(u_0, \alpha_1, \dots, u_k)$ and $(v_0, \beta_1, \dots, v_\ell)$ of the same word have $k = \ell$, $u_i = v_i$ and $\alpha_i = \beta_i$ for all $i$.

## Depends on

- [Primitive word](../../../../Combinatorics/combinatorics-on-words/finite-words/lyndon-and-primitive-words/is-primitive-word.md)

## Proof depends on

- [Nontrivial rotations move a primitive word](../../../../Combinatorics/combinatorics-on-words/finite-words/lyndon-and-primitive-words/rotate-ne-of-is-primitive-word.md)

## Expansion

The definition is the source's Definition 2.6 and uniqueness its Proposition 2.7, proved by induction on $k$: minimality forces $k = \ell$; comparing the shorter of $u_0, v_0$ with the other and using that a primitive word $p$ occurs in $p^2$ only as a prefix or a suffix gives $u_0 = v_0$, then $\alpha_1 = \beta_1$, and the rest is the normal form of the remaining suffix. The occurrence fact is the statement that nontrivial rotations move a primitive word: if $p^2 = x p y$ with $x, y$ nonempty, then $p = x t$ with $|t| = |y|$ and the occurrence reads $p = t x$, a nontrivial rotation of $p$.

This page becomes ready once existence of the normal form for every word is a page of its own; the report leaves it to Problem 2.1, a greedy computation of the $p$-stable normal form.

## Sources

- Volker Diekert, "Makanin's Algorithm for Solving Word Equations with Regular Constraints", Report Nr. 1998/02, Fakultät Informatik, Universität Stuttgart (1998), https://elib.uni-stuttgart.de/server/api/core/bitstreams/3846bd76-7ca9-4e0d-8595-75cc76db3018/content; with minor modifications Chapter 12, "Makanin's Algorithm", of M. Lothaire, *Algebraic Combinatorics on Words*, Cambridge University Press (2002), 387–442, https://doi.org/10.1017/CBO9781107326019.013, Definition 2.6 and Proposition 2.7 (Section 2.3, "Stable normal forms")
