# A quadratic equation whose length set is not Presburger-definable

The set of length vectors of solutions of the quadratic equation $xaby = yabx$ involves a gcd condition and is not definable in Presburger arithmetic. So the length set of a quadratic equation cannot in general be described exactly by a Presburger formula.

Let $\Sigma$ be an alphabet of constants containing two distinct letters $a, b$. For a word equation $E$ with variables $x_1, \dots, x_k$ (in a fixed order), its *length abstraction* is

$$\mathrm{LEN}(E) = \{ (|\sigma(x_1)|, \dots, |\sigma(x_k)|) : \sigma \text{ a solution of } E \} \subseteq \mathbb N^k,$$

where solutions map variables to possibly empty words over $\Sigma$. For the regular (hence quadratic) equation $xaby = yabx$ with variables $x, y$,

$$\mathrm{LEN}(xaby = yabx) = \{(m, n) \in \mathbb N^2 : m = n \ \text{ or } \ (m = 0,\ n \text{ even}) \ \text{ or } \ (n = 0,\ m \text{ even}) \ \text{ or } \ (m, n > 0,\ \gcd(m + 2, n + 2) > 1)\},$$

and this set is not definable by a formula of Presburger arithmetic, the first-order theory of $(\mathbb N, 0, 1, +, \le)$.

## Depends on

- [Quadratic, regular and regular-ordered word equations](restricted-classes-of-word-equations.md)
- [Solution of a word equation](../string-constraints-and-word-equations/ordinary-word-equations/satisfies.md)

## Proof depends on

- [Commuting words are powers of a common word](commuting-words-are-powers-of-a-common-word.md)

## Expansion

*Every listed pair is realised.* For $m = n$ take $\sigma(x) = \sigma(y)$ arbitrary of that length. For $m = 0$ the equation becomes $aby = yab$; by the commutation lemma (with $ab$ primitive) its solutions are $\sigma(y) \in (ab)^*$, of every even length, and symmetrically for $n = 0$. For $m, n > 0$ with $d = \gcd(m + 2, n + 2) > 1$, take $\sigma(x), \sigma(y) \in (a^{d-1} b)^* a^{d-2}$ of lengths $m$ and $n$ (possible since $d$ divides $m + 2$ and $n + 2$). Then $\sigma(x)ab$ and $\sigma(y)ab$ are powers of $a^{d-1}b$, so $\sigma(x) ab \sigma(y) = \sigma(y) ab \sigma(x)$.

*No other pair occurs.* Take a solution $(u, v)$ whose length pair is not listed, with $|u| + |v|$ minimal. If $u = v$, then $|u| = |v|$. If $u = \varepsilon$, then $abv = vab$ forces $v \in (ab)^*$, so $|v|$ is even, and symmetrically for $v = \varepsilon$. So $u, v$ are nonempty, $|u| \ne |v|$, say $|u| > |v|$, and $\gcd(|u| + 2, |v| + 2) = 1$. If $|u| = |v| + 1$, compare position $|u| + 1$ of the two sides: on the left it is the letter $a$ following $u$, on the right it is the last letter of $vab$, namely $b$, a contradiction. So $|u| \ge |v| + 2$, and comparing prefixes shows that $u = vab\,u'$ for a word $u'$; cancelling $vab$ on the left of both sides gives $u'abv = vabu'$. If $u' = \varepsilon$, then $abv = vab$, so $v \in (ab)^*$ and $|u| = |v| + 2$, making both $|u| + 2$ and $|v| + 2$ even, contrary to the gcd being $1$. Otherwise $(u', v)$ is a solution with $\gcd(|u'| + 2, |v| + 2) = \gcd(|u| + 2, |v| + 2) = 1$, both components nonempty and $|u'| \ne |v|$ (else the gcd would be $|v| + 2 > 1$), so its pair is not listed and it is shorter, contradicting minimality.

*Not Presburger-definable.* Presburger-definable subsets of $\mathbb N^k$ are exactly the semilinear sets, and a subset of $\mathbb N$ is Presburger-definable exactly when it is ultimately periodic (in Mathlib as [definability and semilinearity](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/ModelTheory/Arithmetic/Presburger/Definability.lean#L147 "FirstOrder.Language.presburger.definable_iff_isSemilinearSet") and [the one-dimensional case](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/ModelTheory/Arithmetic/Presburger/Definability.lean#L153 "FirstOrder.Language.presburger.definable₁_iff_ultimately_periodic")). Suppose $\mathrm{LEN}(xaby = yabx)$ were defined by a formula $\varphi(m, n)$. Then $\psi(m, n) := m > 0 \wedge n > 0 \wedge (m = n \vee \varphi(m, n))$ defines $\{(m, n) : m, n > 0,\ \gcd(m + 2, n + 2) > 1\}$: off the diagonal this is the last disjunct, and on the diagonal $\gcd(m + 2, m + 2) = m + 2 > 1$. Hence, for $p, q \ge 3$, the relation $\gcd(p, q) > 1$ is Presburger-definable, and so is the set

$$P = \{p \ge 5 : \gcd(p, q) = 1 \text{ for all } q \text{ with } 3 \le q < p\}.$$

$P$ is the set of primes $p \ge 5$: a prime $p \ge 5$ is coprime to all smaller $q \ge 3$; an even $p \ge 5$ has $\gcd(p, 4) \ge 2$ with $4 < p$; an odd composite $p$ has an odd prime divisor $q$ with $3 \le q < p$. But the set of primes is not ultimately periodic: if $x \in P \iff x + c \in P$ for all $x \ge k$, with $c > 0$, then for a prime $p \ge \max(k, 5)$ also $p + pc = p(1 + c) \in P$, which is composite. This contradicts the characterisation of Presburger-definable subsets of $\mathbb N$, so $\mathrm{LEN}(xaby = yabx)$ is not Presburger-definable.

## Sources

- Anthony W. Lin and Rupak Majumdar, "Quadratic Word Equations with Length Constraints, Counter Systems, and Presburger Arithmetic with Divisibility", *Logical Methods in Computer Science* 17(4:4), 2021, <https://doi.org/10.46298/lmcs-17(4:4)2021>; numbers from the accepted version arXiv:2007.15478v6: Section 3.4 (length abstraction), Example 3.4, Theorem 3.5 (existence of a quadratic equation with non-Presburger length abstraction) and Lemma 3.6 (the description of $\mathrm{LEN}(xaby = yabx)$), with their proofs; the non-definability step there appeals to the non-definability of coprimality, made explicit above.
