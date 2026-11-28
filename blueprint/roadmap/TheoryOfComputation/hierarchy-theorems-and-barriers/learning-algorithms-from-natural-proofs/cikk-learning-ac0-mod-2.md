# CIKK: AC0[2] is learnable with quasi-polynomially many membership queries via the rank property

For a Boolean function $f$ on $n$ bits and $0 \le a, b \le n$, let $A^{a,b}(f)$ be the $\binom{n}{a} \times \binom{n}{b}$ matrix over GF(2) whose rows are indexed by the $a$-subsets $I$ and whose columns are indexed by the $b$-subsets $J$ of $[n]$, with entry $\bigoplus_{x \in Z(I \cup J)} f(x)$, where $Z(K) = \{x \in \{0,1\}^n : x_i = 0 \text{ for all } i \in K\}$. The *GF(2) rank property* accepts $f$ if, for $a = n/2 - \sqrt n$ and at least one $0 \le b \le a$,

$$
\operatorname{rank} A^{a,b}(f) \ge \frac{2^n}{140\,n^2}.
$$

It is decidable from truth tables in $\mathsf{NC}^2$, holds for at least half of all functions on $n$ bits, and is useful against circuits of depth $d$ with AND, OR, NOT and $\mathrm{MOD}_2$ gates of size up to $2^{\Omega(n^{1/(2d)})}$. For every fixed depth $d$, the learner from a dense test whose test accepts the truth tables of the functions with the rank property, at a suitable input length $\ell \le n$ whenever such a length exists, learns every function $f$ on $n$ bits computed by such a circuit of depth $d$ and size $s$, with membership queries under the uniform distribution, to within error $\varepsilon$, in time quasi-polynomial in $ns/\varepsilon$; in particular it makes quasi-polynomially many queries.

## Proof sketch

The three properties of the rank property are the natural property embedded in Razborov's proof that majority is not in $\mathsf{AC}^0[2]$: matrices of truth tables of small circuits with $\mathrm{MOD}_2$ gates have low GF(2) rank by the polynomial method, while at least half of all functions reach the threshold. Apply the learning from a property useful against circuits with $\Lambda = \mathsf{AC}^0[2]$ of depth $d$ and $u(\ell) = 2^{\Omega(\ell^{1/(2d)})}$: then $u^{-1}(\mathrm{poly}(n, 1/\varepsilon, s))$ is polylogarithmic in $ns/\varepsilon$, and the running time $\mathrm{poly}(n, 1/\varepsilon, 2^{u^{-1}(\cdot)})$ is quasi-polynomial.

The sources leave the constants unspecified. One explicit instantiation uses that every generator output on the amplified target is computed by a circuit with $\mathrm{MOD}_2$ gates of depth at most $d + 7$ and size at most $ks + 6(kn+k)^2 + 3$. With error $2^{-e}$, confidence $1 - 2^{-h}$, $D = d + 7$, $M = 2^{e+10}(3e + 42)$ and $B = \lfloor\log_2(M^2(s + 6(n+1)^2 + 3))\rfloor + 1$, the explicit learner from a dense test makes at most $(h+1)\,2^{12 \cdot 2^{2D(5D+25)} B^{2D} + 6e + 59}$ queries and outputs hypotheses with De Morgan circuits of at most $2^{17 \cdot 2^{2D(5D+25)}B^{2D} + 9e + 76}$ gates; for fixed $d$, $B = O(e + \log(ns))$.

## Depends on

- [The class $\mathsf{AC}^0(m)$](../../complexity-classes/time-and-space-complexity-classes/ac0-mod.md)
- [Carmosino-Impagliazzo-Kabanets-Kolokolova: learning from a dense test rejecting the amplified generator](learning-from-a-dense-test.md)
- [Natural property](../natural-proofs-barrier/natural-property.md)

## Proof depends on

- [Learning size-s circuits from a dense property of functions with large circuit complexity](learning-from-a-property-useful-against-circuits.md)
- [The CIKK learner's hypotheses are circuits of size $2^{O(g + e + \ell)}$ times the test size](cikk-learner-hypothesis-size.md)
- [Razborov–Smolensky polynomial approximation of AC0[p]](../../circuit-complexity/constant-depth-circuit-lower-bounds/razborovsmolensky-polynomial-approximation-of.md)
- [Razborov: majority is not in AC0[mod 2]](../../circuit-complexity/razborov-majority-not-in-ac0-mod-two.md)

## Sources

- Marco L. Carmosino, Russell Impagliazzo, Valentine Kabanets and Antonina Kolokolova, "Learning Algorithms from Natural Proofs", 31st Conference on Computational Complexity (CCC 2016), LIPIcs 50, 2016, Section 5.2, Theorem 5.3, the natural property useful against AC0[2] after it, and Corollary 5.4, with Theorem 5.1 and the running times listed after its proof.
- Alexander A. Razborov, "Lower Bounds on the Size of Bounded Depth Circuits over a Complete Basis with Logical Addition", Mathematical Notes of the Academy of Sciences of the USSR, 1987.
- Roman Smolensky, "Algebraic Methods in the Theory of Lower Bounds for Boolean Circuit Complexity", Proceedings of the 19th Annual ACM Symposium on Theory of Computing, 1987.
