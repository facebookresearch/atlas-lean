# CIKK: AC0[2] is learnable with quasi-polynomially many membership queries via the rank property

For depth $d$, size $s$, $n$ inputs and exponents $e, h$, there are explicit parameters $g$ and $\ell$ such that the CIKK learner whose test accepts the truth tables of the GF(2) rank property at input length $\ell$ learns every function on $n$ bits computed by a circuit of depth at most $d$ and size at most $s$ with AND, OR, NOT and $\mathrm{MOD}_2$ gates, under the uniform distribution with membership queries, with error $2^{-e}$ and confidence $1 - 2^{-h}$. With $D = d + 7$, $M = 2^{e+10}(3e + 42)$ and $B = \lfloor\log_2(M^2(s + 6(n+1)^2 + 3))\rfloor + 1$, it uses at most

$$
(h+1)\,2^{12 \cdot 2^{2D(5D+25)} B^{2D} + 6e + 59}
$$

queries and outputs hypotheses with De Morgan circuits of at most $2^{17 \cdot 2^{2D(5D+25)}B^{2D} + 9e + 76}$ gates. For fixed $d$, $B = O(e + \log(ns))$, so both are quasi-polynomial in $n$, $s$ and $2^e$.

## Proof sketch

Every generator output on the amplified target is computed by a circuit with $\mathrm{MOD}_2$ gates of depth at most $d + 7$ and size at most $ks + 6(kn+k)^2 + 3$. The Razborov-Smolensky polynomial method shows such circuits have truth-table matrices of low GF(2) rank, while at least half of all functions have high rank, so the rank property is dense and rejects all generator outputs at the chosen length. The query and size bounds follow from the closed forms of the general learner with $\ell$ quasi-logarithmic.

## Depends on

- [The class $\mathsf{AC}^0(m)$](../../complexity-classes/time-and-space-complexity-classes/ac0-mod.md)
- [Carmosino-Impagliazzo-Kabanets-Kolokolova: learning from a dense test rejecting the amplified generator](learning-from-a-dense-test.md)

## Proof depends on

- [Carmosino-Impagliazzo-Kabanets-Kolokolova: learning from a dense test rejecting the amplified generator](learning-from-a-dense-test.md)
- [The CIKK learner's hypotheses are circuits of size $2^{O(g + e + \ell)}$ times the test size](cikk-learner-hypothesis-size.md)
- [Razborov–Smolensky polynomial approximation of AC0[p]](../../circuit-complexity/constant-depth-circuit-lower-bounds/razborovsmolensky-polynomial-approximation-of.md)
- [Razborov: majority is not in AC0[mod 2]](../../circuit-complexity/razborov-majority-not-in-ac0-mod-two.md)

## Sources

- Marco L. Carmosino, Russell Impagliazzo, Valentine Kabanets and Antonina Kolokolova, "Learning Algorithms from Natural Proofs", 31st Conference on Computational Complexity (CCC 2016), LIPIcs 50, 2016.
- Alexander A. Razborov, "Lower Bounds on the Size of Bounded Depth Circuits over a Complete Basis with Logical Addition", Mathematical Notes of the Academy of Sciences of the USSR, 1987.
- Roman Smolensky, "Algebraic Methods in the Theory of Lower Bounds for Boolean Circuit Complexity", Proceedings of the 19th Annual ACM Symposium on Theory of Computing, 1987.
