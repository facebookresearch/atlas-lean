# Learning size-s circuits from a dense property of functions with large circuit complexity

Let $\Lambda$ be a circuit class containing $\mathsf{AC}^0[p]$ for some prime $p$, and let $u : \mathbb{N} \to \mathbb{N}$ be a size function. Let $R$ be a property of Boolean functions that is constructive (membership of a function on $\ell$ bits is decidable from its truth table in time polynomial in $2^\ell$), has largeness at least $1/5$ (it holds for at least a $1/5$ fraction of all functions on $\ell$ bits), and is useful against $\Lambda[u]$ (for all large $\ell$, no function on $\ell$ bits computed by a $\Lambda$-circuit of size at most $u(\ell)$ has it). Then there is a randomized algorithm that, given membership queries to any $f : \{0,1\}^n \to \{0,1\}$ computed by a $\Lambda$-circuit of size $s$, produces a circuit computing $f$ on all but an $\varepsilon$ fraction of inputs in time

$$
\mathrm{poly}\big(n, 1/\varepsilon, 2^{u^{-1}(\mathrm{poly}(n, 1/\varepsilon, s))}\big).
$$

It is the learner from a dense test whose test accepts exactly the truth tables, of length $L = 2^\ell$ with $u^{-1}(\mathrm{poly}(n, 1/\varepsilon, s)) < \ell \le n$ (which exists whenever $u^{-1}(\mathrm{poly}(n, 1/\varepsilon, s)) < n$), of the functions on $\ell$ bits that have $R$.

## Proof sketch

Each function $i \mapsto G^{\mathrm{Amp}(f)}(z)_i$ on $\ell$ bits is computed by a circuit built from a circuit for $f$, the circuits for $\mathrm{Amp}$ and the design's selector circuits, all in $\Lambda$, of size $s_g \le \mathrm{poly}(n, 1/\varepsilon, s)$. Choosing $\ell$ with $u^{-1}(s_g) < \ell$, usefulness makes the test reject every generator output, and largeness is the density condition. The learner from a dense test then runs in time $\mathrm{poly}(n, 1/\varepsilon, L)$.

## Depends on

- [Carmosino-Impagliazzo-Kabanets-Kolokolova: learning from a dense test rejecting the amplified generator](learning-from-a-dense-test.md)
- [Natural property](../natural-proofs-barrier/natural-property.md)
- [Truth table](../natural-proofs-barrier/truth-table.md)

## Sources

- Marco L. Carmosino, Russell Impagliazzo, Valentine Kabanets and Antonina Kolokolova, "Learning Algorithms from Natural Proofs", 31st Conference on Computational Complexity (CCC 2016), LIPIcs 50, 2016, Section 5.1, Theorem 5.1 and its proof, with Definition 2.6 and Lemma 2.7.
- Alexander A. Razborov and Steven Rudich, "Natural Proofs", Journal of Computer and System Sciences, 1997.
