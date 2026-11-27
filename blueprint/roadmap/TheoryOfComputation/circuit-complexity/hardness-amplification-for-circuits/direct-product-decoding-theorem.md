# Direct-product decoding

There are an absolute constant $c>0$ and a probabilistic algorithm with the following property. Let $f:\{0,1\}^n\to\{0,1\}$, let $k\in\mathbb{N}$ and $0<\varepsilon,\delta<1$ with $\varepsilon>e^{-\delta k/c}$, and let $C'$ be a circuit that computes the direct product $f^k$ (on $k$-sets, or equivalently on $k$-tuples, of $n$-bit inputs) correctly on at least an $\varepsilon$ fraction of its inputs. Given oracle access to $C'$, the algorithm outputs with probability $\Omega(\varepsilon)$ a circuit $C$ that computes $f$ correctly on at least a $1-\delta$ fraction of $\{0,1\}^n$. Equivalently, agreement $\varepsilon$ with $f^k$ yields error $\delta=O(\log(1/\varepsilon)/k)$. The output $C$ is an $\mathsf{AC}^0$ circuit of size $\mathrm{poly}(n,k,\log(1/\delta),1/\varepsilon)$ with $O(\log(1/\delta)/\varepsilon)$ oracle gates for $C'$, so it has size polynomial in $n$, $k$, $1/\varepsilon$ and the size of $C'$. Up to the constant $c$ the relation between $k$, $\delta$ and $\varepsilon$ is optimal.

## Proof sketch

Pick a random $k$-set $B$ and a random subset $A\subseteq B$ of size $k/2$, and record the values $C'(B)|_A$ as advice. On input $x$, repeatedly embed $x$ into random $k$-sets $B'\supseteq A$ and output the answer of $C'$ at $x$ on the first $B'$ whose answers agree with the advice on $A$. A sampling argument shows that, with probability $\Omega(\varepsilon)$ over $(A,B)$, consistent sets are mostly correct, so the resulting circuit errs on at most a $\delta$ fraction of inputs.

## Depends on

- [Average-case hardness against circuits](average-case-hardness-against-circuits.md)

## Sources

- Russell Impagliazzo, Ragesh Jaiswal, Valentine Kabanets, Avi Wigderson, "Uniform Direct Product Theorems: Simplified, Optimized, and Derandomized", SIAM Journal on Computing 39(4), 2010 (Theorem 1.2 and Remark 1.3).
- Marco L. Carmosino, Russell Impagliazzo, Valentine Kabanets, Antonina Kolokolova, "Learning Algorithms from Natural Proofs", 31st Conference on Computational Complexity (CCC 2016), LIPIcs 50, 2016.
