# Learning small circuits from interactive witnessing of circuit lower bounds

Pich shows that if errors of most small circuits trying to compute some Boolean function can be found by $2^{O(n)}$-size circuits with only oracle access, interactively and with at most $\log n$ corrections, then polynomial-size circuits are learnable over the uniform distribution with membership queries by circuits of size $2^{O(n)}$.

Let $d \ge 2$, $k, K \ge 1$, and let $H$ be a Boolean function on $n$ inputs. Assume there are circuits $W^1_1, \dots, W^b_{\log n}$ of size $2^{Kn}$, with $b = 2^{Kn}$, such that for each distribution $\mathcal{R}$ on $n^{10dk}$-size circuits with $n$ inputs there is $j \in [b]$ with the following property: given oracle access to a circuit $D$ drawn from $\mathcal{R}$, with probability at least $1 - 3/n^3$ the interactive protocol succeeds, in which $W^j_1$ queries $D$ and outputs a not-yet-queried $x_1$ with $D(x_1) \ne H(x_1)$, or else $W^j_2$ receives the correction $D(x_1) = H(x_1)$, makes further queries and proposes $x_2$, and so on, until some $W^j_t$ with $t \le \log n$ outputs a not-yet-queried $x_t$ with $D(x_t) \ne H(x_t)$. Then circuits of size $n^{dk}$ with $n^d$ inputs can be learned by circuits of size $2^{K'n}$ over the uniform distribution with non-adaptive membership queries, with confidence $2^{-K'n^2}$ and up to error $1/2 - 2^{-K'n^2}$, where $K'$ depends only on $K$.

## Expansion

It suffices that the witnessing works for distributions given by a Nisan–Wigderson generator based on the target circuit $C$: with an $(n, n^d)$-design, the functions $x \mapsto C(w|_{J_x})$ have circuits of size $n^{10dk}$. Running the witnessing protocol on these functions and answering corrections by queries to $C$, Krajíček's interactive reconstruction turns the witnessed errors into a circuit that approximates $C$; the main difficulty is that the witnessing circuits may fail on a noticeable fraction of the circuits they are given. A converse also holds, giving a characterization of learning, and white-box witnessing of this kind is what witnessing theorems extract from proofs of circuit lower bounds in bounded arithmetic.

## Depends on

- [Randomized membership-query learner as a family of decision trees](../../../circuit-complexity/learning-under-the-uniform-distribution/membership-query-learner.md)
- [Circuit complexity of a Boolean function and truth tables](../../../circuit-complexity/minimum-circuit-size-problem/circuit-complexity-of-a-boolean-function.md)

## Proof depends on

- [Nisan-Wigderson reconstruction as a membership-query weak learner (one run)](../../learning-algorithms-from-natural-proofs/nisan-wigderson-reconstruction-weak-learner.md)

## Sources

- Ján Pich, "Learning Algorithms from Circuit Lower Bounds", *Computational Complexity* 33, 2024, DOI 10.1007/s00037-024-00261-4, arXiv:2012.14095v1 (Theorem 1, Section 3.1, and Definition 3 of PAC learning, Section 2).
