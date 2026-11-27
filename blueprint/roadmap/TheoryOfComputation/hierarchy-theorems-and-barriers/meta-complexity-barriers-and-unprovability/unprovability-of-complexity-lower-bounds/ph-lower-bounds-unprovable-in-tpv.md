# Strong lower bounds for the polynomial hierarchy are unprovable in T^i_PV and APC1

Li and Oliveira prove unconditionally that the theory of all true $\forall\Sigma^b_{i-1}$-sentences cannot prove that some polynomial-size $\Pi_i$-circuit is hard on average for $\Sigma_i$-circuits of size $2^{n^\delta}$. In particular $\mathsf{APC}_1$ cannot prove such a separation at the third level.

For functions $s_1, s_2, m$ and $n_0 \in \mathbb{N}$, let $\mathrm{LB}^i(s_1, s_2, m, n_0)$ be the $\mathcal{L}_{\mathsf{PV}}$-sentence

$$
\forall n \in \mathrm{LogLog},\ n \ge n_0\ \ \exists C \in \Pi_i\text{-}\mathsf{SIZE}[s_1(n)]\ \ \forall D \in \Sigma_i\text{-}\mathsf{SIZE}[s_2(n)]\ \ \exists\, m(n) \text{ distinct } x^1, \dots, x^{m(n)} \in \{0,1\}^n\ \ \textstyle\bigwedge_j \mathsf{Error}(C, D, x^j),
$$

where a $\Pi_i$-circuit $C(x, z_1, \dots, z_i)$ accepts $x$ iff $\forall z_1 \exists z_2 \cdots Q_i z_i\ C(x, \vec{z}) = 1$ (dually for $\Sigma_i$), and $\mathsf{Error}(C, D, x)$ says that $C$ and $D$ disagree on $x$. Thus $\mathrm{LB}^i$ states $\Pr_x[C(x) = D(x)] \le 1 - m(n)/2^n$. Let $\mathsf{T}^i_{\mathsf{PV}}$ be the theory of all $\forall\Sigma^b_{i-1}$-sentences over $\mathcal{L}_{\mathsf{PV}}$ true in $\mathbb{N}$.

**Theorem.** For every $i \ge 1$, $n_0 \in \mathbb{N}$, $\delta \in \mathbb{Q} \cap (0,1)$ and $d \ge 1$,

$$
\mathsf{T}^i_{\mathsf{PV}} \nvdash \mathrm{LB}^i(s_1, s_2, m, n_0), \quad s_1(n) = n^d,\ s_2(n) = 2^{n^\delta},\ m(n) = 2^n/n.
$$

**Corollary.** For every $n_0$, rational $\delta \in (0,1)$ and $d \ge 1$, $\mathsf{APC}_1 \nvdash \mathrm{LB}^3(n^d, 2^{n^\delta}, 2^n/n, n_0)$. For $i = 1$ this recovers, in a stronger formalization quantifying over the circuit $C$ inside the sentence, the result that $\mathsf{PV}$ does not prove $\mathrm{LB}^1(n^d, 2^{n^\delta}, 2^n/n, n_0)$.

## Proof sketch

Already $\mathrm{LB}^1$ is a $\forall\Sigma^b_4$-sentence, beyond the reach of KPT witnessing, so the proof uses the game-theoretic witnessing theorem for arbitrarily many quantifiers. A proof of the average-case lower bound yields a worst-case one; witnessing it with a fixed falsifier strategy and Krajíček's Nisan–Wigderson technique produces deterministic circuits of size $2^{m^{o(1)}}$ that approximate any polynomial-size $\Pi_i$-circuit with advantage $2^{-m^{o(1)}}$, and hardness amplification then shows every such circuit agrees with a small $\Sigma_i$-circuit on more than a $1 - 1/n$ fraction of inputs, contradicting the sentence. Since the theory is sound, the sentence is unprovable. The corollary follows because every axiom of $\mathsf{APC}_1$ follows from a true $\forall\Sigma^b_2$-sentence.

## Depends on

- [Cook's theory PV of polynomial-time reasoning](../bounded-arithmetic-and-witnessing/cooks-theory-pv.md)
- [Jeřábek's theory APC1 and the dual weak pigeonhole principle](../bounded-arithmetic-and-witnessing/theory-apc1.md)
- [The polynomial hierarchy](../../../complexity-classes/time-and-space-complexity-classes/ph.md)

## Proof depends on

- [Game-theoretic witnessing for sentences with arbitrarily many quantifiers](../bounded-arithmetic-and-witnessing/tree-exploration-witnessing-theorem.md)

## Sources

- Jiatu Li and Igor C. Oliveira, "Unprovability of Strong Complexity Lower Bounds in Bounded Arithmetic", *STOC* 2023, DOI 10.1145/3564246.3585144, arXiv:2305.15235v1 (Theorem 1.2, Main Theorem, and Corollary 1.4, Section 1.1).
- Igor C. Oliveira, "SIGACT News Complexity Theory Column 124: Meta-Mathematics of Computational Complexity Theory", *ACM SIGACT News* 56(1), 2025, DOI 10.1145/3726856.3726862, arXiv:2504.04416v1 (Theorem 5.6 and the proof overview of Section 5.2.1).
