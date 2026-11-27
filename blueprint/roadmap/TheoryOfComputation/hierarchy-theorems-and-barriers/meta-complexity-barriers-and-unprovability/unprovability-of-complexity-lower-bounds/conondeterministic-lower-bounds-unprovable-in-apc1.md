# Average-case co-nondeterministic lower bounds for NP are unprovable in a fragment of APC1

Pich and Santhanam prove unconditionally that, for every nondeterministic polynomial-time machine $M$, the theory $\mathsf{T}'_{\mathsf{APC}_1}$ cannot prove that $L(M)$ is hard on average for co-nondeterministic circuits of size $2^{n^\delta}$; in particular $\mathsf{PV}$ cannot.

For a nondeterministic machine $M$, a constant $n_0$, a rational $\delta \in (0,1)$ and a $2^{O(n)}$-time constructible $m(n) \le 2^n$, let $\mathrm{LB}^{\mathrm{coN}}_{\mathrm{tt}}(M, 2^{n^\delta}, m)$ be the $\forall\Sigma^b_2$-formula stating: for each $n > n_0$ with $n \in \mathrm{LogLog}$ and each co-nondeterministic circuit $D(x, z)$ with $n$-bit input $x$ and size $2^{n^\delta}$, there are $m$ tuples $(x_i, y_i, z_i)$ witnessing that at least $m$ inputs $x$ satisfy $M(x) \ne D(x)$, that is, for every $i \le m$ and all $y'_i, z'_i$,

$$
\big(M(x_i, y_i) = 1 \wedge D(x_i, z_i) = 0\big) \vee \big(M(x_i, y'_i) = 0 \wedge D(x_i, z'_i) = 1\big).
$$

**Theorem.** Let $n_0$ be a positive integer, $\delta \in (0,1)$ rational and $M$ a nondeterministic polynomial-time machine. Then $\mathsf{T}'_{\mathsf{APC}_1} \nvdash \mathrm{LB}^{\mathrm{coN}}_{\mathrm{tt}}(M, 2^{n^\delta}, 2^n/n)$, where $\mathsf{T}'_{\mathsf{APC}_1}$ is the true universal theory $\mathsf{T}_{\mathsf{PV}}$ plus the parameter-free dual weak pigeonhole principle.

## Expansion

The proof shows that provability implies falsity. From a proof, the KPT theorem for $\mathsf{T}'_{\mathsf{APC}_1}$ gives a constant-round interactive game, played by polynomial-size circuits, that witnesses errors of any co-nondeterministic circuit attempting $L(M)$. A Nisan–Wigderson generator based on a hardness-amplified version of $\neg M$ is itself such a circuit, so the game witnesses its errors, and Krajíček's reconstruction yields deterministic $2^{O(m)}$-size circuits approximating the amplified function. Hardness amplification then shows $L(M)$ is easy on most inputs, contradicting the lower bound; by soundness the statement is unprovable. The same method shows $\mathsf{T}'_{\mathsf{APC}_1}$ cannot prove that a polynomial-time injective map is a Rudich super-bit.

## Depends on

- [Jeřábek's theory APC1 and the dual weak pigeonhole principle](../bounded-arithmetic-and-witnessing/theory-apc1.md)
- [Cook's theory PV of polynomial-time reasoning](../bounded-arithmetic-and-witnessing/cooks-theory-pv.md)
- [The complexity class NP](../../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Proof depends on

- [The KPT witnessing theorem](../bounded-arithmetic-and-witnessing/kpt-witnessing-theorem.md)

## Sources

- Ján Pich and Rahul Santhanam, "Strong Co-Nondeterministic Lower Bounds for NP Cannot be Proved Feasibly", *STOC* 2021, DOI 10.1145/3406325.3451117 (Theorem 6, with Theorem 1 as its informal version and the formula of Section 3.2; Theorem 7 for super-bits; in the full version read).
