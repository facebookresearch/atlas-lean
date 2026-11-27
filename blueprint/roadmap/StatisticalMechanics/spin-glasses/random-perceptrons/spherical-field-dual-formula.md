# Spherical cascade field values and the attained dual entropy formula

Take a depth $k\ge0$, positive weights $(w_i)_{i=0}^k$ summing to one, and $0\le h_0\le\cdots\le h_k$. Let $Z_i=\sum_{j\le i}w_j$ for $0\le i<k$. At depth $i$ use an independent marked Poisson cascade with log-weight intensity $Z_i e^{-Z_i x}\,dx$, and a standard Gaussian vector mark in dimension $n+1$ at each child, independent of its descendant cascade. Each leaf weight is the product of $e^x$ along its path. Here the source defines count integration recursively through the mass-biased kernel normalized by $\sum e^x$ and then reweighted by $(\sum e^x)e^{-x}$. At depth zero the weight is one. The leaf field is the shared Gaussian root vector (coordinate variance $2h_0$) plus the marked increments in root-to-leaf order, with coordinate variances $2(h_1-h_0),\ldots,2(h_k-h_{k-1})$. In the source recurrence the state is a sequence $u$ of vectors, initially constant at the root vector. Processing mark $g$ replaces $u_i$ by $u_{i+1}+\sigma_i g$, where $\sigma_i=\sqrt{2(h_{k-i}-h_{k-i-1})}$ for $i<k$ and $0$ otherwise. At the leaf read coordinate $0$: the first mark therefore has coefficient $\sigma_{k-1}$ and the last has coefficient $\sigma_0$. For each cascade and root field take the sphere average at radius $\sqrt{n+1}$ of the weighted sum of $\exp(\langle\text{leaf field},u\rangle)$, divide by the total cascade weight, take the log divided by $n+1$, then expectation and subtract $h_k$. Call the result $F_n(w,h)$.

More precisely, the depth-zero cascade is the deterministic point of the one-point space. At the next level its law is the Poisson random-measure law of the product of the log intensity, the independent Gaussian mark law and the recursively specified child-cascade law. The source forms this random measure by summing independent finite pieces from the intensity's s-finite decomposition: in each piece sample a Poisson count at that finite mass and IID points from its normalized measure (the zero-mass mark fallback cannot contribute). For each realized node measure $\eta$ on triples $(x,g,c)$, set $T=\int e^x\,d\eta$ in the extended nonnegative reals. The mass kernel is $T^{-1}(\eta\text{ weighted by }e^x)$ and the count kernel is that kernel weighted by $\operatorname{ofReal}(T_{\mathbb R}e^{-x})$, where $T_{\mathbb R}$ is the totalized real projection of $T$. To integrate a leaf test, at depth zero evaluate it on the final field, and at each internal step integrate $e^x$ times the child's recursive value against the count kernel, with the corresponding increment of the field. The angular numerator is the lower integral of the leaf test $e^{\langle\text{field},u\rangle}$ against the sphere law at radius $\sqrt{n+1}$. The denominator is the same leaf recursion with terminal test one. Project both extended results separately to the reals before dividing and taking the totalized real logarithm. Only after dividing by $n+1$ take the real expectation over the independent root and cascade and subtract $h_k$. This specification retains the kernel even on degenerate realizations; unweighted counting agrees at nodes where $0<T<\infty$, not by an identity on all measures.

For any law on $[0,1]$ with CDF $m$, set $a_m(t)=\int_t^1m(s)\,ds$. Let $E(m)$ be one half the extended nonnegative integral of the **truncated** difference between the extended reciprocals of $a_m(t)$ and $1-t$ (embed the two reals before inversion). For monotone $0\le q_0\le\cdots\le q_k<1$, use the CDF $m_q(t)=\sum_{i:q_i\le t}w_i$. For each $h$, the real dual objective $E(m_q)_{\mathbb R}-\sum_iw_ih_i q_i$ attains its minimum over these $q$. The real projection of $E(m)$ maps infinity to zero. As $n\to\infty$, $F_n(w,h)$ converges to that minimum uniformly on every compact set of such $h$ at the fixed weights and depth.

For a nondecreasing quantile $q:[0,1]\to[0,1]$ with $q\le B$ almost everywhere, $0\le B<1$, let $m_q$ now denote the CDF of $q(U)$ for uniform $U$, $a_q(t)=\int_0^1(1-\max(q(u),t))\,du$, $A_q(r)=\int_0^r a_q(t)^{-2}\,dt$, and $h_q(u)=A_{q\wedge B}(q(u)\wedge B)/2$. The field is nonnegative, monotone and bounded by $B/[2(1-B)^2]$. Interpret $F_n(h)$ for bounded monotone $h$ by rounding it down at levels $\lfloor(N+1)h\rfloor/(N+1)$, using a choice-selected finite model of the rounded function: a measurable label map to a finite ordered set, strictly positive masses of all label fibers, and nondecreasing listed values that agree with the rounded field almost everywhere after applying the label map. Use these masses as weights. The model does not require its listed values to be pairwise distinct or assert independence of this choice. Apply `limUnder atTop` to the real step values in $N$ at fixed $n$, without assuming convergence for arbitrary bounded fields as part of the definition. For every $\varepsilon>0$, eventually in $n$, uniformly over all such $q$, $E(m_q)<\infty$, $2h_q=A_q\circ q$ almost everywhere, and

$$
\left|F_n(h_q)-\left(E(m_q)-\int_0^1h_q(u)q(u)\,du\right)\right|<\varepsilon.
$$

**Conventions.** Use the marked Poisson recursion, normalized sphere measure, reciprocal-tail entropy, and bounded-field step approximation. The source uses extended integration for the angular factors and real values only after conversion from finite masses.

## Depends on

- [Monotone trial CDFs and reciprocal-tail entropy](reciprocal-trial-entropy.md)

## Proof depends on

The finite hierarchy angular/free-energy comparison and a compactness argument for dual minimizers below one, plus uniform estimates transferring the attained finite formula to bounded stationary fields.

## Expansion

Prove leaf sums positive and finite at admissible exponents and identify the weighted angular pressure with the finite recursion. Then isolate dual minimization, compact-uniform convergence, and the stationarity identity with the cutoff $B<1$. A pointwise finite-field limit alone cannot support the uniform stationary-field assertion.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SphericalField.lean#L553-L554)
- [Shifted mark update and leaf coordinate](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SphericalField.lean#L187-L236)
- [Reversed coefficient array and finite field value](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SphericalField.lean#L268-L277)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/222.md)
- [Accompanying manuscript: The free energy of the spherical random perceptron](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/The-free-energy-of-the-spherical-random-perceptron-September-24-2026/The-free-energy-of-the-spherical-random-perceptron-September-24-2026.pdf)
