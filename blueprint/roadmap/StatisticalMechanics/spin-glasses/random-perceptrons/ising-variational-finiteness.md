# Finiteness of the Ising perceptron variational value

Let $\alpha\ge0$ and $f:\mathbb R\to\mathbb R$ be bounded and continuous. For Gaussian $Z\sim N(0,1)$ define $T_{s,d}U(x)=d^{-1}\log\mathbb E e^{dU(x+\sqrt s Z)}$ for $d>0$, and $T_{s,0}U(x)=\mathbb E U(x+\sqrt s Z)$. For an almost-everywhere class $q$ with a nondecreasing representative $(0,1)\to[0,1]$, divide $(0,1)$ into $k$ equal open cells. Put $v_i=k\int_{i/k}^{(i+1)/k}q$ for $0\le i<k$ and append $v_k=1$, $v_{-1}=0$. The pattern functional $P(f,q)$ is the limit along the size filter (with the native totalized fallback when no limit exists) of the composition of $T_{v_i-v_{i-1},i/k}$ for $i=0,\ldots,k$, with $i=0$ outermost, applied to $f$ and evaluated at zero.

For each finite partition $0=t_0<\cdots<t_m=1$ ($m\ge1$) and ordered nonnegative $h_0\le\cdots\le h_{m-1}$, let $L(h)$ be the value at zero of $T_{h_0,0}\circ T_{h_1-h_0,t_1}\circ\cdots\circ T_{h_{m-1}-h_{m-2},t_{m-1}}$ applied to $\log\cosh x-h_{m-1}/2$. Write $h(u)=h_i$ on the corresponding open cell and zero at its cuts. Let $S(q)=\sup_h[L(h)+\tfrac12\int_0^1h(u)q(u)\,du]$ in the extended reals. Then $\inf_q[\alpha P(f,q)+S(q)]$ is a finite real number. This does not assert convergence of the finite-volume pressure.

**Conventions.** Use Gaussian power transforms, the quantile-cell pattern approximation (indexed by $k=n+1$ and using the source's filter-limit convention), and the field-step supremum in the extended reals.

## Depends on

- [Ising perceptron overlap paths and field steps](ising-overlap-path-and-field-steps.md)

## Proof depends on

Uniform bounds on the pattern transforms and a trial path with finite entropy supremum, plus a lower bound for all paths. Bounding each individual field test without a common upper bound does not show finiteness of its supremum.

## Expansion

Verify the reduction from the measurable almost-everywhere path class to cell averages. Isolate the uniform boundedness of the Gaussian transforms and the explicit finite-entropy trial calculation; do not import the stronger random-pressure theorem as a prerequisite.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/IsingFiniteness.lean#L86-L90)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/222.md)
- [Accompanying manuscript: The free energy of the Ising random perceptron](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/The-free-energy-of-the-Ising-random-perceptron-September-24-2026/The-free-energy-of-the-Ising-random-perceptron-September-24-2026.pdf)
