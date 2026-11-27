# Bootstrapping win-win: recursive hitting sets over lengths n_{i+1} = n_i^β

Let $Q$ be dense and easy. Fix an initial length $n_0$, a constant $\beta>1$, lengths $n_{i+1}=n_i^{\beta}$ and $t=O(\log n_0)$. Put $H_0=\{0,1\}^{n_0}$ and let $\mathrm{BF}_i(1^{n_i})$ output the first element of $H_i$ in $Q_{n_i}$. Let $H_{i+1}\subseteq\{0,1\}^{n_{i+1}}$ be the improved Chen–Tell hitting set for $f=\mathrm{BF}_i$ and $M=n_{i+1}$. If $T_i$ is the time to print $H_i$, then $T_0\le 2^{\alpha n_0}$ and $T_{i+1}\le T_i^{\alpha}$ for a constant $\alpha \ge 1$, giving $\log T_i \le \alpha^{i+1} n_0$, and with $\beta=2\alpha$,

$$
\frac{\log T_t}{\log n_t}\le\frac{\alpha\, n_0}{2^{t}\log n_0}.
$$

Hence for $t\approx\log(n_0/\log n_0)$ the ratio is $O(1)$, so $H_t$ is printable in time $\mathrm{poly}(n_t)$, and there is an index $i\le t$ at which a polynomial-time pseudodeterministic algorithm outputs a canonical element of $Q_{n_i}$ (in the formal proof of Theorem 1.1, Section 3, Chen et al. set $T_0 = 2^{2n_0}$, $\log T_i \le \lambda^i \cdot 2n_0$ with $\lambda = c(\tau+1)\kappa$, $\beta \ge 100\lambda$, and $t \le \log n_0$).

## Proof sketch

The growth bound is an induction: $T_i\le 2^{\alpha^{i+1}n_0}$ while $n_i=n_0^{(2\alpha)^{i}}$, so $\log T_t / \log n_t \le \alpha^{t+1} n_0 / ((2\alpha)^t \log n_0) = \alpha\, n_0 / (2^t \log n_0)$. If $H_t$ hits $Q_{n_t}$, scanning it is polynomial time at length $n_t$. Otherwise, since $H_0$ hits $Q_{n_0}$, some $i<t$ has $H_i$ hitting $Q_{n_i}$ while $Q_{n_{i+1}}$ avoids $H_{i+1}$; then the reconstruction, with $Q_{n_{i+1}}$ as the distinguisher, computes $\mathrm{BF}_i(1^{n_i})$, a canonical element, in time $\mathrm{poly}(d_i,n_i)=\mathrm{poly}(n_i)$.

## Depends on

- [Chen–Lu–Oliveira–Ren–Santhanam: Chen–Tell hitting sets with a Shaltiel–Umans core are printable in time poly(T)](improved-chen-tell-hsg-shaltiel-umans.md)
- [Pseudodeterministic constructions for dense properties, everywhere and infinitely often](pseudodeterministic-construction-of-dense-property.md)

## Sources

- Lijie Chen, Zhenjian Lu, Igor C. Oliveira, Hanlin Ren and Rahul Santhanam, "Polynomial-Time Pseudodeterministic Construction of Primes", FOCS (2023), arXiv:2305.15140.
