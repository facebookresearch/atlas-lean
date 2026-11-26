# The hierarchical cavity formula for diluted Ising pressure

Let $p\ge2$ be an even integer and $\alpha>0$. An interaction has law of $(\theta,a,b,(f_l)_{l<p})$, where $\theta:\{\pm1\}^p\to\mathbb R$, $a,b\in\mathbb R$ and $f_l:\{\pm1\}\to\mathbb R$. Assume $\mathbb E\max_s|\theta(s)|<\infty$, $a>0$ almost surely, and, for every spin tuple almost surely,

$$
e^{\theta(s)}=a\left(1+b\prod_l f_l(s_l)\right),\qquad |b\prod_l f_l(s_l)|<1.
$$

The $f_l$ are IID and their full tuple is independent of $b$; $(-b)^m$ is integrable and has nonnegative mean for every integer $m\ge1$. The site field law has finite absolute first moment. For $N>0$ take $K\sim\operatorname{Poisson}(\alpha N)$, with independent interaction draws and IID fields $h_i$. Use independent uniform indices $i_{jl}\in[N]$, allowing repetitions within each interaction. The pressure is $N^{-1}\mathbb E\log\sum_\sigma\exp(\sum_{j=1}^K\theta_j((\sigma_{i_{jl}})_l)+\sum_i h_i\sigma_i)$.

Here is the variational value. Write $Q_x(s)=e^{xs}/(2\cosh x)$,
$E_\theta(x)=\sum_s e^{\theta(s)}\prod_l Q_{x_l}(s_l)$, and
$M_\theta(x;s)=\log\sum_{s'\in\{\pm1\}^{p-1}}e^{\theta(s',s)}\prod_{l<p-1}Q_{x_l}(s'_l)$.
Let $H_0=\mathbb R$, $H_{j+1}=\mathcal P(H_j)$ with weak topology and its Borel sets. At depth $r$ select $\zeta\in H_{r+1}$ and $0<m_1<\cdots<m_r<1$. Define $\mathcal T(g)$ for a log functional $g$ of a finite array of messages: draw one top-level $H_r$ law independently per message from $\zeta$; holding those laws fixed, recurse down independently, applying the logarithmic conditional power mean $m_j^{-1}\log\mathbb E\exp(m_j g_{\rm next})$ at level $j$ counted from the root, so $m_1$ is the outermost power mean. At depth zero evaluate $g$ on the reals, and average over the top-level draws after all power means. Physical disorder stays fixed inside $\mathcal T$.

For an independent $J\sim\operatorname{Poisson}(p\alpha)$, interactions and site field $h$, put $g_{\rm site}(x)=\log[\tfrac12\sum_{s=\pm1}\exp(hs+\sum_{j=1}^{J}M_{\theta_j}(x_j;s))]$. The pressure converges as $N\to\infty$ to the infimum over all depths and trial data of

$$
\log2+\mathbb E\mathcal T(g_{\rm site})-\alpha(p-1)\mathbb E\mathcal T(\log E_\theta).
$$

**Conventions.** Use Poisson dilution and the finite labelled log partition, the stated factorization and moment class, and nested weak-Borel trial laws with finite conditional power means.

## Depends on

- [Poisson-diluted Ising energy and conditional cavity weights](poisson-diluted-ising-law.md)

## Proof depends on

Matching interpolation upper and cavity lower comparisons for this moment class, together with a limiting argument that does not assume bounded disorder or bounded messages.

## Expansion

Build the hierarchy and prove well-definedness by domination by the integrable interaction maximum and field. Split the upper and lower bounds, isolate where even arity and the signs of the $(-b)^m$ means enter, and verify the depth-zero convention and repeated label choices. Do not assume thermodynamic-limit existence as a premise.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DilutedSpin.lean#L146-L151)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/221.md)
- [Accompanying manuscript: The Mézard–Parisi formula for diluted spin glasses](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/The-Mezard-Parisi-formula-for-diluted-spin-glasses-September-23-2026/paper.pdf)
- [Background: Mézard and Parisi, The Bethe lattice spin glass revisited](https://arxiv.org/abs/cond-mat/0009418)
