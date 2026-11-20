# The Parisi recursion

Let $\xi' \colon \mathbb{R} \to \mathbb{R}$, $k \in \mathbb{N}$ and real sequences $m, q$. Starting from
$f_{k+1}(y) = \log\cosh y$, let $f_\ell$ be the result of one [Parisi step](parisi-step.md) with
variance $\xi'(q_{\ell+1}) - \xi'(q_\ell)$ and parameter $m_\ell$ applied to $f_{\ell+1}$, for
$\ell = k, \dots, 0$ (Talagrand, *The Parisi formula*, Ann. of Math. 163 (2006), (1.9)–(1.10)). The recursion is indexed from the top: its stage
$j$ is $f_{k+1-j}$, for $j = 0, \dots, k + 1$. Beyond $j = k + 1$ the stages are extended by applying
the level-$0$ step again, with variance $\xi'(q_1) - \xi'(q_0)$ and parameter $m_0$; only the stages
$j \le k + 1$ enter the Parisi functional.

In the source, $X_{k+1} = \log\cosh(h + \sum_{p \le k} z_p)$ and
$X_\ell = \frac1{m_\ell}\log\mathbb{E}_\ell\exp(m_\ell X_{\ell+1})$ with independent
$z_p \sim N(0, \xi'(q_{p+1}) - \xi'(q_p))$; since $X_\ell$ depends on $z_0, \dots, z_{\ell-1}$ only
through $h + \sum_{p<\ell} z_p$, $X_\ell = f_\ell(h + \sum_{p < \ell} z_p)$ and $X_0 = f_0(h)$.
