# Reversal of a segment of a cyclic sequence

For a set $E$, $n \ge 1$, $\rho : E \to E$, positions $\ell, m$ and a sequence $v$ of length $n$, the segment reversal replaces $v_k$, for each position $k$ with $\ell \le k \le m$, by $\rho(v_{\mu(k)})$, where $\mu(k) = \min(\ell + m - k, n - 1)$ is the [mirror position](ons-mir.md), and keeps the other entries.
