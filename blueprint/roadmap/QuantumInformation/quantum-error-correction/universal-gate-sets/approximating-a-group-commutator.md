# Approximating a group commutator

Let $V, W, \tilde V, \tilde W$ be unitary matrices with $\|V - \tilde V\| < \Delta$, $\|W - \tilde W\| < \Delta$,
$\|I - V\| < \delta$ and $\|I - W\| < \delta$ (operator norm). Then

$$\big\| V W V^{*} W^{*} - \tilde V \tilde W \tilde V^{*} \tilde W^{*} \big\| \;<\; 8 \Delta \delta + 4 \Delta \delta^2 + 8 \Delta^2 + 4 \Delta^3 + \Delta^4 .$$

When $\Delta = \varepsilon$ and $\delta = O(\sqrt{\varepsilon})$ the right side is $O(\varepsilon^{3/2})$: approximating
$V$ and $W$ to accuracy $\varepsilon$ approximates their group commutator to accuracy $O(\varepsilon^{3/2})$. This is the
step of the Solovay–Kitaev algorithm that improves the accuracy at each level of recursion.

Proof: write $\tilde V = V + \Delta_V$, $\tilde W = W + \Delta_W$ and expand; the terms of second, third and fourth order in
$\Delta$ contribute at most $6\Delta^2 + 4\Delta^3 + \Delta^4$, and the first-order terms pair up, using
$\Delta_V V^{*} + V \Delta_V^{*} = -\Delta_V \Delta_V^{*}$ (unitarity of $V$ and $\tilde V$) and
$W = I + \delta_W$, into two terms each bounded by $\Delta^2 + 4\Delta\delta + 2\Delta\delta^2$.

## Sources

- C. M. Dawson and M. A. Nielsen, *The Solovay–Kitaev algorithm*, Quantum Inf. Comput. 6 (2006), 81–95, arXiv:quant-ph/0505030, Section 4.2, Lemma 1 and equations (14)–(20).
