# State overlap bounds measurement distinguishability

Let $\psi,\varphi\in\mathbb{C}^\iota$ be unit vectors and, for a set $S$ of computational-basis outcomes, let $P_\psi(S) = \sum_{y\in S}|\psi_y|^2$.

If $P_\psi(S)\ge 1-\varepsilon$ and $P_\varphi(S)\le\varepsilon$ with $\varepsilon\le\tfrac12$, then $|\langle\psi,\varphi\rangle|\le 2\sqrt{\varepsilon(1-\varepsilon)}$. The same holds when $\psi$ lands in $S_1$ and $\varphi$ in a disjoint $S_2$ with probability at least $1-\varepsilon$ each, or when a classical readout $\mathrm{out}:\iota\to\beta$ outputs distinct values $b_1\ne b_2$ on the two states with probability at least $1-\varepsilon$.

## Proof sketch

Split the overlap along $S$ and its complement and apply Cauchy-Schwarz to each part: $|\langle\psi,\varphi\rangle|\le\sqrt{pq}+\sqrt{(1-p)(1-q)}$ with $p = P_\psi(S)$, $q = P_\varphi(S)$. This bound is evaluated at the extreme admissible $p,q$; disjoint events and distinct readouts reduce to one event $S$.

The following bound is derived here and is not stated in the cited source: $|\langle\psi,\varphi\rangle|^2 + \big(P_\psi(S) - P_\varphi(S)\big)^2\le 1$, and hence $|P_\psi(S)-P_\varphi(S)|\le\|\psi-\varphi\|$. It follows from the same split, since $(\sqrt{pq}+\sqrt{(1-p)(1-q)})^2 + (p-q)^2\le1$.

## Depends on

- [Positive-operator-valued measurements and the Born rule](povm-and-born-rule.md)

## Sources

- A. Ambainis, "Quantum lower bounds by quantum arguments", Journal of Computer and System Sciences 64:750-767, 2002; arXiv:quant-ph/0002066v1, Lemma 1 and its proof.
