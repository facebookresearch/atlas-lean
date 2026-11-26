# Balanced group commutators in $SU(2)$

There are constants $c_{gc} > 0$ and $\varepsilon_1 > 0$ such that every $U \in SU(2)$ with $\| I - U \| < \varepsilon$,
$\varepsilon \le \varepsilon_1$, is a group commutator

$$U = V W V^{*} W^{*}, \qquad V, W \in SU(2), \qquad \| I - V \|, \| I - W \| < c_{gc} \sqrt{\varepsilon}$$

(operator norm). Dawson and Nielsen take $V$ and $W$ to be rotations of the Bloch sphere by the same angle $\varphi$ about
the $x$ and $y$ axes, whose commutator is a rotation by an angle $\theta$ with
$\sin(\theta/2) = 2 \sin^2(\varphi/2) \sqrt{1 - \sin^4(\varphi/2)}$; a rotation $U$ by $\theta$ about any axis is conjugate
by some $S \in SU(2)$ to that commutator, so $U = (S V S^{*})(S W S^{*})(S V S^{*})^{*}(S W S^{*})^{*}$. Since a rotation
by $\tau$ is at distance $2 \sin(\tau/4)$ from $I$, $\| I - U \| \approx 2 \| I - V \|^2$, giving $c_{gc} \approx 1/\sqrt{2}$.

## Sources

- C. M. Dawson and M. A. Nielsen, *The Solovay–Kitaev algorithm*, Quantum Inf. Comput. 6 (2006), 81–95, arXiv:quant-ph/0505030, Section 4.1, equations (10)–(13) ("This is the desired balanced group commutator, and gives $c_{gc} \approx 1/\sqrt{2}$").
