# Classical and entangled values of the CHSH game

In the CHSH game the questions $x, y \in \{0, 1\}$ are uniform and independent, the answers are bits $a, b$, and the players win
when $a \oplus b = x \wedge y$. Its classical value is $3/4$, and its entangled value is $\cos^2(\pi/8) = (2 + \sqrt 2)/4$: sharing
$(\lvert 00 \rangle + \lvert 11 \rangle)/\sqrt 2$ and measuring in real bases at angles $0$ and $\pi/4$ (Alice) and $\pi/8$ and $-\pi/8$ (Bob)
wins with probability $\cos^2(\pi/8)$, and no entangled strategy in any finite dimension does better (Tsirelson).

## Proof

Classical value: a deterministic strategy $(a_0, a_1, b_0, b_1)$ would win on all four question pairs only if
$a_0 \oplus b_0 = a_0 \oplus b_1 = a_1 \oplus b_0 = 0$ and $a_1 \oplus b_1 = 1$, whose sum modulo $2$ gives $0 = 1$; so it wins at most
$3$ of the $4$ pairs, and $a = b = 0$ wins exactly $3$. Entangled strategy: for the state and angles given, the answers agree with
probability $\cos^2(\theta_x - \phi_y)$, and $\lvert \theta_x - \phi_y \rvert = \pi/8$ on the three pairs that need agreement and
$3\pi/8$ on the pair that needs disagreement, so each pair is won with probability $\cos^2(\pi/8)$. Upper bound: with $\pm 1$
observables the winning probability is $1/2 + \frac18 \langle A_0 B_0 + A_0 B_1 + A_1 B_0 - A_1 B_1 \rangle$, and Tsirelson's inequality
bounds the expectation by $2\sqrt 2$.

## Expansion

A good expansion adds a page for each pending prerequisite below.

- Proof prerequisite: Tsirelson's inequality: for Hermitian $\pm 1$ observables $A_0, A_1$ and $B_0, B_1$ with each $A_i$ commuting with each $B_j$, every state has CHSH expectation at most $2\sqrt 2$.

## Depends on

- [Two-player nonlocal games: classical and entangled values](two-player-nonlocal-games-classical-and-entangled-values.md)

## Related topics

- [Tsirelson's bound is attained](tsirelson-bound-tight.md)

## Sources

- R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415v6, Section 17.2 (CHSH: classical value 3/4, the quantum strategy, and Tsirelson's bound). <https://arxiv.org/abs/1907.09415v6>
- B. S. Tsirelson, *Quantum generalizations of Bell's inequality*, Lett. Math. Phys. 4 (1980), 93–100.
