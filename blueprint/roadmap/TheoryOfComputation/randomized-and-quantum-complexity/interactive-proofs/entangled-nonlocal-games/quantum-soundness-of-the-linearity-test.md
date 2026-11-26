# Quantum soundness of the two-player linearity test

In the two-player linearity test over $\mathbb{F}_2^n$ the referee sends Alice a pair of points $(u, v)$ and Bob one of $u$, $v$ or $u + v$ (uniform $u, v$), expects Alice's answers $(a_u, a_v)$, accepts if Bob's answer matches the corresponding value $a_u$, $a_v$ or $a_u \oplus a_v$. Let a tensor strategy on a state $\psi$ use projective measurements, with Bob's projector for answer $b \in \{0, 1\}$ on question $w$ written $B^w_b$. If it passes with probability at least $1 - \varepsilon$, then there is a measurement $\{Q_s\}_{s \in \mathbb{F}_2^n}$ on Bob's space such that

$$
\mathop{\mathbb{E}}_{w} \sum_{b \in \{0, 1\}} \Big\| \Big(1 \otimes \big(B^w_b - \textstyle\sum_{s : \langle s, w \rangle = b} Q_s\big)\Big)\psi \Big\|^2 \le C\varepsilon
$$

for an absolute constant $C$, with $w$ uniform in $\mathbb{F}_2^n$: Bob's answers are approximately obtained by measuring $s$ once and answering $\langle s, w \rangle$.

## Proof sketch

Consistency with Bob makes Alice's measurements on $u$, $v$, $u+v$ approximately commute and multiply as characters; averaging the induced unitary representation over the group (a quantum version of BLR via Gowers–Hatami) yields an exact representation close to the strategy.

## Depends on

- [Entangled strategies and the entangled value of a game](entangled-strategies-and-entangled-value.md)
- [Blum–Luby–Rubinfeld linearity test](../../../pcp-and-inapproximability/blum-luby-rubinfeld-linearity-test/blr-test.md)

## Sources

- A. Natarajan and T. Vidick, "A Quantum Linearity Test for Robustly Verifying Entanglement", STOC 2017.
