# Quantum soundness of the two-player linearity test

In the two-player linearity test over $\mathbb{F}_2^n$ the referee sends Alice a pair of points $(u, v)$ and Bob one of $u$, $v$ or $u + v$ (uniform $u, v$), expects Alice's answers $(a_u, a_v)$, accepts if Bob's answer matches the corresponding value $a_u$, $a_v$ or $a_u \oplus a_v$. If a tensor strategy with projective measurements passes with probability at least $1 - \varepsilon$, then there are commuting $\pm 1$ observables $W(s)$ indexed by $s \in \mathbb{F}_2^n$ forming a representation of $\mathbb{F}_2^n$ (so Alice's answers are approximately given by measuring a single projective measurement with outcomes $s$ and answering $\langle s, u \rangle$), with distance $O(\sqrt\varepsilon)$ on the state.

## Proof sketch

Consistency with Bob makes Alice's measurements on $u$, $v$, $u+v$ approximately commute and multiply as characters; averaging the induced unitary representation over the group (a quantum version of BLR via Gowers–Hatami) yields an exact representation close to the strategy.

## Depends on

- [Entangled strategies and the entangled value of a game](entangled-strategies-and-entangled-value.md)
- [Blum–Luby–Rubinfeld linearity test](../../pcp-and-inapproximability/blum-luby-rubinfeld-linearity-test/blr-test.md)

## Sources

- A. Natarajan and T. Vidick, "A Quantum Linearity Test for Robustly Verifying Entanglement", STOC 2017.
