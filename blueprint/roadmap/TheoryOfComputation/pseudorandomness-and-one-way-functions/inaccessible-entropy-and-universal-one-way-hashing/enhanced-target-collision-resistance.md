# Enhanced target collision resistance

A keyed hash family $H$ is *enhanced target collision resistant* if every probabilistic polynomial-time two-stage adversary wins the following game with negligible probability: in stage one, given $1^n$, it commits to a message $m_0$; it then receives a uniform key $k$ and in stage two outputs a pair $(k', m') \ne (k, m_0)$ with $H_{k'}(m') = H_k(m_0)$. It may change the key, the message, or both. Enhanced target collision resistance implies target collision resistance.

## Depends on

- [Collision resistance and target collision resistance](../../../ComputerScience/cryptography/hash-functions/collision-resistance-and-target-collision-resistance.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
