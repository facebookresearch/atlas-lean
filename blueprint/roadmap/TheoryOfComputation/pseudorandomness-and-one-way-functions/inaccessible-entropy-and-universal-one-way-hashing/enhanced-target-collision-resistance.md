# Enhanced target collision resistance

A keyed hash family $H$ is *enhanced target collision resistant* if every probabilistic polynomial-time two-stage adversary wins the following game with negligible probability: in stage one, given $1^n$, it commits to a message $m_0$; it then receives a uniform key $k$ and in stage two outputs a pair $(k', m') \ne (k, m_0)$ with $H_{k'}(m') = H_k(m_0)$. It may change the key, the message, or both. Enhanced target collision resistance implies target collision resistance.

## Depends on

- [Collision resistance and target collision resistance](../../../ComputerScience/cryptography/hash-functions/collision-resistance-and-target-collision-resistance.md)

## Sources

- S. Halevi and H. Krawczyk, "Strengthening Digital Signatures via Randomized Hashing", Advances in Cryptology – CRYPTO 2006, Lecture Notes in Computer Science, Springer, 2006, pp. 41–59.
