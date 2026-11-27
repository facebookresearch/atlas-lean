# Brakerski-Christiano-Mahadev-Vazirani-Vidick: a test of quantumness from LWE

Assuming the quantum hardness of the Learning With Errors problem, there is a two-round interactive protocol between a classical polynomial-time verifier and a prover such that an efficient quantum prover is accepted with probability close to $1$, while every classical probabilistic polynomial-time prover is accepted with probability at most $3/4 + \mathrm{negl}$; moreover, repetition certifies that the quantum prover's outputs contain min-entropy (certifiable randomness from a single device). Unlike the random-oracle separation of Yamakawa and Zhandry, verification here needs a secret trapdoor.

## Proof sketch

The prover prepares $\sum_{b, x}|b\rangle|x\rangle|f_{k,b}(x)\rangle$ and measures the image $y$, leaving $|0\rangle|x_0\rangle + |1\rangle|x_1\rangle$. The verifier asks either for a preimage (checked with the trapdoor) or for a Hadamard-basis measurement $(b', d)$ satisfying $b' = d\cdot(x_0\oplus x_1)$. A classical prover answering both challenges could be rewound to produce a preimage and a correct equation, violating the adaptive hardcore bit property, which holds for the LWE-based construction.

## Depends on

- [Trapdoor claw-free function families](trapdoor-claw-free-function-families.md)

## Sources

- Zvika Brakerski, Paul Christiano, Urmila Mahadev, Umesh Vazirani, Thomas Vidick, "A cryptographic test of quantumness and certifiable randomness from a single quantum device", FOCS (2018), Journal of the ACM 68(5) (2021); arXiv:1804.00640.
