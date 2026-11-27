# Brakerski-Christiano-Mahadev-Vazirani-Vidick: a test of quantumness from LWE

Assuming the quantum hardness of the Learning With Errors problem, there is a two-round interactive protocol between a classical polynomial-time verifier and a prover such that an efficient quantum prover is accepted with probability close to $1$, while every classical probabilistic polynomial-time prover is accepted with probability at most $3/4 + \mathrm{negl}$; moreover, repetition certifies that the quantum prover's outputs contain min-entropy (certifiable randomness from a single device). Unlike the random-oracle separation of Yamakawa and Zhandry, verification here needs a secret trapdoor.

## Proof sketch

The protocol uses the noisy trapdoor claw-free family built from LWE. The prover prepares $\sum_{b, x, y}\sqrt{(f'_{k,b}(x))(y)}\,|b\rangle|x\rangle|y\rangle$ (normalized), using the efficiently samplable densities $f'_{k,b}(x)$ close to $f_{k,b}(x)$, and measures an image $y$, leaving up to negligible error $|0\rangle|x_0\rangle + |1\rangle|x_1\rangle$ with $(x_0, x_1) \in R_k$. The verifier asks either for a preimage $(b, x_b)$, checked with the trapdoor (it inverts every point of the support of $f_{k,b}(x)$), or for an equation: the prover applies $J$ to the second register and measures in the Hadamard basis, obtaining $(d, c)$ with $c = d\cdot(J(x_0)\oplus J(x_1))$, which the verifier checks with the trapdoor, together with $d \in G_{k,0,x_0} \cap G_{k,1,x_1}$. A classical prover answering both challenges could be rewound to produce a preimage and a valid equation, that is, a tuple in $H_k$ more often than one in $\overline{H}_k$, violating the adaptive hardcore bit property of the noisy family.

## Depends on

- [Trapdoor claw-free function families](trapdoor-claw-free-function-families.md)

## Sources

- Zvika Brakerski, Paul Christiano, Urmila Mahadev, Umesh Vazirani, Thomas Vidick, "A cryptographic test of quantumness and certifiable randomness from a single quantum device", FOCS (2018), Journal of the ACM 68(5) (2021); arXiv:1804.00640 (Section 1, Figure 1; the honest prover of Protocol 1, Section 5.3).
