# Quantum soundness of the two-player linearity test

In the two-player linearity test of Natarajan and Vidick (Figure 1) over $\mathbb{F}_2^n$, the referee sends Alice a pair of uniformly random points $(a, b)$ and Bob a question $c \in \{a, b, a + b\}$ together with a uniformly random dummy string $c'$, expects Alice's answers $(x_a, x_b)$ and Bob's answer $y$, and checks consistency with $x_a$, $x_b$, or $x_a \oplus x_b$. If a strategy passes with probability at least $1 - \varepsilon$, then Alice's observables $A(a) = A^0_a - A^1_a$, after Naimark dilation to a state $\psi'$, satisfy $\mathbb{E}_{a,b}\langle \psi', A(a)A(b)A(a+b)\psi'\rangle = 1 - O(\sqrt{\varepsilon})$, and there are observables $\tilde A(a)$ with $\tilde A(a)\tilde A(b) = \tilde A(a+b)$ for all $a, b \in \mathbb{F}_2^n$ and $\mathbb{E}_a \|(A(a) - \tilde A(a))\psi'\|^2 = O(\sqrt{\varepsilon})$ (Natarajan and Vidick, Theorems 10 and 11).

## Proof sketch

Consistency with Bob makes Alice's observables on $a$, $b$, and $a+b$ approximately commute and satisfy $\mathbb{E}_{a,b}\langle \psi', A(a)A(b)A(a+b)\psi'\rangle = 1 - O(\sqrt{\varepsilon})$ (Theorem 11); applying the Gowers–Hatami stability theorem for approximate representations of $\mathbb{F}_2^n$ rounds $A$ to an exact representation $\tilde A$ at averaged squared state-dependent distance $O(\sqrt{\varepsilon})$ (Theorem 10).

## Depends on

- [Entangled strategies and the entangled value of a game](entangled-strategies-and-entangled-value.md)
- [Blum–Luby–Rubinfeld linearity test](../../../pcp-and-inapproximability/blum-luby-rubinfeld-linearity-test/blr-test.md)

## Sources

- A. Natarajan and T. Vidick, "A Quantum Linearity Test for Robustly Verifying Entanglement", STOC 2017 (arXiv:1610.03574), Figure 1 and Theorems 10 and 11.
