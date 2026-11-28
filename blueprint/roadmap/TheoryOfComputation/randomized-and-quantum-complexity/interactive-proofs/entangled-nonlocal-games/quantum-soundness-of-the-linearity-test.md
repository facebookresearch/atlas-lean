# Quantum soundness of the two-player linearity test

In the two-player linearity test of Natarajan and Vidick (Figure 1) over $\mathbb{F}_2^n$, the referee labels one of the two players, chosen at random, Alice and the other Bob. He sends Alice a uniformly random pair $(a, b)$ and Bob the pair $(c, c')$, where $c$ is $a$, $b$ or $a + b$ with probability $1/3$ each and $c'$ is uniform; each pair is sent in lexicographic order, so Bob cannot tell which of his strings is checked. Alice answers $\alpha, \beta \in \{\pm 1\}$ for $a$ and $b$, and Bob answers $\gamma, \gamma' \in \{\pm 1\}$ for his two strings, $\gamma$ being his answer for $c$. If $c = a$ (resp. $c = b$) the referee accepts iff $\gamma = \alpha$ (resp. $\gamma = \beta$); if $c = a + b$ he accepts iff $\gamma = \alpha\beta$. Suppose a strategy with shared state $\psi$ and projective measurements $\{M^{\alpha,\beta}_{a,b}\}$ for Alice passes with probability at least $1 - \varepsilon$. Let $\tilde M^{\alpha}_a = \mathbb{E}_b \sum_\beta M^{\alpha,\beta}_{a,b}$, let $\{A^{\alpha}_a\}_{\alpha = \pm 1}$ be the projective measurement on Alice's space extended by an ancilla obtained from $\{\tilde M^\alpha_a\}_\alpha$ by Naimark dilation, with $\psi'$ the state $\psi$ tensored with the ancilla, and let $A(a) = A^{+1}_a - A^{-1}_a$. Then $\mathbb{E}_{a,b}\langle \psi', A(a)A(b)A(a+b)\psi'\rangle = 1 - O(\sqrt{\varepsilon})$ (Theorem 11), and after a further ancilla there are observables $\tilde A(a)$ with $\tilde A(a)\tilde A(b) = \tilde A(a+b)$ for all $a, b \in \mathbb{F}_2^n$ and $\mathbb{E}_a \|(A(a) - \tilde A(a))\psi''\|^2 = O(\sqrt{\varepsilon})$, with $\psi''$ the extended state (Theorem 10).

## Proof sketch

Consistency with Bob, who cannot tell which of his strings is checked, makes Alice's observables on $a$, $b$, and $a+b$ approximately commute and satisfy $\mathbb{E}_{a,b}\langle \psi', A(a)A(b)A(a+b)\psi'\rangle = 1 - O(\sqrt{\varepsilon})$ (Theorem 11); applying the Gowers–Hatami stability theorem for approximate representations of $\mathbb{F}_2^n$ rounds $A$ to an exact representation $\tilde A$ at averaged squared state-dependent distance $O(\sqrt{\varepsilon})$ (Theorem 10).

## Depends on

- [Entangled strategies and the entangled value of a game](entangled-strategies-and-entangled-value.md)
- [Blum–Luby–Rubinfeld linearity test](../../../pcp-and-inapproximability/blum-luby-rubinfeld-linearity-test/blr-test.md)

## Sources

- A. Natarajan and T. Vidick, "A Quantum Linearity Test for Robustly Verifying Entanglement", STOC 2017 (arXiv:1610.03574), Figure 1 and Theorems 10 and 11.
