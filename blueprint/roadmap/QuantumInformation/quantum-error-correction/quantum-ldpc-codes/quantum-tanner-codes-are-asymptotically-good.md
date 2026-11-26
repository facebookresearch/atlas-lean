# Quantum Tanner codes are asymptotically good

There are infinite families of [quantum LDPC codes](quantum-ldpc-code.md) with rate bounded below and minimum distance
linear in the length. Leverrier and Zémor's *quantum Tanner codes* place qubits on the squares of a left-right Cayley
complex built from a group $G$ and two generating sets $A, B$ of size $\Delta$, and impose local constraints from classical
codes $C_A \subseteq \mathbb{F}_2^{A}$ and $C_B \subseteq \mathbb{F}_2^{B}$ on the squares around each vertex. For
$\rho \in (0, 1/2)$, $\varepsilon \in (0, 1/2)$ and $\delta > 0$ with $-\delta \log_2 \delta - (1-\delta)\log_2(1-\delta) < \rho$,
random choices of $C_A$ and $C_B$ of rates $\rho$ and $1 - \rho$ give, with positive probability for $\Delta$ large enough,
codes of rate $(2\rho - 1)^2$ and minimum distance at least
$\delta n / (4 \Delta^{3/2 + \varepsilon})$. Panteleev and Kalachev first proved that asymptotically good quantum LDPC
codes exist, with lifted product codes.

## Expansion

A sound expansion adds pages for: left-right Cayley complexes and their expansion from Ramanujan-type Cayley graphs; the
quantum Tanner code construction and its CSS conditions; the robustness of dual tensor codes (Leverrier and Zémor,
Theorem 9) for random $C_A$, $C_B$; and the expansion argument of their Theorem 1 that a low-weight codeword can be reduced
by a nearby codeword of the complementary code.

## Depends on

- [Quantum LDPC code](quantum-ldpc-code.md)

## Sources

- A. Leverrier and G. Zémor, *Quantum Tanner codes*, Proceedings of FOCS 2022, 872–883, arXiv:2202.13641, Section 1, Theorems 1 and 2, and Theorems 17 and 18.
- P. Panteleev and G. Kalachev, *Asymptotically good quantum and locally testable classical LDPC codes*, Proceedings of STOC 2022, 375–388, arXiv:2111.03654, Theorem 2 ("an explicit family of quantum LDPC codes ... with the parameters $[[n, k > Rn, d = \Theta(n)]]$").
