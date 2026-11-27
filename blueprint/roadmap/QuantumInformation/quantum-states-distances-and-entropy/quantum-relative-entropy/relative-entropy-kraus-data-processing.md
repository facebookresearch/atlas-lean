# Data processing for quantum relative entropy under Kraus channels

Let $V$ be an isometry from $\mathbb{C}^\iota$ to $\mathbb{C}^{\iota'}$ and let $\{K_j\}_{j\in s}$ be finitely many matrices $\mathbb{C}^\iota\to\mathbb{C}^{\iota'}$ with $\sum_j K_j^*K_j = I$, defining the channel $\Phi(X)=\sum_j K_jXK_j^*$. For positive semidefinite $\rho,\sigma$ on $\mathbb{C}^\iota$:

1. $D(V\rho V^*\,\|\,V\sigma V^*) = D(\rho\,\|\,\sigma)$, including the infinite case;
2. $D(\Phi(\rho)\,\|\,\Phi(\sigma)) \le D(\rho\,\|\,\sigma)$.

## Proof sketch

Isometric conjugation preserves spectra and maps kernels to kernels within the range, so both the support test and the trace formula are unchanged. For a channel, the Stinespring isometry $W\psi = \sum_j K_j\psi\otimes|j\rangle$ satisfies $\Phi(X) = \operatorname{Tr}_2 (WXW^*)$, so part 2 follows from part 1 and monotonicity under partial trace.

## Depends on

- [Support inclusion and Umegaki relative entropy](umegaki-relative-entropy.md)
- [Finite-family Kraus linear map](../../../Analysis/not-yet-classified/kraus/kraus-linear-map.md)

## Proof depends on

- [Monotonicity of quantum relative entropy under partial trace](relative-entropy-partial-trace-monotonicity.md)
- [Stinespring dilation theorem](../../../Analysis/operator-algebras/stinespring-dilation.md)

## Sources

- J. Watrous, "The Theory of Quantum Information", Cambridge University Press, 2018.
- M. A. Nielsen and I. L. Chuang, "Quantum Computation and Quantum Information: 10th Anniversary Edition", Cambridge University Press, 2010.
