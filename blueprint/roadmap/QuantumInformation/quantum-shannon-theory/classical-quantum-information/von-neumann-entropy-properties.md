# Basic properties of von Neumann entropy: bounds, additivity, subadditivity and Araki-Lieb

For density matrices on finite-dimensional spaces:

1. $0 \le S(\rho)\le\log_2 d$ on $\mathbb{C}^d$, with $S = 0$ on pure states and $S(I/d) = \log_2 d$;
2. $S(V\rho V^*) = S(\rho)$ for every isometry $V$, and $S(\rho\otimes\sigma) = S(\rho)+S(\sigma)$;
3. for a pure bipartite state $|\psi\rangle\langle\psi|$ the two reduced states have equal entropy;
4. (subadditivity) $S(\rho_{AB})\le S(\rho_A) + S(\rho_B)$;
5. (Araki-Lieb) $S(\rho_B) - S(\rho_A)\le S(\rho_{AB})$.

## Proof sketch

Parts 1-2 follow from the eigenvalue formula; part 3 from the Schmidt decomposition, which gives the two reductions the same nonzero spectrum. Subadditivity is $(\ln 2)^{-1} I(A:B) \ge 0$, since $D(\rho_{AB}\|\rho_A\otimes\rho_B) = (\ln 2)(S(\rho_A)+S(\rho_B)-S(\rho_{AB}))$ and relative entropy is nonnegative. Araki-Lieb follows by applying subadditivity to a purification $\rho_{ABC}$ and using part 3 to trade $S(\rho_{AC})$ for $S(\rho_B)$ and $S(\rho_C)$ for $S(\rho_{AB})$.

## Depends on

- [Von Neumann entropy and Holevo information](von-neumann-entropy-and-holevo-information.md)
- [Density matrices, pure states and reduced states](../../quantum-states-distances-and-entropy/density-matrices-and-fidelity/density-matrices-and-reduced-states.md)

## Proof depends on

- [Nonnegativity of quantum relative entropy for singular states (Klein's inequality)](../../quantum-states-distances-and-entropy/quantum-relative-entropy/relative-entropy-nonnegativity.md)
- [Quantum mutual information](quantum-mutual-information.md)
- [Schmidt decomposition](../../quantum-foundations/schmidt-decomposition.md)
- [Purification and unitary equivalence of purifications](../../quantum-foundations/purification-and-unitary-equivalence-of-purifications.md)

## Sources

- J. Watrous, "The Theory of Quantum Information", Cambridge University Press, 2018.
- M. A. Nielsen and I. L. Chuang, "Quantum Computation and Quantum Information: 10th Anniversary Edition", Cambridge University Press, 2010.
