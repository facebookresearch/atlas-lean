# Composed functions, gadgets and lifting theorems

Let $f : \{0,1\}^n \to \{0,1\}$ (or a search problem $S \subseteq \{0,1\}^n \times \mathcal{O}$) and let $g : \mathcal{X} \times \mathcal{Y} \to \{0,1\}$ be a two-party **gadget**. The **composed function** $f \circ g^n : \mathcal{X}^n \times \mathcal{Y}^n \to \{0,1\}$ is

$$
(f \circ g^n)(x, y) = f\bigl(g(x_1, y_1), \dots, g(x_n, y_n)\bigr),
$$

with Alice holding $x$ and Bob holding $y$. A **lifting theorem** for a query measure $M$ and communication measure $M^{cc}$ states $M^{cc}(f \circ g^n) = \Theta\bigl(M(f) \cdot M^{cc}(g)\bigr)$, or at least $\Omega\bigl(M(f) \log |\mathcal{X}|\bigr)$, for all $f$. The **index gadget** $\mathrm{IND}_m : [m] \times \{0,1\}^m \to \{0,1\}$ is $\mathrm{IND}_m(a, b) = b_a$.

## Depends on

- [Deterministic communication complexity](../deterministic-communication-protocols/comm-complexity.md)
- [Decision-tree depth and degree of a Boolean function](../query-and-communication-measures/decision-tree-depth-and-degree-of-a-boolean.md)

## Sources

- M. Göös, T. Pitassi, T. Watson, "Query-to-communication lifting for BPP", FOCS (2017); SIAM Journal on Computing 49 (2020), arXiv:1703.07666.
- M. Göös, S. Lovett, R. Meka, T. Watson, D. Zuckerman, "Rectangles are nonnegative juntas", STOC (2015); SIAM Journal on Computing 45 (2016) 1835-1869.
