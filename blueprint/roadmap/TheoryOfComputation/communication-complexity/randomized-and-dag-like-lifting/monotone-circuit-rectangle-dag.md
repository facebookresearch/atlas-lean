# Monotone circuits are rectangle-DAGs for monotone Karchmer–Wigderson games

For a monotone Boolean function $f : \{0,1\}^N \to \{0,1\}$, the **monotone Karchmer-Wigderson game** $\mathrm{mKW}_f$ gives Alice $x \in f^{-1}(1)$ and Bob $y \in f^{-1}(0)$ and asks for an index $i$ with $x_i = 1$ and $y_i = 0$. Then the minimum size of a monotone circuit computing $f$ equals, up to a constant factor, the minimum size of a rectangle-DAG for $\mathrm{mKW}_f$; the minimum monotone circuit depth equals the deterministic communication complexity of $\mathrm{mKW}_f$.

## Proof sketch

Given a monotone circuit, label each gate $v$ by the rectangle $\{x : v(x) = 1\} \times \{y : v(y) = 0\}$, which is covered by the rectangles of its two children for both $\wedge$ and $\vee$ gates, and each input gate $x_i$ yields the answer $i$. Conversely, from a rectangle-DAG build a circuit gate by gate from sinks upwards, using monotonicity to replace each rectangle by the monotone function separating its two sides. The depth statement is the Karchmer-Wigderson theorem for the monotone game.

## Depends on

- [Rectangle-DAGs (dag-like communication protocols)](rectangle-dag.md)
- [Deterministic communication complexity](../deterministic-communication-protocols/comm-complexity.md)

## Sources

- A. A. Razborov, "Unprovability of lower bounds on circuit size in certain fragments of bounded arithmetic", Izvestiya Mathematics 59 (1995) 205-227.
- D. Sokolov, "Dag-like communication and its applications", CSR (2017).
- M. Karchmer, A. Wigderson, "Monotone circuits for connectivity require super-logarithmic depth", SIAM Journal on Discrete Mathematics 3 (1990) 255-265.
