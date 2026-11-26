# Aho–Ullman–Yannakakis: tilings give O(log² χ) protocols

If a function $f : X \times Y \to Z$ has a labelled rectangle partition with $t$ rectangles, then it has a deterministic protocol of depth at most $2 \lceil \log_2 t \rceil \lceil \log_2 (t+1) \rceil$. Hence

$$D(f) \le 8 \big(\log_2 \chi(f)\big)^2 + O(1),$$

so deterministic communication complexity and the logarithm of the tiling number are polynomially (quadratically) related.

## Proof sketch

Every rectangle either intersects the rows of a given other rectangle or its columns but not both unless they coincide. In each round the players announce a rectangle consistent with their input that eliminates at least half of the remaining rectangles on their side; after $O(\log t)$ rounds of $O(\log t)$ bits one rectangle remains.

## Depends on

- [Monochromatic rectangle partitions and the tiling number](monochromatic-rectangle-partitions-and-tiling-number.md)
- [Deterministic communication complexity](../deterministic-communication-protocols/comm-complexity.md)

## Sources

- A. V. Aho, J. D. Ullman and M. Yannakakis, "On Notions of Information Transfer in VLSI Circuits", STOC 1983.
- E. Kushilevitz and N. Nisan, "Communication Complexity", Cambridge University Press, 1997.
- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
