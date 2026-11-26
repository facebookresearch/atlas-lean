# Kaibel–Weltge: unique disjointness needs (3/2)^n rectangles

For every finite set $\alpha$ with $|\alpha| = n$, every $1$-cover of unique disjointness by rectangles (each containing no pair with $|S \cap T| = 1$) has at least $(3/2)^n$ rectangles:

$$3^n \le 2^n \cdot C^1(\mathrm{UDISJ}_\alpha).$$

Hence $N^1(\mathrm{UDISJ}_\alpha) \ge \lceil \log_2 \lceil (3/2)^n \rceil \rceil$, and the correlation polytope has extension complexity at least $(3/2)^n$.

## Proof sketch

There are $3^n$ disjoint pairs. A rectangle $A \times B$ avoiding uniquely intersecting pairs contains at most $2^n$ disjoint pairs: the disjoint pairs in it form a "valid" set on which a counting argument over coordinates (each coordinate contributes a factor at most $2$ instead of $3$) bounds the size.

## Depends on

- [Unique disjointness](unique-disjointness.md)
- [Rectangle covers and nondeterministic communication complexity](rectangle-covers-and-nondeterministic-complexity.md)

## Sources

- V. Kaibel and S. Weltge, "A Short Proof that the Extension Complexity of the Correlation Polytope Grows Exponentially", Discrete & Computational Geometry 53(2), 2015.
