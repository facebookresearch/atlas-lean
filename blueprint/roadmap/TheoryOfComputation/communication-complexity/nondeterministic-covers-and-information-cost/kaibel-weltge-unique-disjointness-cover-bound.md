# Kaibel–Weltge: unique disjointness needs (3/2)^n rectangles

For every finite set $\alpha$ with $|\alpha| = n$, every $1$-cover of unique disjointness by rectangles (each containing no pair with $|S \cap T| = 1$; pairs with $|S \cap T| \ge 2$ are allowed) has at least $(3/2)^n$ rectangles:

$$3^n \le 2^n \cdot C^1(\mathrm{UDISJ}_\alpha).$$

Hence $N^1(\mathrm{UDISJ}_\alpha) \ge \lceil \log_2 \lceil (3/2)^n \rceil \rceil$. For $n \ge 1$, this count is the combinatorial core of the extension-complexity bound $\mathrm{xc}(\mathrm{COR}(n)) \ge (3/2)^n$ for the correlation polytope: the slack of the inequality indexed by $a$ at the vertex $bb^{\mathsf T}$ is $(1 - |a \cap b|)^2$, whose support is exactly the set of pairs with $|a \cap b| \ne 1$, and Yannakakis's factorization theorem converts a cover bound for that support into an extension-complexity bound. That consequence is recorded on [Kaibel-Weltge: the correlation polytope has extension complexity at least (3/2)^n](../../../ComputerScience/approximation-algorithms/extended-formulations-and-extension-complexity/correlation-polytope-lower-bound.md).

## Proof sketch

There are $3^n$ disjoint pairs. A rectangle $A \times B$ avoiding uniquely intersecting pairs contains at most $2^n$ disjoint pairs: the disjoint pairs in it form a *valid* set $R$ (no $(a, b), (a', b') \in R$ with $|a \cap b'| = 1$), and valid sets have at most $2^n$ members by induction on $n$. Split $R$ into the pairs that contain the last element $n$ in $a$ or cannot have $n$ added to $a$ within $R$, and symmetrically for $b$; deleting $n$ maps each part injectively onto a valid set over $n - 1$ elements, and every pair of $R$ lies in one of the parts, since $(a \cup \{n\}, b)$ and $(a, b \cup \{n\})$ cannot both lie in $R$ (they would meet in exactly $\{n\}$).

## Depends on

- [Unique disjointness](unique-disjointness.md)
- [Rectangle covers and nondeterministic communication complexity](rectangle-covers-and-nondeterministic-complexity.md)
- [The correlation polytope](../../../ComputerScience/approximation-algorithms/extended-formulations-and-extension-complexity/correlation-polytope.md)

## Proof depends on

- [Yannakakis' factorization theorem](../../../ComputerScience/approximation-algorithms/extended-formulations-and-extension-complexity/yannakakis-factorization-theorem.md)

## Sources

- V. Kaibel and S. Weltge, "A Short Proof that the Extension Complexity of the Correlation Polytope Grows Exponentially", Discrete & Computational Geometry 53(2), 2015.
