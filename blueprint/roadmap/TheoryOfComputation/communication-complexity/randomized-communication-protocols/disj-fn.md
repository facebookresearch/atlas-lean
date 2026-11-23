# Set intersection function

For $n \in \mathbb{N}$, the set intersection function $\mathrm{DIS}_n : \{0,1\}^n \times \{0,1\}^n \to \{0, 1\}$ takes the
value $1$ at $(x, y)$ if and only if there is a position $i$ with $x_i = y_i = 1$, that is, if the subsets of
$\{1, \dots, n\}$ with characteristic vectors $x$ and $y$ intersect. Its negation is set disjointness.

## Sources

- N. Alon, Y. Matias and M. Szegedy, "The space complexity of approximating the frequency moments", *Journal of Computer and System Sciences* 58 (1999), 137–147, Section 3 (the function $\mathrm{DIS}_n$).
