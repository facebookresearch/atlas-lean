# Fooling set

Let $X$ and $Y$ be sets (the inputs of Alice and of Bob). Let $f : X \times Y \to \{0, 1\}$. A finite set $S \subseteq X \times Y$ is a fooling set for $f$ with value $b \in \{0, 1\}$ if $f(x, y) = b$ for all $(x, y) \in S$ and, for any two distinct pairs $(x_1, y_1), (x_2, y_2) \in S$, $f(x_1, y_2) \ne b$ or $f(x_2, y_1) \ne b$. A fooling set with value $1$ is a $1$-fooling set.

## Sources

- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, web draft of 2007-01-08, Definition 12.3.
