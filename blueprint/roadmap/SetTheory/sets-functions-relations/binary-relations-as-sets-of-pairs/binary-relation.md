# Binary relation as a set of ordered pairs

A binary relation on a set $X$ is a subset $R$ of $X \times X$, and one writes $x \mathrel{R} y$ for $(x, y) \in R$. Mathlib defines relations between two types as sets of pairs. For types $\alpha$ and $\beta$, a relation from $\alpha$ to $\beta$ is a set of pairs $(a, b)$ with $a \in \alpha$ and $b \in \beta$, and Mathlib writes $a \sim[R] b$ for $(a, b) \in R$. No property such as reflexivity, symmetry or transitivity is imposed. The pairs are those of Lean's product type $\alpha \times \beta$, not the Kuratowski pairs $\{\{a\}, \{a, b\}\}$ of set theory; the two descriptions of a relation correspond to each other, but not by definition. Taking $\alpha = \beta$ to be the type of elements of $X$ gives the familiar definition.

## Sources

- Herbert B. Enderton, Elements of Set Theory, Academic Press, 1977.
