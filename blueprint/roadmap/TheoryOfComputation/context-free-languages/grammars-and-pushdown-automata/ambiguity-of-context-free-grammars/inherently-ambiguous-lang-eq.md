# Inherently ambiguous example as a union of two languages

Over the alphabet $\{a, b, c\}$, the language $L = \{a^i b^j c^k : i, j, k \in \mathbb{N},\ i = j \text{ or } j = k\}$
equals

$$\{a^n b^n : n \in \mathbb{N}\} \cdot \{c\}^* \;\cup\; \{a\}^* \cdot \{b^n c^n : n \in \mathbb{N}\},$$

where $\cdot$ is concatenation of languages and ${}^*$ the Kleene star.
