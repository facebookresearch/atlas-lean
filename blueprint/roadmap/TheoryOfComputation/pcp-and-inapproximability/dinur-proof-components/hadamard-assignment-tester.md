# The Hadamard assignment tester has constant queries and rejection rate

For every finite label set $\alpha$ and every binary constraint $C \subseteq \alpha \times \alpha$ there is a local test on proofs consisting of two tables $A, B : \{0,1\}^\alpha \to \{0,1\}$ (supposed long codes of labels $a, b \in \alpha$) and auxiliary Hadamard tables, with a number of queries and an alphabet independent of $\alpha$, such that: (completeness) if $(a, b) \in C$ the long codes of $a, b$ with honest auxiliary tables pass with probability $1$; (soundness) for every proof, the rejection probability is at least $\varepsilon_0 \cdot \delta$, where $\delta$ is the relative distance of $(A, B)$ from the pairs of long codes of satisfying label pairs and $\varepsilon_0 > 0$ is an absolute constant. Long codes of distinct labels are at relative distance $1/2$, so a table within distance $1/4$ of a long code determines the label.

## Proof sketch

Encode the constraint by a system of quadratic equations over $\mathbb{F}_2$ in the one-hot vectors of $a$ and $b$ (their long codes are the Hadamard encodings of these unit vectors) and run the Hadamard quadratic-equation tester, sharing the two vertex tables. Selecting one of the checks uniformly loses only a constant factor in the rejection probability.

## Depends on

- [Assignment testers](../pcp-constructions/assignment-testers.md)
- [Long code and folded tables](../long-code-and-hastad-tests/long-code-and-folded-tables.md)

## Proof depends on

- [Hadamard tester for systems of quadratic equations](hadamard-tester-for-quadratic-equations.md)

## Sources

- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
- I. Dinur, "The PCP Theorem by Gap Amplification", Journal of the ACM 54(3), 2007.
