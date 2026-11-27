# Range of a relation

The range of a relation $R$, a set of ordered pairs, is the set of all $y$ for which some $x$ satisfies $(x, y) \in R$. In set theory this is a set: with Kuratowski pairs $(x, y) = \{\{x\}, \{x, y\}\}$, every such $y$ lies in $\bigcup\bigcup R$, so the range is cut out of $\bigcup\bigcup R$ by the subset axiom. Mathlib defines the range for typed relations. For types $\alpha$ and $\beta$, a relation $R$ from $\alpha$ to $\beta$ is a set of pairs $(a, b)$ with $a \in \alpha$ and $b \in \beta$. Its range, which Mathlib calls its codomain, is the subset of $\beta$ consisting of the $b$ for which some $a$ satisfies $(a, b) \in R$. It need not be all of $\beta$, and $R$ need not be total or single-valued. In this typed setting the range is formed by set comprehension within $\beta$, not by the subset axiom of set theory. For a relation $R$ given as a set of ordered pairs, take for $\alpha$ and $\beta$ any sets that contain all first and all second coordinates of $R$, for instance $\bigcup\bigcup R$ for both; the range of $R$ is then the same set, which gives the familiar definition.

## Sources

- Herbert B. Enderton, Elements of Set Theory, Academic Press, 1977.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for relations between two types as sets of pairs: `SetRel`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Basic/Rel.lean#L80-L83.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for membership in the range: `SetRel.mem_cod`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Basic/Rel.lean#L117-L118.
