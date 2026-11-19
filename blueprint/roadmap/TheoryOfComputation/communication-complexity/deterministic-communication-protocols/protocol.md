# Deterministic two-party protocol

Let $X$ and $Y$ be sets (the inputs of Alice and of Bob). A deterministic two-party protocol for inputs $x \in X$ (held by Alice) and $y \in Y$ (held by Bob) is a
finite binary tree built from three kinds of nodes: a leaf, labelled by an output bit $b$; an Alice node,
labelled by a map $a : X \to \{0, 1\}$ and having two subprotocols $p_0$ and $p_1$, at which Alice announces
$a(x)$ and the run continues with $p_{a(x)}$; and a Bob node, labelled by a map $g : Y \to \{0, 1\}$ with
subprotocols $p_0, p_1$, at which Bob announces $g(y)$ and the run continues with $p_{g(y)}$.

## Sources

- A. Rao and A. Yehudayoff, *Communication Complexity*, early draft, Chapter 1, "Defining 2 party protocols".
- A. C. Yao, "Some complexity questions related to distributive computing", *Proceedings of the Eleventh Annual ACM Symposium on Theory of Computing (STOC 1979)*, 209–213.
