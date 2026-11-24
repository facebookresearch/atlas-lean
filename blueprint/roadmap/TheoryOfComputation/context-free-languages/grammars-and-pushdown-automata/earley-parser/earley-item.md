# Earley item

Let $T$ be a set of terminals and $N$ a set of nonterminals. An Earley item consists of a production
$A \to \gamma$ over $T$ and $N$, a dot position $k \in \mathbb{N}$ (the number of symbols of $\gamma$ recognized so
far), a word $p$ over $T$ (the input consumed before the origin of the item) and a word $c$ over $T$ (the input
consumed by the first $k$ symbols of $\gamma$). The intended reading is that the whole input is $pcu$ for
some word $u$.
