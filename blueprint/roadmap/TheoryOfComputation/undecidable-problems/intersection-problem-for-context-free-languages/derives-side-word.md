# The construction of derivations

Let $P$ be a list of dominoes, $\sigma$ a map assigning a
word over $\alpha$ to each domino, and $G$ the context-free grammar of the side grammar of $P$ for
$\sigma$, with start nonterminal $S$ and terminals $\alpha \oplus \mathbb{N}$ (letters and
indices). For every nonempty sequence $i_1, \dots, i_n$ of indices, each less than the length of
$P$, and all words $u, v$ over $\alpha \oplus \mathbb{N}$, $G$ derives the terminal word
$u\, w_{i_1} \cdots w_{i_n}\, i_n \cdots i_1\, v$ from the sentential form $u\, S\, v$, where
$w_i$ is $\sigma$ applied to the $i$-th domino of $P$.
