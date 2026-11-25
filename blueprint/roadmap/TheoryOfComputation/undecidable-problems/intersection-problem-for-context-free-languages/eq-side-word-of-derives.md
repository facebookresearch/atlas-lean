# The analysis of derivations

Let $P$ be a list of dominoes, $\sigma$ a map assigning a word
over $\alpha$ to each domino, and $G$ the context-free grammar of the side grammar of $P$ for
$\sigma$, with start nonterminal $S$ and terminals $\alpha \oplus \mathbb{N}$ (letters and
indices). Let $u, v, x$ be words over $\alpha \oplus \mathbb{N}$. If $G$ derives the terminal word
$x$ from the sentential form $u\, S\, v$, then there is a nonempty sequence $i_1, \dots, i_n$ of
indices, each less than the length of $P$, such that
$x = u\, w_{i_1} \cdots w_{i_n}\, i_n \cdots i_1\, v$, where $w_i$ is $\sigma$ applied to the
$i$-th domino of $P$.

Such a derivation applies $S \to w_i\, S\, i$ for each index but the last and then
$S \to w_i\, i$.
