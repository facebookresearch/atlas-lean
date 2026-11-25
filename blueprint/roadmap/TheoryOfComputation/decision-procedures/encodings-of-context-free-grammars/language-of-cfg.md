# The encoding of a grammar generates the same language

Let $T$ be an alphabet and let $G$ be a context-free grammar with terminals $T$. The encoding of $G$ is the
encoded context-free grammar obtained by numbering the nonterminals of $G$ (the initial nonterminal and
every nonterminal occurring in a production) by their positions in a fixed list of them, with start
nonterminal the number of the initial nonterminal and one production for each production of $G$, renamed
accordingly. The language of the encoding of $G$ equals the language of $G$.
