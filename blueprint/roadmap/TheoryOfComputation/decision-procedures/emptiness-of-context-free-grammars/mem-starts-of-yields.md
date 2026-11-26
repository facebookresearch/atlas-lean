# Completeness of the start positions

Let $g$ be an encoded context-free grammar over an
alphabet $T$ with decidable equality, let $w$ be a word over $T$, and let $\rho$ be an encoded
right-hand side whose decoding yields a word $u$ in the grammar that $g$ denotes. If
$i \le j \le |w|$ and $u$ is the factor of $w$ from position $i$ to position $j$, then $i$ is a
start position of $\rho$ at $j$ for the word $w$ and the list of items found by the membership
procedure on $g$ and $w$.
