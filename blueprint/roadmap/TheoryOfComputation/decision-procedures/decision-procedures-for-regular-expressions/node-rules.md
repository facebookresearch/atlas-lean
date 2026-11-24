# Productions of a node

For a natural number $k$ and a node $n$, the productions of
node $k$ are the following encoded productions, all with left-hand side $k$, where nonterminal
$i$ stands for node $i$: none if $n$ is the zero node; $k \to \varepsilon$ if $n$ is the
empty-word node; $k \to a$ if $n$ is the character $a$; if $n$ is a sum with arguments $i$ and
$j$, the unit production $k \to i$ when $i < k$ and the unit production $k \to j$ when
$j < k$; if $n$ is a product with arguments $i$ and $j$, the production $k \to i\,j$ when
$i < k$ and $j < k$; if $n$ is a star with argument $i$, the production $k \to \varepsilon$
together with $k \to i\,k$ when $i < k$.
