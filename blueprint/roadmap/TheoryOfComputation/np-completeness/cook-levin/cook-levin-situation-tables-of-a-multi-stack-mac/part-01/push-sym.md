# Symbols a statement tree can push

Let $q$ be a statement tree of a multi-stack Turing
machine with state type $\sigma$, let $k$ be a stack and $x$ a symbol of the alphabet of $k$. Then
$x$ can be pushed onto $k$ by $q$ when $q$ contains a push node onto stack $k$ with symbol
function $f$ and some state $v \in \sigma$ satisfies $x = f(v)$. Every push node of $q$ counts,
whichever branches are taken.
