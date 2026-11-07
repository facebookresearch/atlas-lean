# Consistency edges between two occurrences of a variable

Let $l = (x, b)$ be a literal
with variable index $x$ and polarity $b$, let $L$, $M$ be the vertices of a new occurrence of
$l$, and let $(x', b', L', M')$ be an earlier occurrence. If $x' \ne x$ the list of consistency
edges is empty. If $x' = x$ and $b' = b$ it is $[(L', M), (M', L)]$; if $x' = x$ and $b' \ne b$
it is $[(L', L), (M', M)]$.
