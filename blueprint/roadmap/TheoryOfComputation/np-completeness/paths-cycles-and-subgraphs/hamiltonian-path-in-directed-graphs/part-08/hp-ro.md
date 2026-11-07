# Row vertices counted from either end

For $m$ clauses, let $r_{i,l} = m + i(3m + 2) + 1 + l$
be vertex $l$ of the row of diamond $i$. For a Boolean $b$ and a natural number $l$, this is
$r_{i,l}$ if $b$ is true and $r_{i,3m - l}$ if $b$ is false, where $3m - l$ is truncated
subtraction ($0$ when $l > 3m$). For $l \le 3m$ it is vertex $l$ of the row counted from the left
end ($b$ true) or from the right end ($b$ false).
