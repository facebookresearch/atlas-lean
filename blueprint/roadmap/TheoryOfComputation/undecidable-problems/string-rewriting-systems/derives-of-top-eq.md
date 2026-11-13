# The backward direction of the MPCP reduction

Let $(R, x, y)$ be a reachability instance
and read words over $\alpha$ as words of letters. Let $A$ be a sequence of dominoes of the MPCP
instance of $(R, x, y)$. For all words $v, s, t$ over $\alpha$, if $s$ rewrites to $t$ under $R$
in zero or more steps and the top of $A$ equals $v \star t$ followed by the bottom of $A$, where
$\star$ is the row separator, then $s v$ rewrites to $y$ under $R$ in zero or more steps.

Reading the dominoes left to right, $s$ is the part of the current row already matched, with
bottoms $t$, and $v$ is the rest of the row still to be matched on top.
