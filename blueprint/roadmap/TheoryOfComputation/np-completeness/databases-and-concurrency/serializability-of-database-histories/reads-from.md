# Reads-from relation

$R_j$ reads $x$ from $W_t$ when $x$ is in $R_j$'s read set and, scanning the augmented history backwards from the first occurrence of $R_j$ (from the end of the history if $R_j$ does not occur), the first write symbol whose write set contains $x$ is $W_t$. In a well-formed history $R_j$ occurs once, and this is the last write of $x$ before $R_j$.
