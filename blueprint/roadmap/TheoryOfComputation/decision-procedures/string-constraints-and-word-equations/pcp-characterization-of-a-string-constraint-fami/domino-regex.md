# Regular language of domino index words

Let $\alpha$ be an alphabet. A domino over an alphabet $\alpha$ is a pair $d = (d^{\uparrow}, d^{\downarrow})$ of words over $\alpha$ (its top and bottom words). The block alphabet $\hat\alpha$ is the disjoint union of the set of all dominoes over $\alpha$ (whose elements, written $[d]$, are called domino letters) and $\alpha$ (plain letters). For a finite list $P$ of dominoes, the index-word regular expression of
$P$ is $(\sum_{d \in P} [d])^*$, the Kleene star of the sum of the one-letter expressions $[d]$ for $d$ in
$P$ (the sum of the empty list being the expression for the empty language, so that for empty $P$ the
language is $\{\varepsilon\}$). Its language is the set of concatenations of domino letters of dominoes
in $P$.
