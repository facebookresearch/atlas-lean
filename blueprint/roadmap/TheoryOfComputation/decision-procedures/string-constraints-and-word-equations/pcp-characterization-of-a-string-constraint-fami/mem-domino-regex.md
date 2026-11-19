# Membership in the domino index-word language

Let $\alpha$ be an alphabet. A domino over an alphabet $\alpha$ is a pair $d = (d^{\uparrow}, d^{\downarrow})$ of words over $\alpha$ (its top and bottom words). The block alphabet $\hat\alpha$ is the disjoint union of the set of all dominoes over $\alpha$ (whose elements, written $[d]$, are called domino letters) and $\alpha$ (plain letters). For a finite list $P$ of dominoes, $R_P$ is the regular expression $(\sum_{d \in P} [d])^*$ over $\hat\alpha$ (the sum being the regular expression for the empty language when $P$ is empty), whose language is the set of concatenations of domino letters of dominoes in $P$. For a finite list $P$ of dominoes and a word $w$ over $\hat\alpha$,
$w$ lies in the language of $R_P$ if and only if $w$ is the concatenation $b_1 \cdots b_k$ of a finite list
of words $b_1, \dots, b_k$ ($k \ge 0$) each of which is a one-letter word $[d]$ with $d$ in $P$.
