# Membership atom of the PCP encoding checks index words

Let $\alpha$ be an alphabet. A domino over an alphabet $\alpha$ is a pair $d = (d^{\uparrow}, d^{\downarrow})$ of words over $\alpha$ (its top and bottom words). The block alphabet $\hat\alpha$ is the disjoint union of the set of all dominoes over $\alpha$ (whose elements, written $[d]$, are called domino letters) and $\alpha$ (plain letters). For a finite list $P$ of dominoes, $R_P$ is the regular expression $(\sum_{d \in P} [d])^*$ over $\hat\alpha$ (the sum being the regular expression for the empty language when $P$ is empty), whose language is the set of concatenations of domino letters of dominoes in $P$. For a finite list $P$ of dominoes and a word $x$ over
$\hat\alpha$ assigned to the variable, the atom stating that the variable lies in the language of (the
encoding of) $R_P$ is satisfied if and only if $x$ lies in the language of $R_P$.
