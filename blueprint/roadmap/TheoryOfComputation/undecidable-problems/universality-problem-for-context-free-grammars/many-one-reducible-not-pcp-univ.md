# The complement of PCP many-one reduces to universality of context-free grammars

Let
$\alpha$ be a finite alphabet with decidable equality and a primitive recursive encoding. There
is a computable map sending each PCP instance $P$ (a list of dominoes over $\alpha$) to an
encoded context-free grammar $G_P$ over the alphabet $\alpha \oplus \mathrm{Bool}$ (the letters
of $\alpha$ together with two bits) such that $P$ has no PCP solution if and only if $G_P$
generates every word over $\alpha \oplus \mathrm{Bool}$.
