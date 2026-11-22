# States of the homomorphic-image ε-NFA

Let $T$ be a finite alphabet, let $\varphi$ map
letters of $T$ to words over $T'$, let $\sigma$ be a set (the states of a DFA), and let $N$ be the
maximum of the lengths $|\varphi(a)|$ over $a \in T$. The states of the ε-NFA form the disjoint
union of $\sigma$ and the set of triples $(q, a, i)$ with $q \in \sigma$, $a \in T$ and
$0 \le i < N$.
