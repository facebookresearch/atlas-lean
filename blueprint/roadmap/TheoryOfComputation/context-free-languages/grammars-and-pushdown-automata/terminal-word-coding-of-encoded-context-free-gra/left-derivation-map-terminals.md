# Coding a leftmost derivation

Let $T$ have decidable equality, let $\varphi$ send terminals of $T$ to words over $T'$ with induced word homomorphism $h$, and let $g$ be an encoded context-free grammar over $T$. If $g$ has a leftmost derivation from a sentential form $u$ to a word $w$ with rule list $\rho$, then the coded grammar has a leftmost derivation from the coded form of $u$ to $h(w)$ whose rule list consists of the coded rules of $\rho$, in the same order. No injectivity is needed.
