# Division map for the syntactic monoid of an inverse image

Let
$h \colon \Sigma^* \to \Gamma^*$ be a monoid morphism between free monoids and $L$ a language over
$\Gamma$. Write $[u]_L$ for the class of a word $u$ in the syntactic monoid $M(L)$ of $L$, $K$ for
the inverse image $h^{-1}(L) = \{w \in \Sigma^* \mid h(w) \in L\}$, and
$\varphi \colon \Sigma^* \to M(L)$ for the recognizing morphism $w \mapsto [h(w)]_L$. This is the
monoid morphism from the submonoid $\varphi(\Sigma^*)$ of $M(L)$ to the syntactic monoid $M(K)$
that sends $\varphi(w)$ to $[w]_K$; it is well defined because $\varphi(x) = \varphi(y)$ implies
$[x]_K = [y]_K$.

This morphism is surjective, so $M(K)$ is a quotient of a submonoid of $M(L)$.
