# Division map for the syntactic monoid of an alphabet preimage

Let
$f \colon \Sigma \to \Gamma$ be a map between alphabets and $L$ a language over $\Gamma$. Write
$f^*(w)$ for the word obtained by applying $f$ to each letter of a word $w$, $[u]_L$ for the
class of a word $u$ in the syntactic monoid $M(L)$ of $L$, $K$ for the alphabet preimage
$\{w \in \Sigma^* \mid f^*(w) \in L\}$, and $\varphi \colon \Sigma^* \to M(L)$ for the alphabet
preimage morphism $w \mapsto [f^*(w)]_L$. This is the monoid morphism from the submonoid
$\varphi(\Sigma^*)$ of $M(L)$ to the syntactic monoid $M(K)$ that sends $\varphi(w)$ to $[w]_K$;
it is well defined because $\varphi(x) = \varphi(y)$ implies $[x]_K = [y]_K$.

This morphism is surjective, so $M(K)$ is a quotient of a submonoid of $M(L)$.
