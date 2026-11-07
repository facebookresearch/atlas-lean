# The alphabet preimage morphism recognizes the alphabet preimage

Let
$f \colon \Sigma \to \Gamma$ be a map between alphabets and $L$ a language over $\Gamma$. Write
$f^*(w)$ for the word obtained by applying $f$ to each letter of a word $w$, $[u]_L$ for the
class of a word $u$ in the syntactic monoid $M(L)$ of $L$, $A_L \subseteq M(L)$ for the
accepting set of classes of words in $L$, and $\varphi \colon \Sigma^* \to M(L)$ for the alphabet
preimage morphism $w \mapsto [f^*(w)]_L$. Then $\varphi$ recognizes the alphabet preimage
$\{w \in \Sigma^* \mid f^*(w) \in L\}$ through $A_L$: for every word $w \in \Sigma^*$, we have
$f^*(w) \in L$ if and only if $\varphi(w) \in A_L$.
