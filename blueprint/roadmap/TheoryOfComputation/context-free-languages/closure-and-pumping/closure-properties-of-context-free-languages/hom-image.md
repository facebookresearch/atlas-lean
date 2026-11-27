# Context-free languages are closed under homomorphic images

Let $T$ and $T'$ be alphabets,
$L$ a context-free language over $T$, and $\varphi$ a map sending each letter of $T$ to a word
over $T'$. Then the language of all words $\varphi(a_1) \cdots \varphi(a_n)$ with
$a_1 \cdots a_n \in L$ is context-free.

A grammar for it replaces every terminal $a$ in every production by the word $\varphi(a)$.
