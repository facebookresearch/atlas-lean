# Context-free languages are closed under substitution by context-free languages

Let $T$ and $T'$ be alphabets, let $L$ be a context-free language over $T$, and let $s$ assign to each
letter $a \in T$ a context-free language $s(a)$ over $T'$. Then the language

$$\{y \in T'^* : \text{there is } a_1 \cdots a_k \in L \text{ with } y \in s(a_1) s(a_2) \cdots s(a_k)\}$$

is context-free; here $s(a_1) \cdots s(a_k)$ is the concatenation of languages, which is $\{\varepsilon\}$ for
$k = 0$.
