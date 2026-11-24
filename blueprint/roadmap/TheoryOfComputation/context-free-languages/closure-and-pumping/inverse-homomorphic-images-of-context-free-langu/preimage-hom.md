# Context-free languages are closed under inverse homomorphisms

Let $T$ be a finite alphabet, $T'$ an alphabet, $L$ a context-free language over $T'$, and $\varphi : T \to T'^*$
a map, extended to the monoid morphism $\varphi(a_1 \cdots a_k) = \varphi(a_1) \cdots \varphi(a_k)$. Then the
language $\{w \in T^* : \varphi(w) \in L\}$ is context-free.
