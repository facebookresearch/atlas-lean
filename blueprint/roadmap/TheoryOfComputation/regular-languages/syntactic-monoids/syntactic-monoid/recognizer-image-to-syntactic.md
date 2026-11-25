# Map from a recognizer's image to the syntactic monoid

Let $\varphi : \Sigma^* \to M$ be a
monoid morphism from the free monoid $\Sigma^*$ that recognizes a language $L$ over $\Sigma$
through a subset $A \subseteq M$. This is the monoid morphism from the image $\varphi(\Sigma^*)$
to the syntactic monoid of $L$ that sends $\varphi(x)$ to the syntactic class of $x$ for every
word $x$. It is well defined because words with the same image under $\varphi$ are syntactically
equivalent for $L$.
