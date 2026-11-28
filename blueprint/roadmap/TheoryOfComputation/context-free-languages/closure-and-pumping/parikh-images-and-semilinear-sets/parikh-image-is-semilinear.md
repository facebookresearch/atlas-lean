# Parikh's theorem: the Parikh image of every context-free language is semilinear

Let $T$ be an alphabet with decidable equality (no finiteness is assumed). The Parikh vector of a word $w \in T^*$ is the map $\psi(w) : T \to \mathbb{N}$ sending each letter $a$ to the number of occurrences of $a$ in $w$, and the Parikh image of a language $L$ is $\psi(L) = \{\psi(w) : w \in L\}$. A set $S$ of maps $T \to \mathbb{N}$ is linear if there are $b : T \to \mathbb{N}$ and finitely many $p_1, \dots, p_k : T \to \mathbb{N}$ with

$$S = \{\, b + c_1 p_1 + \cdots + c_k p_k : c_1, \dots, c_k \in \mathbb{N} \,\},$$

and semilinear if it is a finite union of linear sets.

The following holds: for every context-free language $L \subseteq T^*$, the Parikh image $\psi(L)$ is semilinear.

## Sources

- R. J. Parikh, "On context-free languages", *Journal of the ACM* 13 (1966), 570-581.
