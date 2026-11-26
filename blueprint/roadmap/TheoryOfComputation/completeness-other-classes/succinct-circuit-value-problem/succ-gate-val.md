# Value of a gate of a succinct circuit (Succinct Circuit Value)

Let $C$ be a list of
encoded gates, let $n, i \in \mathbb{N}$, let $x$ be a list of booleans (the input) and let $v$
be a list of booleans (the values of earlier gates), where an entry outside $x$ or $v$ reads as
false. Let $(t, p_1, p_2)$ be the decoded description of gate $i$ of the circuit succinctly
described by $C$. If $i < n$, gate $i$ is an input gate and its value is $x_i$. Otherwise its
value is $v_{p_1} \land v_{p_2}$ if $t = 1$, $v_{p_1} \lor v_{p_2}$ if $t = 2$, $\lnot v_{p_1}$
if $t = 3$, true if $t = 4$, and false for every other $t$, including $t = 0$ and $t = 5$.
