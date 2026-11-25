# Composition of sequential transducers

Let $S_1$ be a sequential transducer from $I$ to
$M$ with start state $s_1$, initial output $\iota_1$ and final output map $\phi_1$, and let $S_2$
be one from $M$ to $O$ with start state $s_2$, initial output $\iota_2$ and final output map
$\phi_2$. For a transducer $S$, a state $q$ and a word $w$, write $\delta_S(q, w)$ for the state
$S$ reaches by reading $w$ from $q$ and $\lambda_S(q, w)$ for the concatenation of the words it
emits along the way. The composition of $S_1$ and $S_2$ is the sequential transducer from $I$ to
$O$ whose states are the pairs $(q_1, q_2)$ of a state of $S_1$ and a state of $S_2$, where:
reading a letter $a$ in state $(q_1, q_2)$, if $S_1$ reading $a$ in $q_1$ moves to $q_1'$ and
emits $w$, the composition moves to $(q_1', \delta_{S_2}(q_2, w))$ and emits
$\lambda_{S_2}(q_2, w)$; the start state is $(s_1, \delta_{S_2}(s_2, \iota_1))$; the initial
output is $\iota_2$ followed by $\lambda_{S_2}(s_2, \iota_1)$; a state $(q_1, q_2)$ is accepting
when $q_1$ is accepting for $S_1$ and $\delta_{S_2}(q_2, \phi_1(q_1))$ is accepting for $S_2$; and
the final output at $(q_1, q_2)$ is $\lambda_{S_2}(q_2, \phi_1(q_1))$ followed by
$\phi_2(\delta_{S_2}(q_2, \phi_1(q_1)))$.

In words: run $S_1$ and feed its output, including its initial output (fed through $S_2$ before
any input is read) and its final output, through $S_2$.
