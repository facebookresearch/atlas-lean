# Soundness of the paths of the substitution ε-NFA

Let $M$ be a DFA over $T$ with start
state $q_0$, and for each letter $a \in T$ let $N_a$ be a DFA over $T'$, with accepted language
$L(N_a)$; for a word $w = a_1 \cdots a_n$ over $T$ write $L_w = L(N_{a_1}) \cdots L(N_{a_n})$,
which is $\{\varepsilon\}$ when $w$ is empty. Let $x$ be a sequence of labels, each a letter of
$T'$ or $\varepsilon$, let $\bar x$ be the word over $T'$ obtained from $x$ by deleting the
$\varepsilon$'s, and suppose the ε-NFA built from $M$ and the $N_a$ has a path reading $x$ from
the state $q_0$ of $M$ to a state $u$. If $u$ is a state $q$ of $M$, then there is a word $w$
over $T$ such that $M$ reaches $q$ from $q_0$ on $w$ and $\bar x \in L_w$. If $u$ is the state
$p$ of the copy of $N_a$ entered from the state $q$ of $M$, then there are a word $w$ over $T$
such that $M$ reaches $q$ from $q_0$ on $w$, a word $y_1 \in L_w$ and a word $y_2$ over $T'$
such that $\bar x = y_1 y_2$ and $N_a$ reaches $p$ from its start state on $y_2$.
