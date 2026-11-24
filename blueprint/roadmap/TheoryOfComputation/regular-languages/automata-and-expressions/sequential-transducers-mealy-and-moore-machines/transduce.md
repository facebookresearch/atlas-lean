# Transduction of a Mealy machine

Let $M$ be a Mealy machine with start state $q_0$. On
an input word $a_1 a_2 \cdots a_n$, for each $i$ let $q_i$ and $b_i$ be the state that $M$ moves
to and the letter that it outputs when it reads $a_i$ in state $q_{i-1}$. The transduction of
$M$ on this word is the output word $b_1 b_2 \cdots b_n$.
