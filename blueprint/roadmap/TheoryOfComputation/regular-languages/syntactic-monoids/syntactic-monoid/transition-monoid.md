# Transition monoid of a DFA

The transition monoid of a DFA $M$ is the image of the
transition morphism of $M$: the submonoid of state transformations of $M$ consisting of the
transition actions of all words, where a word $x$ acts by sending each state $q$ to the state
that $M$ reaches by reading $x$ from $q$. State transformations are multiplied in reading
order, so the product $fg$ applies $f$ first and then $g$.
