# Transition morphism of a DFA

For a DFA $M$, the transition morphism is the monoid
homomorphism from the free monoid of words to the state transformations of $M$ that sends each
word $x$ to its transition action, the map taking each state $q$ to the state that $M$ reaches
by reading $x$ from $q$. State transformations are multiplied in reading order, so the product
$fg$ applies $f$ first and then $g$; with this order, the word $xy$ is sent to the product of
the images of $x$ and $y$.
