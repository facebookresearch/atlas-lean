# Language of an encoded NFA

The language of an encoded NFA $N$ over an alphabet $\alpha$
is the language accepted by the ε-NFA that $N$ denotes, whose states are the natural numbers:
the words $w$ over $\alpha$ such that some accepting state of $N$ is among the states reached on
$w$ from the start states of $N$, with ε-moves allowed before, between and after the letters.
