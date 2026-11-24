# Words spelling a configuration

A word $w$ spells a configuration $c$ of a single-tape
Turing machine if there are a state $q$, a tape symbol $h$ and words $L$, $R$ of tape symbols
such that $c$ is in state $q$, its head reads $h$, its tape reads $L$ immediately to the left of
the head and $R$ immediately to the right of it, with blanks beyond, and
$w = \vdash L\,q\,h\,R \dashv$.
