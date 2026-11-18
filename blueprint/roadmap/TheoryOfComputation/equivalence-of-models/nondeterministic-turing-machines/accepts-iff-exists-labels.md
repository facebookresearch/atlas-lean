# Acceptance as a label list

A single-tape nondeterministic Turing machine $m$ accepts a
word $x$ if and only if there is a list $\mu$ of transition labels (read a symbol, write a symbol,
move, skip) such that applying the labels of $\mu$ in order to the input tape of $x$ (the tape
holding $x$ from the head cell rightward, every other cell blank) never fails, that is, every read
label finds its symbol in the cell under the head, and $\mu$ leads the automaton of $m$ from some
start state to some accepting state.
