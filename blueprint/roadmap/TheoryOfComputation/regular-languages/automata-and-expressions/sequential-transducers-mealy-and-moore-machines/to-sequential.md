# Mealy machine as a sequential transducer

The sequential transducer of a Mealy machine
$M$ has the states and the start state of $M$; on an input letter $a$ in a state $q$ it moves
to the state that $M$ moves to and emits the one-letter word consisting of the letter that $M$
outputs on this transition. Every state accepts, and the initial and final outputs are empty.
