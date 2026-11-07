# The reachable states are those some word can lead to

For an encoded NFA $N$ and a natural
number $t$, $t$ is among the reachable states of $N$ if and only if there is a word $w$ such that
$t$ is among the states that the ε-NFA denoted by $N$ reaches on $w$ from its start states, with
ε-moves allowed before, between and after the letters.
