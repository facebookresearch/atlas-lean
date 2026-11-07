# Run of an encoded NFA

For an encoded NFA $N$ and a word $w = a_1 \cdots a_n$, the run of
$N$ on $w$ is the list of states obtained by starting from the ε-closure of the start states of
$N$ and, for each letter $a_i$ in turn, taking the letter step on $a_i$ and then the ε-closure.
