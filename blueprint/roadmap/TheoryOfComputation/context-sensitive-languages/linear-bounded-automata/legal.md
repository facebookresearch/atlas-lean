# Legal head move of a linear bounded automaton

Let $h, n \in \mathbb{N}$ be a head position and a tape length. A left move is legal from $h$ on a tape of
length $n$ if $0 < h < n$; a stay move is legal if $h < n$; a right move is legal if $h + 1 < n$. Thus a
move is legal exactly when both the current head position and the new head position lie on the tape.
