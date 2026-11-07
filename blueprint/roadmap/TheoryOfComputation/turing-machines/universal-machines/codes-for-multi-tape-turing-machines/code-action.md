# Coded actions

A coded action for a machine with $k$ work tapes consists of a coded
input-head move; for each of the $k$ work tapes, an optional symbol to write, the symbol being a
bit or the blank (so a blank can be written), together with a coded head move; an optional
output bit; and an optional next state in $\mathbb{N}$, where no next state means halting. A
head move is coded by a natural number: $0$ moves left, $1$ stays, and any other number moves
right.
