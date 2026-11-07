# The running transition of the fenced machine

In the running state of a state $q$ of a
single-tape machine $M$, the fenced machine of $M$ acts on the cell under its head as follows: on a
symbol $a$ it makes the lifted transition of $M$ in state $q$ on $a$; on a left or right padding
cell it makes the lifted transition of $M$ in state $q$ on a blank; on a wall or a blank cell it
leaves the cell unchanged, does not move, and enters the trap.
