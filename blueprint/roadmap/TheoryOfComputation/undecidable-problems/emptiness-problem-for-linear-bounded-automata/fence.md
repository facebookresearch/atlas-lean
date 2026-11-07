# The fenced machine

For a single-tape machine $M$ over a finite inhabited alphabet $\Sigma$,
the fenced machine of $M$ is the single-tape machine over the fenced alphabet of $\Sigma$ whose
states are the states of the fenced machine for the states of $M$, which starts in the first start
state and acts on the cell under its head as follows. In the first start state, on a wall it moves
right into the second start state, and on any other cell it leaves the cell unchanged, does not
move and enters the trap. In the second start state, on a left padding cell it moves right and
stays in that state, and on any other cell it makes the running transition of the initial state of
$M$. In the running state of a state $q$ of $M$ it makes the running transition of $q$. In the
trap it leaves the cell unchanged, does not move and stays in the trap.

So on the fenced input of a word $w$ it moves right off the left wall and over the left padding,
then runs $M$ from its initial state, and enters the trap when it reads a wall or a blank cell. On
a blank cell, in every state, it writes a blank and does not move.
