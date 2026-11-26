# Encoded parity game

An encoded finite parity game on the $n$ positions
$0, \dots, n - 1$ consists of an owner for each position, given as a Boolean (false for the even
player, true for the odd player), a move relation, given as a Boolean-valued $n \times n$
matrix, and a priority for each position, given as a natural number.

No seriality is assumed: a position may have no move, since restricted subgames need not be
serial on the whole arena.
