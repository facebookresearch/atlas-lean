# Loops solving a PIPE LINK instance

A closed walk $c$ in the grid graph of a PIPE LINK instance solves the instance when

1. every square of the grid lies on $c$;
2. at every clue square $x$ (a square holding a piece) and every square $w$ adjacent to $x$, the loop uses the side between $x$ and $w$ exactly when the clue piece at $x$ opens towards $w$; and
3. a square where the loop turns (two consecutive steps of $c$, taken cyclically, that are not in a straight line) is visited only once, so a square visited twice is crossed straight both times.
