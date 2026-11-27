# MINIMAX APPROVAL VOTING is NP-complete

The decision problem MINIMAX APPROVAL VOTING is NP-complete: it belongs to NP, and every
decision problem in NP has a polynomial-time many-one reduction to it.

A direct reduction from VERTEX COVER gives the many-one reduction: with one vote approving the two
endpoints of each edge and a committee $S$ of size $k$, the distance to the vote for edge $e$ is
$k + 2 - 2|S \cap e|$, so a bound of $k$ holds exactly when every edge is hit.

Source: LeGrand (2004); LeGrand, Markakis and Mehta (2007); problem as defined by Cygan,
Kowalik, Socała and Sornat (2017).
