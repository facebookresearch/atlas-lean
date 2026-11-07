# The halting set of a single-tape machine on binary inputs is r.e

Let $M$ be a single-tape
Turing machine over a finite alphabet $\Sigma$ and $\iota$ any map from the Booleans to $\Sigma$.
Then the set of natural numbers $n$ such that $M$ halts on the word obtained by applying $\iota$
letterwise to the binary code of $n$ (least significant bit first, the empty word for $0$) is
recursively enumerable.
