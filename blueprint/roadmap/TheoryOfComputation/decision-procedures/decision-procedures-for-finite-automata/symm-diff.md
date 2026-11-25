# Symmetric difference of two DFAs

For DFAs $M$ and $N$ over the same alphabet, with sets of
states $\sigma$ and $\sigma'$, this is the product DFA with set of states $\sigma \times \sigma'$
whose start state is the pair of the start states of $M$ and $N$, whose transition takes $(p, q)$
on a letter $a$ to the pair of the state to which $M$ moves from $p$ on $a$ and the state to which
$N$ moves from $q$ on $a$, and whose accepting states are the pairs $(p, q)$ such that $p$ is an
accepting state of $M$ or $q$ is an accepting state of $N$, but not both.

It accepts exactly the words on which $M$ and $N$ disagree.
