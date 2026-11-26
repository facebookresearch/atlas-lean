# Reachable states of a DFA

Let $M$ be a DFA over a finite alphabet whose set of states
$\sigma$ is finite and has decidable equality. The reachable states of $M$ form the finite set
obtained from the empty set by applying one round of the DFA reachability search for $M$ exactly
$|\sigma|$ times, where $|\sigma|$ is the number of states of $M$.

Since the round is monotone, this set is its least fixed point, and a state lies in it exactly
when $M$ reaches it from its start state on some word.
