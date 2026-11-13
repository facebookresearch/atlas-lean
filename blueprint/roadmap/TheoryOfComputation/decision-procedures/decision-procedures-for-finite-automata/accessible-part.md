# Accessible part of a DFA

Let $M$ be a DFA over a finite alphabet $\alpha$ with a finite
state set $\sigma$ with decidable equality. The accessible part of $M$ is its accessible part found
by the reachability search with $|\sigma|$ rounds: the DFA over $\alpha$ whose states are the
states found by the reachability search from the empty set with at most $|\sigma|$ rounds (exactly
the states that some word leads to from the start state of $M$), whose start state is the start
state of $M$, whose transition function is that of $M$ restricted to these states, and whose
accepting states are those of them that $M$ accepts.
