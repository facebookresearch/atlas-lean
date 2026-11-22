# Run-wise Rabin/Streett duality

Let $r$ be a Rabin automaton and let $s$ be an infinite
sequence of states. Then $s$ satisfies the Rabin condition of $r$, that is, for some Rabin pair
$(E, F)$ of $r$ the sequence $s$ visits $E$ infinitely often and $F$ only finitely often, if and
only if $s$ fails the Streett condition with the same pairs, that is, it is not the case that for
every Rabin pair $(E, F)$ of $r$, if $s$ visits $E$ infinitely often then $s$ visits $F$
infinitely often.

The sequence $s$ need not be a run of $r$. (For languages of nondeterministic automata there is
no such complementation statement, since complementation also swaps the run quantifier.)
