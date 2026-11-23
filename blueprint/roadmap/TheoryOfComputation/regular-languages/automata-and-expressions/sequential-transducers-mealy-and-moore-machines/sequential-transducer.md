# Sequential transducer

A sequential transducer with states in a type $Q$, input letters in
a type $\Sigma$ and output letters in a type $\Gamma$ consists of a transition function assigning
to each state $q \in Q$ and input letter $a \in \Sigma$ a successor state in $Q$ and an output
word over $\Gamma$, a start state in $Q$, a set of accepting states $F \subseteq Q$, an initial
output word over $\Gamma$, and, for each state in $Q$, a final output word over $\Gamma$.

No finiteness is assumed of $Q$, $\Sigma$ or $\Gamma$.
