# Product DFA of a sequential transducer and a DFA

Let $S$ be a sequential transducer
with state type $Q$, input alphabet $\Sigma$ and output alphabet $\Gamma$, and let $M$ be a DFA
over $\Gamma$ with state type $P$. The product DFA of $S$ and $M$ is the DFA over $\Sigma$ with
state type $Q \times P$ defined as follows. In state $(q, r)$ on a letter $a$, if $S$ moves from
$q$ to $q'$ emitting the word $w$, it moves to $(q', r')$, where $r'$ is the state $M$ reaches
from $r$ on $w$. Its start state is $(q_0, r_0)$, where $q_0$ is the start state of $S$ and
$r_0$ is the state $M$ reaches from its start state on the initial output of $S$. A state
$(q, r)$ is accepting when $q$ is an accepting state of $S$ and the state $M$ reaches from $r$
on the final output of $S$ at $q$ is an accepting state of $M$.
