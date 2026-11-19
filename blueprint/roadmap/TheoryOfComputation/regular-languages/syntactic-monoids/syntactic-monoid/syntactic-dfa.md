# The syntactic DFA

Let $L$ be a language over an alphabet $\Sigma$. The syntactic DFA of
$L$ has the syntactic monoid of $L$ as its set of states, the identity $1$ as start state, and
the syntactic classes of the words of $L$ as accepting states; from a state $q$, reading a
letter $a \in \Sigma$ leads to $q \cdot [a]$, where $[a]$ is the syntactic class of the
one-letter word $a$.

It is the direct automata-theoretic presentation of the canonical syntactic recognizer.
