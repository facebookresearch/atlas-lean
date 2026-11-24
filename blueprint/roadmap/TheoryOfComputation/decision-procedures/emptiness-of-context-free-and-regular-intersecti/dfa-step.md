# One round of the item search against a DFA

For an encoded grammar $g$, an encoded DFA
$D$ and a list $R$ of natural numbers (the items found so far), one round produces the list of the
codes $\langle A, \langle p, q \rangle \rangle$, where $\langle \cdot, \cdot \rangle$ is the
natural-number pairing, for every production $A \to \beta$ of $g$, every state $q$ of $D$ and
every start state $p$ of $\beta$ for $q$ given $R$.
