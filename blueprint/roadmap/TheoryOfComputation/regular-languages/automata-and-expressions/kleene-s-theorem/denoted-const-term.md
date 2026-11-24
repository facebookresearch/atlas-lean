# DFA equation constant terms are regex-denoted

Let $\alpha$ be an alphabet. A language over $\alpha$ is regex-denoted if it is the language matched by some regular expression over $\alpha$ (regular expressions being built from $0$, $1$ and single letters by sum, concatenation and Kleene star). Let $M$ be a deterministic automaton with input alphabet $\alpha$, state set $Q$, transition function $\delta$ and set of accepting states $F$. For every state $q$, the constant term $B_q$ ($\{\varepsilon\}$ if $q \in F$,
$\emptyset$ otherwise) is regex-denoted.
