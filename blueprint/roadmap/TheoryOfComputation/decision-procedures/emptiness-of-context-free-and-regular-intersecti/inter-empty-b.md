# The intersection-emptiness test for a grammar and a DFA

Let $g$ be an encoded grammar with
start nonterminal $S$, let $D$ be an encoded DFA with start state $s$, and write
$\langle \cdot, \cdot \rangle$ for the natural-number pairing. The test of $g$ and $D$ is true
exactly when there is no accepting state $f$ of $D$ that is also one of the states of $D$ and for
which the code $\langle S, \langle s, f \rangle \rangle$ is among the found items of $g$ and
$D$.
