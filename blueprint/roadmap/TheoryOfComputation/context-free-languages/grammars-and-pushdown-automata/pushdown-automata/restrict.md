# Restricting the stack alphabet of a pushdown automaton

Let $M$ be a pushdown
automaton with stack alphabet $\Gamma$, and let $\Gamma_0 \subseteq \Gamma$ be a finite set
of stack symbols that contains the initial stack symbol of $M$ and is closed for $M$.
The restriction of $M$ to $\Gamma_0$ is the pushdown automaton with the same input
alphabet, states and start state as $M$, stack alphabet $\Gamma_0$, and the initial stack
symbol of $M$ as its initial stack symbol. Its transitions from a state $q$ on an input
option $o$ with top symbol $\gamma \in \Gamma_0$ are the transitions $(q', u)$ of $M$ from
$q$ on $o$ with top symbol $\gamma$, with the pushed list $u$ read as a list over
$\Gamma_0$; closedness guarantees that every symbol of $u$ lies in $\Gamma_0$.

The restricted automaton has a finite stack alphabet and accepts the same language as
$M$.
