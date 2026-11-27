# One round of the DFA reachability search

Let $M$ be a DFA over a finite alphabet
$\alpha$. The round sends a finite set $S$ of states of $M$ to the set consisting of the start
state of $M$ and of every state that the transition function of $M$ takes some $s \in S$ to on
some letter $a \in \alpha$.
