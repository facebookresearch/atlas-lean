# Coded configurations of a single-tape machine

For a single-tape Turing machine with state
set $Q$ and tape alphabet $\Sigma$, write $\bot$ for an absent value. A coded configuration is a
quadruple $(q, h, L, R)$ where $q \in Q \cup \{\bot\}$ is the state ($\bot$ meaning halted),
$h \in \Sigma \cup \{\bot\}$ is the symbol under the head ($\bot$ being the blank), and $L$ and $R$
are finite lists over $\Sigma \cup \{\bot\}$, meant as the cells to the left and to the right of
the head.
