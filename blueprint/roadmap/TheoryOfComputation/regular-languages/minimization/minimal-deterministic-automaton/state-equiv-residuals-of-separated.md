# States of an accessible, state-separated DFA correspond to residuals

Let $M$ be a DFA
that is accessible and state-separated, and let $L$ be the language it accepts. The map sending
each state $q$ of $M$ to the language of words accepted by $M$ starting from $q$ is a bijection
from the states of $M$ onto the set of left quotients $\{z : xz \in L\}$ of $L$ by words $x$.
