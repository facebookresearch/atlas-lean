# Equality case of the Nerode state bound

Let $L$ be a language with finitely many
Nerode classes, and let $M$ be a DFA with a finite set of states $Q$ that accepts exactly $L$.
Send each Nerode class of $L$ to the state that $M$ reaches from its start state on the chosen
representative word of the class. Then the number of Nerode classes of $L$ equals $|Q|$ if and
only if every state in $Q$ is the image of some Nerode class under this map.
