# Strict Nerode state bound

Let $L$ be a language with finitely many Nerode classes, and
let $M$ be a DFA with a finite set of states $Q$ that accepts exactly $L$. Send each Nerode
class of $L$ to the state that $M$ reaches from its start state on the chosen representative
word of the class. If some state in $Q$ is not the image of any Nerode class under this map,
then the number of Nerode classes of $L$ is strictly less than $|Q|$.
