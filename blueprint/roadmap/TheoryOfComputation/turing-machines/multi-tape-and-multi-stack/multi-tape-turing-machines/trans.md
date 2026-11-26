# Relabellings compose

Let $M$, $M'$ and $M''$ be multi-tape Turing machines with the same
number of work tapes and the same alphabet, with state sets $Q$, $Q'$ and $Q''$. If $M'$
simulates $M$ up to the state relabelling $f : Q \to Q'$ and $M''$ simulates $M'$ up to the
state relabelling $g : Q' \to Q''$, then $M''$ simulates $M$ up to the state relabelling
$g \circ f$.
