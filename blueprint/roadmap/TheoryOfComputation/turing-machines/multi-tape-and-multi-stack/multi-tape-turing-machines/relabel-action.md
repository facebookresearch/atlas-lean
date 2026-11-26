# Relabelling the successor state of an action

For a map $f : Q \to Q'$ of states and an
action $a$ of a machine with $k$ work tapes and states $Q$, the relabelled action is the action
with states $Q'$ that moves the input head, writes and moves on the work tapes and outputs exactly
as $a$ does, and whose successor state is $f(q)$ when $a$ goes to state $q$ and is halting when $a$
halts.
