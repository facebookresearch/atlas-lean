# Applying a relabelled action

Let $f : Q \to Q'$ be a map of states; relabelling by $f$
replaces a state $q$ by $f(q)$ and keeps the halting state. For every action $a$ of a machine with
$k$ work tapes and states $Q$ and every configuration $c$ of such a machine, applying $a$ with its
successor state relabelled by $f$ to $c$ with its state relabelled by $f$ gives the configuration
obtained by applying $a$ to $c$ and then relabelling its state by $f$.
