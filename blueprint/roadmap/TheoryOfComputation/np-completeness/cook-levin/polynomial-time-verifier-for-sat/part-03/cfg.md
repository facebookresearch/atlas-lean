# Configurations of the clause-check machine

For a type $LL$ of lookup labels, a
configuration of the multi-stack Turing machine of the clause check: a current label (absent once
the machine halts) that is either a driver label or a label in $LL$, a Boolean internal state,
and the contents of the eight stacks $T$, $B$, $S$, $A$, $C$, $V$, $P$, $F$ of the clause check,
each a list of symbols of the token and table stacks (name bits, literal and clause markers, and
table markers).
