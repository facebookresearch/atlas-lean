# The lookup contract

A lookup sub-program $lk$ with start label $l_0$ meets the contract
with constants $a$ and $b$ when the following holds. For every name $q$ (a list of bits), every
table $es$, with table stack $B_{es}$, and every list of symbols $R$ whose first symbol, if any,
is not a bit, start the clause-check machine with lookup $lk$ at label $l_0$, with any internal
state and with stack contents that have the bits of $q$ in reverse order followed by $R$ on the
token stack $T$, $B_{es}$ on $B$, and $S$, $A$, $C$, $V$ empty. Then it reaches label ret in at
most $a \cdot |B_{es}| + b$ steps, with some internal state, with $V$ holding exactly the bit
that is the live value of $q$ in $es$, and with every other stack unchanged.
