# The clause-check driver

Given the lookup's start label $l_0$, the statement at each
driver label. At start: if the token stack $T$ is empty, go to yes; if its top is a clause
marker, pop it, push the bit false onto the flag stack $F$ and go to lits; otherwise go to no.
At lits: if the top of $T$ is a literal marker of polarity $p$, pop it, push the bit $p$ onto
the polarity stack $P$ and go to $l_0$; otherwise go to endc. At ret: if the top of the value
stack $V$ is the bit true exactly when the top of $P$ is the bit true, pop $F$ and push the bit
true onto it; in either case then pop $V$, pop $P$ and go to drop. At drop: if the top of $T$
is a bit, pop it and go to drop; otherwise go to lits. At endc: if the top of $F$ is the bit
true, pop it and go to start; otherwise go to no. At yes and at no: halt.
