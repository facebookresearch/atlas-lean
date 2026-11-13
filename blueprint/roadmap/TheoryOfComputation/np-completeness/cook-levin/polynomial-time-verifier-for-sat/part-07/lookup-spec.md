# The embedded lookup meets the lookup contract

The clause-check driver, with the embedded
lookup program as its lookup sub-program and the lookup's start label as the label it calls, meets
the driver's lookup contract with constants $a = 8$ and $b = 4$: from the lookup's start label,
with a reversed name block $q$ on the token stack $T$ above a rest that does not begin with a name
bit, the table stack of an entry list $es$ on $B$, and the stacks $S$, $A$, $C$, $V$ empty, it
reaches the driver's return label within $8m + 4$ steps, where $m$ is the length of the table
stack, with $V$ holding the single bit of the live value of $q$ in $es$ and every other stack
unchanged.
