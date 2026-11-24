# Stack embedding of the lookup into the clause-check driver

Every stack of the lookup and
of the clause-check driver has the token alphabet of the SAT verifier. The lookup is embedded in the driver by
sending each of its stacks $T$, $B$, $S$, $A$, $C$, $V$ to the driver stack of the same name (an
injective map) and identifying the alphabets by the identity of the token alphabet.
