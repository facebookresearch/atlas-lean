# The embedded lookup program

The lookup sub-program of the clause-check driver: at each
lookup label $l$, it is the lookup program's statement at $l$ with every stack operation moved to
the driver's stack of the same name (the lookup's stacks $T$, $B$, $S$, $A$, $C$, $V$) and every
jump target relabelled by the lookup-label map, which sends $\mathsf{done}$ to the driver's
return label $\mathsf{ret}$ and keeps every other label.
