# One step of the joint walk of the 3-COLOR verifier

The statement pops the top symbol of
each of the endpoint counters $U$ and $V$ (a pop from an empty counter leaves it empty) and then
moves the next color code $(a, b)$ from the color stack $P$ onto the scratch stack $T$, rejecting
if $P$ is empty. It continues at the joint walk again if both counters were nonempty; at the walk
towards the endpoint of $U$, holding the color $(a, b)$, if only $U$ was nonempty (so $(a, b)$ is
the color of the endpoint of $V$); at the walk towards the endpoint of $V$, holding $(a, b)$, if
only $V$ was nonempty; and at the restoring label $\mathsf{back}$ if both were empty. In the last
case the edge is a loop, which passes once its endpoint's color exists.
