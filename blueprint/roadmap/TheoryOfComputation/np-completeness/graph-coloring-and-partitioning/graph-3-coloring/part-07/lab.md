# Labels of the 3-COLOR verifier

The labels are: read the number $n$ of vertices onto the
counter stack $N$; load the witness colors onto the scratch stack $T$; move them onto the color
stack $P$; start an edge; read its first endpoint onto the counter stack $U$; read its second
endpoint onto the counter stack $V$; walk the colors towards both endpoints; for each pair of
bits $(a, b)$, walk on towards the farther endpoint holding the nearer one's color $(a, b)$, one
label for counter $U$ and one for counter $V$; restore $P$; accept; reject.
