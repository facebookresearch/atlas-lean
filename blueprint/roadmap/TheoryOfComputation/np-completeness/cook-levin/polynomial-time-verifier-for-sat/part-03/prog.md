# The clause-check driver with a lookup sub-program

Given a lookup sub-program $lk$ on a
label set $L$ and an entry label $l_0 \in L$, this is the program on the labels $D \sqcup L$, where
$D$ is the set of driver labels: at a driver label $d$ it runs the driver's statement for $d$
(the driver calls the lookup by jumping to $l_0$), and at a label $l \in L$ it runs $lk(l)$.
