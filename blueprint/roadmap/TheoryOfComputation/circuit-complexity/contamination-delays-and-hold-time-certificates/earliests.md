# Earliest changes of the gates of a program

Given a contamination delay $d_j \in \mathbb{R}$ for every gate and an earliest change time in $\mathbb{R} \cup \{\infty\}$ for every input, the earliest changes of the gates of a straight-line program are computed gate by gate: each gate's earliest change is its delay plus the minimum, starting from $\infty$, of the earliest changes of the inputs and earlier gates it reads.
