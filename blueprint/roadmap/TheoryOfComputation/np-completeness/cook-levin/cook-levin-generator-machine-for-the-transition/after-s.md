# Label after a situation clause in the transition-family generator

Let $N$ be the number
of situations. For a natural number $i$, the label the generator moves to after the clause of
situation $i$ is the end-of-time-step label if $i = 0$. Otherwise it is the first label of the
clause routine for situation $i - 1$ if $i - 1 < N$, and the end-of-time-step label again if
$i - 1 \ge N$.
