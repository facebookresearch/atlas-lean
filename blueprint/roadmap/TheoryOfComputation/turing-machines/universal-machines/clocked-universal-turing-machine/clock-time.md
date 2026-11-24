# Step bound of the clocked simulation

For a code $c$ and a clock $T$, let $|C|$ be the
length of the code stack of $c$. The step bound of the clocked simulation on the clock $T$ is
$T + 1$ times the cost of one round of the loop on configurations whose numbers are at most
$|C| + 2$, that is, $(T + 1)(14|C| + 19)$.
