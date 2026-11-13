# Situation injectivity

Let $M$ be a finite stack machine with encoding data $E$, and write
$N$ for the number of situations of $E$, $K$ for the number of stacks of $E$ and $d$ for the
window depth of $M$. Let $c$ be a configuration of $M$ all of whose stack symbols lie in the
effective alphabets of $E$, and let $i < N$. If the label/state code of situation $i$ equals the
(label, state) code of $c$, and for every stack number $k < K$ and every depth $j < d$ the window
code of situation $i$ at stack $k$, depth $j$ equals the cell code of $c$ at stack $k$, depth
$j$, then $i$ is the situation index of $c$.

This is the converse of the fact that the situation index of such a $c$ is below $N$ and has the
code and the windows of $c$.
