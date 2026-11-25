# Reading the top through the windows

Let $d \in \mathbb{N}$, let $S_0$ and $P$ assign a list
to each stack, let $c$ assign a natural number to each stack, and let $k$ be a stack with
$c(k) < d$. Reading the top of stack $k$ from the depth-$d$ windows of the lists $S_0$, with pushed
symbols $P$ and consumption counts $c$, gives the first symbol of $P(k)$ followed by $S_0(k)$ with
its first $c(k)$ symbols removed, or ⊥ if that list is empty.
