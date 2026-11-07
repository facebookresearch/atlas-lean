# Entries of a decoded stack on prefix-form input

Let $f : \mathbb{N} \to
\mathrm{Option}\,\alpha$ and write $\bot$ for the absent value. For $j, m \in \mathbb{N}$ let
$\mathrm{decS}(f, j, m)$ be the list of the values $f(j), f(j + 1), \dots$, read for at most $m$
positions and stopped at the first $\bot$. Suppose $f$ is in prefix form on the window from $j$
to $j + m$: whenever $j \le a \le b < j + m$ and $f(a) = \bot$, also $f(b) = \bot$. Then for every
$i < m$, the $i$-th entry of $\mathrm{decS}(f, j, m)$, taken to be $\bot$ when the list has at
most $i$ entries, equals $f(j + i)$.
