# Counter sequence of a state sequence

Let $g$ be a generalized Büchi automaton with $k$
acceptance sets and let $s = (s_0, s_1, \dots)$ be an infinite sequence of states. The counter
sequence $c_0, c_1, \dots$ of $s$, with values in $\{0, \dots, k\}$, is defined by $c_0 = 0$ and
$c_{n+1} = \mathrm{next}(c_n, s_{n+1})$, where $\mathrm{next}$ is the counter update of $g$. So
$c_n$ is the counter after reading the states $s_1, \dots, s_n$; the state $s_0$ is not read.
