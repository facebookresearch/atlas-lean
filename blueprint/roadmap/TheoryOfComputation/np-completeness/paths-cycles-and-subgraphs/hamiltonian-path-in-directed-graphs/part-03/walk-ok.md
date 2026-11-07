# The walk check of the HAMPATH verifier

Fix natural numbers $s, t, n$ and a list $E$ of
pairs of natural numbers. The walk check accepts a list $q$ of natural numbers after $c$ vertices,
the last of which was $b$, by recursion on $q$. On the empty list it accepts if and only if
$c = n$, $c \neq 0$ and $b = t$. On a list with first entry $a$ and remaining entries $q'$ it
accepts if and only if the step check passes and the walk check accepts $q'$ after $c + 1$
vertices, the last of which was $a$. The step check requires $a < n$; it requires $a = s$ when
$c = 0$, and that $(b, a)$ is an entry of $E$ when $c \neq 0$; and it requires that $a$ does not
occur in $q'$.
