# One step of the HAMPATH walk

Given natural numbers $s$ and $n$, an edge list $E$, a count
$c$ of vertices already seen, the previous vertex $b$, the current vertex $a$ and the list $q$ of
remaining vertices, the step check is true exactly when $a < n$, $a$ does not occur in $q$, and
either $c = 0$ and $a = s$, or $c \neq 0$ and $(b, a) \in E$.
