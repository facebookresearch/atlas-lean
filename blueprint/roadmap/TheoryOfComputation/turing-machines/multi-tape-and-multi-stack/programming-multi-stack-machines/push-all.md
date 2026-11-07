# Pushing symbols onto several stacks

Let $ps$ be a list of pairs $(k, x)$ of a stack index
$k$ and a symbol $x$ of the alphabet of stack $k$, and let $q$ be a statement of a TM2 machine.
This is the statement that, for each pair $(k, x)$ of $ps$ in list order, pushes $x$ onto stack
$k$, and then continues with $q$.
