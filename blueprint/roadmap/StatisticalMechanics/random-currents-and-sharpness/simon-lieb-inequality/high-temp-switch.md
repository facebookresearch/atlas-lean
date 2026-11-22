# High-temperature switching map

Let $G = (V, E)$ be a finite simple graph, $S \subseteq V$ and $o, z \in V$ with $o \in S$ and $z \notin S$. For a [valid input](valid.md) $(F, H)$, let
$K = F \,\triangle\, H$ and let $(x, y, Q)$ be the [chosen first-exit data](high-temp-first-exit-2.md) for $K$. The switching sends
$(F, H)$ to the output $\bigl(x, y,\ H \,\triangle\, Q,\ (F \,\triangle\, Q) \setminus \{\{x, y\}\}\bigr)$: it cuts $K$ at its first exit
from $S$ and redistributes the pieces.
