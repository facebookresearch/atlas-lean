# One marking pass

Given $n \in \mathbb{N}$, an edge list $E$ and a list $m$ of booleans
(the marks), the pass scans the pairs $(u, v)$ of $E$ in order and, whenever $u < n$, $v < n$
and position $u$ of the current marks is true, sets position $v$ to true. A position beyond the
end of the list counts as false and setting it changes nothing. Marks set earlier in the pass
are seen by later pairs.
