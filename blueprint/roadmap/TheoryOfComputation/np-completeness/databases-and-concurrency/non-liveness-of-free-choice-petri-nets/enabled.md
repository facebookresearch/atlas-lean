# Enabled transitions of a Petri net

A transition $t = (a, b)$, with input places $a$ and output places $b$ given as Boolean lists, is enabled at a marking $M$ when every input place $j$ of $t$ (an entry of $a$ that is true; missing entries count as false) holds at least one token: $M(j) \ge 1$.
