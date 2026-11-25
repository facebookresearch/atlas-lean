# Moving one color code from the color stack

Let $f$ assign a label to each pair of
bits, and suppose the color stack $P$ of stacks $S$ holds, from the top, the bit symbols $c_1$
and $c_2$ followed by a rest $r$. Then executing the color-moving block with continuation $f$,
from any internal value and the stacks $S$, ends at label $f(c_1, c_2)$ with internal value
$c_2$ and with the stacks $S$ changed only in that $P$ becomes $r$ and the scratch stack $T$
gets $c_1$ and then $c_2$ pushed on top (so $c_2$ is on top).
