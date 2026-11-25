# Joint-walk step when the second endpoint counter runs out first

Write $1^j$ for the
stack of $j$ copies of the bit symbol for true. If the endpoint counters of stacks $S$ hold
$U = 1^{u+1}$ and $V$ empty, then executing the joint-walk block from any internal value and
the stacks $S$ has the same outcome as executing, from internal value false and the stacks $S$
with $U$ replaced by $1^u$, the color-moving block that, after moving a color $(a, b)$,
continues to the label that walks on along $U$ holding $(a, b)$.
