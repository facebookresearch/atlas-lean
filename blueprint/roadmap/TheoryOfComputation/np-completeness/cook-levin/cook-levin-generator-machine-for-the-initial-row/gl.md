# Labels of the initial-row generator

For natural numbers $g$ and $n$, the labels are: a
label for each stage of the first precomputation part and one for each stage of the second; for
each loop phase $p$, a loop-head label, a counter-reset label, two base-copy labels, a
multiplication label for each multiplication stage and a base-drain label; for the input loop,
a head label, two base-copy labels, a multiplication label for each multiplication stage, a read
test for each code $i < g$ and a base-drain label; an error label; for each clause kind $c$ for
$g$ and $n$, a clause-start label, two labels copying the variable count, a literal label for
each literal index $l < n + 2$ and each literal stage, and a label emitting the leading gap; and
a final label. The label type has decidable equality and is finite.
