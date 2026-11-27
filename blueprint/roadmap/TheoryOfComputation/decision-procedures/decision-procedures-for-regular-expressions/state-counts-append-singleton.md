# Appending a node appends its count

For every list $l$ of regular-expression nodes and
every node $n$, let $l'$ be the list $l$ with $n$ appended at the end. Then the list of Thompson
state counts of $l'$ is the list of counts of $l$ followed by one more entry, the count of $n$
computed from the counts of $l$.
