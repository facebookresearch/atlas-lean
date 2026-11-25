# Thompson state counts of a node list

For a list $l$ of regular-expression nodes, the
list of Thompson state counts of $l$ is computed in one left-to-right pass: starting from the
empty list, each node $n$ of $l$ in turn appends the count of $n$ computed from the list of
counts built so far.
