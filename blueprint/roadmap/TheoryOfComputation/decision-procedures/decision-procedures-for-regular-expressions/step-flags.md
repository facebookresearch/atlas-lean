# Flags of the next node

Given the list $A$ of flag triples of the nodes before it, the
flag triple of a node is $(\mathrm{false}, \mathrm{false}, \mathrm{false})$ for a zero node,
$(\mathrm{true}, \mathrm{false}, \mathrm{false})$ for an epsilon node and
$(\mathrm{true}, \mathrm{true}, \mathrm{false})$ for a letter node. For a sum, product or star
node it is the flags of a sum, product or star applied to the entries of $A$ at its arguments,
where an argument that is not an index of $A$ reads as
$(\mathrm{false}, \mathrm{false}, \mathrm{false})$.
