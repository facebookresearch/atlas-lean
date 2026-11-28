# Data of a phylogenetic tree

A tree record is a triple of a natural number $n$ of vertices, a list of natural pairs (the edges) and a list of natural vertex labels whose $x$-th entry is read as the leaf of taxon $x$. The data are raw: a record may have an edge $(7, 9)$ with one declared vertex, or leaf entries that are not vertices. That a record describes an unrooted binary phylogenetic tree on the taxa is a separate condition.
