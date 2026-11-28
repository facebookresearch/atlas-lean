# Well-formed instances of DCJ MEDIAN

An instance is well-formed when the gene list is unary and each of the three adjacency lists passes the [genome-list](genome-list.md) test: bounded, distinct endpoints, no repeated or reversed pair, and each extremity in at most one adjacency. A list whose graph is a matching can still fail this test, for example $[(0, 1), (0, 1)]$ with one gene.
