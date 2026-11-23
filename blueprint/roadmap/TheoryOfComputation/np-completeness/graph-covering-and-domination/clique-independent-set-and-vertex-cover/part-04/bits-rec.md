# Row-by-row pair bits of an occurrence list

For a list of literal occurrences (clause
index, variable, polarity), the row-by-row pair bits are defined recursively: the empty list has
none, and for a list $o, o_1, \dots, o_k$ they are the adjacency bits of $o$ with
$o_k, \dots, o_1$, in that order, followed by the row-by-row pair bits of $o_1, \dots, o_k$.
Two occurrences are adjacent when they lie in different clauses and are not complementary.
