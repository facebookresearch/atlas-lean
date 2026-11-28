# Well-formed instances of SAT WITH AT MOST THREE LITERALS PER CLAUSE AND AT MOST THREE CLAUSES PER VARIABLE

An instance is well-formed when every clause has at most three literal entries, each on a variable below $n$, and for every variable $v < n$ at most three clauses contain a literal on $v$. A variable may repeat within a clause, so it can occur more than three times in all: the formula $(x \lor x \lor x) \land x$ is well-formed.
