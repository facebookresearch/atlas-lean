# Cooper's network of a CNF formula

A rational Boolean network is a list of nodes in topological order, the last node being the output;
each node has a list of parents and a table of rows $(u, n, d)$ giving
$P(\text{node} = \text{true} \mid u) = n / d$ for the parents' values $u$. Cooper's network of a CNF
formula starts from a constant-true node and adds the clauses from the last one. For each clause it
adds a constant-false node, then for each literal, from the last one, the root node of the literal's
variable (a parentless node true with probability $1/2$, created at the variable's first occurrence)
and an OR node of the chain output and that root, true exactly when the chain output is true or the
root has the literal's polarity. An AND node then joins the clause's output to the running AND
chain, whose last node is the network's output.
