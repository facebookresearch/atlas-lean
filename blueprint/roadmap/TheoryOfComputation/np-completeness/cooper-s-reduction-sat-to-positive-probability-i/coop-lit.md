# Adding a literal

In Cooper's construction, adding a literal $(x, b)$ to a state with chain output $o$ first takes the root of the variable $x$ (creating it if needed) and then appends an OR node whose parents are $o$ and that root, true exactly when $o$ is true or the root has value $b$. The new OR node, whose index is the number of nodes before it was added, is the new chain output.
