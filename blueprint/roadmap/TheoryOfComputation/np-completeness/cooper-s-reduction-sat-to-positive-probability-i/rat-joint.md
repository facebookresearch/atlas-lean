# Rational joint

For a rational Boolean network and an assignment $x$ of Booleans to its nodes, the rational joint is the product over the nodes $k$ of $p_k$ if $x(k)$ is true and $1 - p_k$ if $x(k)$ is false, where $p_k$ is the table entry of node $k$ read at its parents' values under $x$, in the order of its parent list (a listed parent outside the network reads $\mathsf{false}$). The empty product, for the empty network, is $1$. A row stores the value for true only: a constant-true node has stored value $1$, and its factor for an assignment that sets it false is $1 - 1 = 0$.
