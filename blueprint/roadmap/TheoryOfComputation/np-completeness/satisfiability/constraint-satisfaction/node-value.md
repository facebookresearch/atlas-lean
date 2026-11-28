# Value of a term node

The integer value of a node $(\mathit{kind}, (a, b), \mathit{args})$ given the values of earlier nodes, an integer assignment $\sigma$ to the variables, and an interpretation $\varphi$ of the function symbols: $\sigma(a)$ for kind $0$, the integer $a - b$ for kind $1$, and, for every other kind, $\varphi(a)$ applied to the values of the argument nodes (argument nodes without a value read as $0$).
