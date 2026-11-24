# The forward map undoes the backward map

Let $(X_i)_{i \in \iota}$ be topological spaces
with subsets $U_i \subseteq X_i$, let $P$ be their restricted product (the tuples with
$x_i \in U_i$ for all but finitely many $i$), and let $L$ be the direct limit, over finite sets
$S \subseteq \iota$, of the pieces $X_S$ of tuples with $x_i \in U_i$ for all $i \notin S$. Let
$f : P \to L$ be the forward map, sending $x$ to its class in the piece indexed by its support
$\{i : x_i \notin U_i\}$, and let $g : L \to P$ be the backward map, sending a class to the tuple
carried by any of its representatives. Then $f(g(q)) = q$ for every $q \in L$.
