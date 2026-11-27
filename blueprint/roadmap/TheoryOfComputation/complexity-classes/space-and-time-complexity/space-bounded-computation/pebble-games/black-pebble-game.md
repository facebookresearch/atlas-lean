# Black pebble game and black pebbling price

Let $G$ be a directed acyclic graph, an arc $u\to v$ meaning that $u$ is an immediate predecessor of $v$. A **configuration** is a finite set $C\subseteq V(G)$ of pebbled vertices. A **move** either places a pebble on a vertex $v\notin C$ all of whose predecessors lie in $C$ (in particular on any source), or removes a pebble from a vertex of $C$. A vertex $v$ is **pebblable with $s$ pebbles** if some sequence of moves from $C_0=\emptyset$ reaches a configuration containing $v$ while every configuration along the way has at most $s$ pebbles. The **black pebbling price** $\mathrm{Peb}(G,v)$ is the least such $s$. Pebblability is monotone in $s$, and on a finite DAG every vertex is pebblable with $|V(G)|$ pebbles.

## Sources

- Michael S. Paterson and Carl E. Hewitt, "Comparative Schematology", Record of the Project MAC Conference on Concurrent Systems and Parallel Computation, ACM, 1970, pp. 119–127.
- Jakob Nordström, "Pebble Games, Proof Complexity, and Time-Space Trade-offs", Logical Methods in Computer Science 9(3):15, 2013.
- John E. Savage, "Models of Computation: Exploring the Power of Computing", Addison-Wesley, 1998.
