# Feasibility for UPGRADING SPANNING TREE

An instance $(n, E, c, D, K)$ of UPGRADING SPANNING TREE is feasible when there is a finite set $W \subseteq \{0, \dots, n-1\}$ with

$$\sum_{v \in W} c(v) \le K,$$

where $c(v)$ is entry $v$ of the cost list (taken to be $0$ if the list is too short), together with a list $T$ that is a sublist of $E$ (obtained by deleting entries and keeping the order) such that the graph of $T$ on $n$ vertices is a tree and

$$\sum_{e \in T} d_W(e) \le D,$$

the sum running over the entries of $T$ with multiplicity, where $d_W(e)$ is the weight of $e$ after upgrading the vertices in $W$.
