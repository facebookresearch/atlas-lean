# Bounds consistency and range consistency

Bounds consistency and range consistency weaken generalized arc consistency on integer domains by letting the other variables take any value between their current minimum and maximum, not only values still in their domains.

Let $C$ be a constraint with scope $(x_1,\dots,x_k)$ whose values are integers, and let $D$ give each $x_i$ a finite nonempty set $D(x_i)\subseteq\mathbb Z$. Write $\min D(x)$ and $\max D(x)$ for its least and greatest element and $[a,b]=\{a,a+1,\dots,b\}$.

- A value $v\in D(x_i)$ has a **domain support** in $C$ if some $t\in C$ has $t_i=v$ and $t_j\in D(x_j)$ for all $j$; it has an **interval support** if some $t\in C$ has $t_i=v$ and $t_j\in[\min D(x_j),\max D(x_j)]$ for all $j$.
- $C$ is **domain consistent** (DC) on $D$ if every value of every $D(x_i)$ has a domain support; this is [generalized arc consistency](generalized-arc-consistency.md).
- $C$ is **range consistent** (RC) on $D$ if every value of every $D(x_i)$ has an interval support.
- $C$ is **bounds consistent** (BC) on $D$ if for every $i$ the two values $\min D(x_i)$ and $\max D(x_i)$ have interval supports.

A domain support is an interval support, and the bounds belong to the domain, so DC implies RC and RC implies BC. When every $D(x_i)$ is an interval the two kinds of support coincide and RC is the same as DC. Enforcing BC only moves the bounds of each domain, enforcing RC may also delete interior values, and both definitions depend on the integer order, which DC does not.

## Depends on

- [Generalized arc consistency](generalized-arc-consistency.md): DC is GAC, and the support notion is the same.

## Proof depends on

None.

## Expansion

The implications DC $\Rightarrow$ RC $\Rightarrow$ BC follow by reading the definitions: $D(x_j)\subseteq[\min D(x_j),\max D(x_j)]$, and $\min D(x_i),\max D(x_i)\in D(x_i)$. When all domains are intervals, $D(x_j)=[\min D(x_j),\max D(x_j)]$ and the two support notions agree. López-Ortiz, Quimper, Tromp and van Beek's Example 1 (after Puget) shows that BC can prune strictly: on $x_1\in[3,4]$, $x_2\in[2,4]$, $x_3\in[3,4]$, $x_4\in[2,5]$, $x_5\in[3,6]$, $x_6\in[1,6]$ with $x_1,\dots,x_6$ pairwise different, BC reduces the domains to $[3,4],[2],[3,4],[5],[6],[1]$. Bessiere, Katsirelos, Narodytska, Quimper and Walsh's running example shows RC deleting an interior value that BC keeps.

## Sources

- A. López-Ortiz, C.-G. Quimper, J. Tromp and P. van Beek, "A fast and simple algorithm for bounds consistency of the alldifferent constraint", *Proceedings of the Eighteenth International Joint Conference on Artificial Intelligence (IJCAI 2003)*, 245–249, [https://www.ijcai.org/Proceedings/03/Papers/036.pdf](https://www.ijcai.org/Proceedings/03/Papers/036.pdf). Definition 1 (domain and interval support), Definition 2 (bounds, range and domain consistency) and Example 1, §2, pp. 245–246.
- C.-G. Quimper, A. López-Ortiz, P. van Beek and A. Golynski, "Improved algorithms for the global cardinality constraint", *Principles and Practice of Constraint Programming – CP 2004*, Lecture Notes in Computer Science 3258 (2004), 542–556, doi:10.1007/978-3-540-30201-8_40. Definitions 1 and 2, §2.
- C. Bessiere, G. Katsirelos, N. Narodytska, C.-G. Quimper and T. Walsh, "Decompositions of all different, global cardinality and related constraints", *Proceedings of the Twenty-First International Joint Conference on Artificial Intelligence (IJCAI 2009)*, 419–423, [https://www.ijcai.org/proceedings/2009/77](https://www.ijcai.org/proceedings/2009/77). §2 (DC, BC, RC) and the example of §3, arXiv:0905.3755v1, [https://arxiv.org/abs/0905.3755v1](https://arxiv.org/abs/0905.3755v1).
