# The inverse limit is closed

Let $I$ be a preordered set, let $(X_i)_{i \in I}$ be a
family of Hausdorff topological spaces, and for every $i \le j$ let $f_{ij} \colon X_j \to X_i$
be a continuous map. Then the inverse limit
$\{x \in \prod_{i \in I} X_i : f_{ij}(x_j) = x_i \text{ for all } i \le j\}$ is closed in the
product $\prod_{i \in I} X_i$.

Each equation $f_{ij}(x_j) = x_i$ cuts out a closed set because $X_i$ is Hausdorff, and the
limit is the intersection of all of them.
