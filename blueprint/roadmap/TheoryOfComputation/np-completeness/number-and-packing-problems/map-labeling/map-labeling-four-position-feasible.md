# Feasible MAP LABELING WITH FOUR POSITIONS instances

A MAP LABELING WITH FOUR POSITIONS instance with points $(x_j, y_j)$ and $\sigma = p / q$ is
feasible when some choice of a corner $(a_j, b_j) \in \{0, 1\}^2$ for each point makes the
labels pairwise non-overlapping, where the label of point $j$ is the $\sigma \times \sigma$
square with lower-left corner $(x_j - a_j \sigma, y_j - b_j \sigma)$. Scaled by $q$, the labels
of distinct points $j$ and $k$ do not overlap exactly when $|q(x_j - x_k) - p(a_j - a_k)| \ge p$
or $|q(y_j - y_k) - p(b_j - b_k)| \ge p$; labels may touch.
