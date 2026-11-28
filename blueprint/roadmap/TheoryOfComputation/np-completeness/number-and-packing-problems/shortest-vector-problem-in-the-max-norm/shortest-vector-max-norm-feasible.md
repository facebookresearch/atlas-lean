# Feasible instances of SHORTEST VECTOR PROBLEM IN THE MAX NORM

An instance of SHORTEST VECTOR PROBLEM IN THE MAX NORM with $k$ stored rows and bound $K$ is feasible when some nonzero integer vector $x = (x_0, \dots, x_{k-1})$ gives, with $M$ the $k \times k$ [matrix of the instance](basis-matrix.md), a vector $v = x M$ whose coordinates

$$
v_j = \sum_{a < k} x_a \, M_{a j}, \qquad 0 \le j < k,
$$

all have absolute value at most $K$. Only the first $k$ coordinates of each stored row take part, missing coordinates count as $0$, and an instance with no stored rows is not feasible. Feasibility does not include well-formedness; the decision problem requires both. For a [well-formed](well-formed.md) instance, $v = x_1 v_1 + \dots + x_k v_k$ is a nonzero combination of the basis vectors and the condition is $\lVert v \rVert_\infty \le K$.
