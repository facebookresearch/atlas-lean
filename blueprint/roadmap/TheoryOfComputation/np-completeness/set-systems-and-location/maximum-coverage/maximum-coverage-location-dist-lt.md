# Shortest-route distance to a point of a network below a radius

The shortest-route distance from vertex $v$ to the point $x = (a, b, t)$ is less than $r$: some walk reaches $a$ with total length plus $t$ less than $r$, or reaches $b$ with total length plus $d(\{a, b\}) - t$ less than $r$. An edge's length is read from the first entry of the edge list with the same endpoints, and is $0$ when no entry has them. A vertex with no listed customer data has gain $0$ and radius $0$.
