# TERRAIN GUARDING is NP-complete

The TERRAIN GUARDING decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a 1.5-dimensional terrain $T$, that is, an $x$-monotone polygonal chain given by $n \ge 2$ vertices $v_1, \dots, v_n$ with $v_i = (x_i, y_i)$ and $x_1 < x_2 < \dots < x_n$, with an edge joining each pair $v_i, v_{i+1}$; a finite set $G$ of candidate guard points on the terrain; a finite set $N$ of points on the terrain; and a natural number $K$. Every coordinate of a vertex, a guard or a point of $N$ is rational and is given as a [rational code](rat-code.md): two natural numbers whose difference is the numerator, and a positive natural denominator. Question: is there a set of at most $K$ guards from $G$ such that every point of $N$ is seen by one of them? A point $p$ on the terrain sees a point $q$ on the terrain if the line segment $pq$ is never strictly below the terrain.

## Sources

- J. King and E. Krohn, "Terrain guarding is NP-hard", SIAM Journal on Computing 40(5) (2011), 1316-1339, doi:10.1137/100791506 (arXiv:0907.1280, Section 2: the reduction from planar 3-SAT is for the discrete terrain guarding problem, "where both the set of guards and the set of points to be guarded are a finite subset of the terrain").
