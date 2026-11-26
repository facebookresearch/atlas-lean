# K-FACILITY LOCATION is NP-complete

The [decision problem](k-facility-location-dec.md) K-FACILITY LOCATION belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Hardness comes from a special case: DOMINATING SET is the instance with $p(v, f) = 1$ when $f = v$ or $f$ is adjacent to $v$, $p(v, f) = 0$ otherwise, and $K = |V|$ (a dominating set of size at most $k \le |V|$ extends to one of size exactly $k$).

## Sources

- P. Crescenzi and V. Kann, *A compendium of NP optimization problems*, problem MAXIMUM K-FACILITY LOCATION.
- G. Cornuéjols, M. L. Fisher, and G. L. Nemhauser, "Location of bank accounts to optimize float: an analytic study of exact and approximate algorithms", Management Science 23 (1977), 789-810, doi:10.1287/mnsc.23.8.789.
