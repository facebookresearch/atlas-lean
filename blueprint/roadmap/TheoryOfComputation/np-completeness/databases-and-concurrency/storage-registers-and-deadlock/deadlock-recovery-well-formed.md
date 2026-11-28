# Well-formed instances of DEADLOCK RECOVERY

An instance of DEADLOCK RECOVERY is well-formed when every allocation and request vector has length $m$, the current allocations fit in the resources ($Σ_{q \in P} r_j(q) \le B_j$), and every process $p$ satisfies (a) $r_j(p) + a_j(p) \le B_j$ for every $j$, and (b) is blocked: for some $j$, $a_j(p) + Σ_{q \in P} r_j(q) > B_j$.
