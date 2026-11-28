# Feasible instances of DEADLOCK RECOVERY

An instance of DEADLOCK RECOVERY is feasible when some set $A$ of processes of total cost at most $K$ can be aborted, returning their allocations, so that the remaining processes, in the order of some list $L$ that lists every process outside $A$ exactly once, can each be granted its request from the free resources, finish, and release its allocation. Resource bounds, allocations and requests that are not listed count as $0$.
