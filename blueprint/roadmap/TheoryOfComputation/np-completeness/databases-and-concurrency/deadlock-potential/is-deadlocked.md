# Deadlocked schedules

A partial schedule $\sigma$ is deadlocked when it is legal, some process has not executed all its steps, and for every such process $p$ its next step would exceed some resource bound: for some resource $j$, the amount $a_j$ of that step plus the usage of $j$ after all of $\sigma$ exceeds $B_j$.
