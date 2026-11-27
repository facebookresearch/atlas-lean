# Evaluating a circuit

Given an assignment of booleans to the variables and a list of gates
$g_1, \dots, g_m$, circuit evaluation returns the list $(v_1, \dots, v_m)$ of gate values, where
$v_k$ is the value of the gate $g_k$ under the assignment and the earlier values
$(v_1, \dots, v_{k-1})$.
