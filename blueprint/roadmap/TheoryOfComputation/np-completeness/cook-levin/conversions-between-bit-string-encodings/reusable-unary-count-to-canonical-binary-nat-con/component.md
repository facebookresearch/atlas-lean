# Unary-to-binary converter as a host component

For a Boolean "framed", the unary-to-binary converter as a component machine: its stacks are the fifteen stacks
$X, O, A, H, N, M, C, S_1, S_2, Y, Z, T, L, R, R_t$ of the vertex-cover to subset-sum reduction machine (listed in
this order) with their alphabets, its labels are those of the [converter](lab.md) and its program is the
[converter program](prog.md) for that value of framed.

Its input is a unary counter of $n$ symbols, and the step bounds of the [framed](run-framed.md) and
[unframed](run-raw.md) runs are linear in $n$.
