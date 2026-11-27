# Well-formed MPM FLOW SHOP, OUT-TREE, MAXIMUM LATENESS (FMPM|outtree; p_ij = 1|L_max) instances

Well-formedness of an instance: the machine environment is well formed, there is at least one
job (so that `L_max = max_i (C_i - d_i)` is defined), the listed pairs describe a precedence
relation on the jobs, and it is an out-tree (every job has at most one immediate predecessor).
