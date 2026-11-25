# Well-formed MPT FLOW SHOP WITH TREE PRECEDENCE AND UNIT TIMES (FMPT|tree; p_ij = 1|L_max) instances

Well-formedness of an instance: there is at least one job, the machine environment is well
formed (`StagesWellFormed`), every job has `r` unit processing times (`UnitJobs`), the listed
arcs describe an acyclic precedence digraph on the jobs (`PrecWellFormed`), and its precedence
relation is a tree (`IsTreePrecedence`).
