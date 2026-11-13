# Running a chain of copy sites in the HAMPATH emitter

Let $j_1, \dots, j_n$ be copy sites
chained from label $l_0$ to label $l$ with passed bit $b$. Then for every quiescent state $s$ and
every flag $v$ there is a flag $v'$ such that the emitter machine goes, in exactly as many steps as
the step count of $j_1, \dots, j_n$ at $s$, from label $l_0$ with flag $v$ and the stacks of $s$ to
label $l$ with flag $v'$ and the stacks of the state that differs from $s$ only in that the atoms
of $j_1, \dots, j_n$ at $s$, concatenated in this order, are appended to its edge bits.
