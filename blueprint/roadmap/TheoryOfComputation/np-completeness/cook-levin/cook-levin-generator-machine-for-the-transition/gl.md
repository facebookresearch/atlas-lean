# Labels of the clause-family generator

For $N, m \in \mathbb{N}$, a label is one of: a
precomputation stage; the head or the tail of the time loop; a stage of the multiplication
routine of a time step; for a situation $i < N$, one of three labels that start clause $i$, a
stage of the routine emitting literal $j$ of clause $i$ for some $j < m$, or the label that
finishes clause $i$; the label that ends a time step; or the final label $\mathsf{done}$, where a
successful run halts. There are finitely many labels; the generator uses $m$ equal to the number
of literals of a clause.
