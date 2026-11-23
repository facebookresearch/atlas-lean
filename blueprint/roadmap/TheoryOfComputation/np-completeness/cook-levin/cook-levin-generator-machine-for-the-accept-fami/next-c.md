# Next label after a clause of the accept generator

Let $n_1, g \in \mathbb{N}$; clauses are
emitted last first. After the code clause $u < n_1$ the generator goes to the halting label
$\mathrm{done}$ if $u = 0$, and otherwise to the first label $\mathrm{e00}$ of code clause
$u - 1$. After the cell clause $x < g$ it goes, if $x = 0$, to the start of the code chain (the
first label of code clause $n_1 - 1$, or $\mathrm{done}$ if $n_1 = 0$), and otherwise to the
first label of cell clause $x - 1$.
