# Start of the accept code chain

For a generator with $n_1$ code clauses, the code chain
starts at the entry label of code clause $n_1 - 1$ (the last one, as clauses are emitted last
first), or at the halting label $\mathrm{done}$ when $n_1 = 0$.
