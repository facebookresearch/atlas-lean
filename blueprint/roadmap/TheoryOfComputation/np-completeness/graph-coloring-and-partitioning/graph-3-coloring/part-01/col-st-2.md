# The SAT-to-3-COLOR graph construction

For a CNF formula $\varphi$, start from the state
whose next free vertex is $3$, with no earlier occurrences and with emitted edges $(0, 1)$,
$(0, 2)$, $(1, 2)$ (the palette triangle on the vertices $0$, $1$, $2$), and process the
clauses of $\varphi$ one at a time, from the last clause to the first. The result is the final
state.
