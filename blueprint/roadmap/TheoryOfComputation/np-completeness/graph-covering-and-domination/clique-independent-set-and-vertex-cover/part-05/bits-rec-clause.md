# Pair bits of a leading clause

Let $C$ be a clause and $\varphi$ a CNF formula. Let
$O_\varphi$ be the list of literal occurrences of $\varphi$ (clause index, variable, polarity),
with every clause index increased by $1$. Then the row-by-row pair bits of the list made of the
literals of $C$, each with clause index $0$, followed by $O_\varphi$, are the rows pushed for the
literals of $C$ walked above a clause marker and the items of $\varphi$, followed by the
row-by-row pair bits of $O_\varphi$.
