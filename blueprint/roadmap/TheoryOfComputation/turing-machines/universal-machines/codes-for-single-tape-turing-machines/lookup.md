# Table lookup of a code

For a code $c$ and numbers $q$ and $a$, the lookup of $c$ at
state $q$ and symbol $a$ is the entry in row $q$, column $a$ of the table of $c$: either a pair
$(q', s)$ of a next state and an action code, or no entry (halt). It is no entry when the
table has no row $q$ or that row has no column $a$.
