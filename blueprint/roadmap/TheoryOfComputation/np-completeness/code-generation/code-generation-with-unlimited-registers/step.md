# Executing an instruction

Executing $r_a \leftarrow r_b$ on register contents $s$ copies the content of $r_b$ into $r_a$. Executing $r_a \leftarrow r_a \mathbin{\mathrm{op}} r_b$ is allowed when $r_a$ holds a vertex $u$ and $r_b$ holds a vertex $w$ such that, for some vertex $v$, $(v, u)$ is in $L$ and $(v, w)$ is in $R$; it puts $v$ into $r_a$ and leaves the other registers unchanged.
