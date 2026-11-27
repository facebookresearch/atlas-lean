# Executing a commutative-machine instruction

Copies and operations execute as in CODE GENERATION WITH UNLIMITED REGISTERS. A reversed operation $r_a \leftarrow r_b \mathbin{\mathrm{op}} r_a$ is allowed when $r_b$ holds a vertex $u$ and $r_a$ holds a vertex $w$ such that, for some vertex $v$, $(v, u)$ is in $L$ and $(v, w)$ is in $R$; it puts $v$ into $r_a$ and leaves the other registers unchanged.
