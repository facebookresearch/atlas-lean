# One round of counter comparison

For stacks $a, b, t_a, t_b$, symbols $u_{t_a}$ of stack
$t_a$ and $u_{t_b}$ of stack $t_b$, and labels $\mathit{self}$, $\mathit{lt}$, $\mathit{eq}$ and
$\mathit{gt}$, this machine statement pops stack $a$ and then stack $b$; after each pop it stores
in the state whether the pop found a symbol and branches on it. If both pops found a symbol, it
pushes $u_{t_a}$ onto $t_a$, then $u_{t_b}$ onto $t_b$, and goes to $\mathit{self}$. If only the
pop of $a$ found a symbol, it pushes $u_{t_a}$ onto $t_a$ and goes to $\mathit{gt}$; if only the
pop of $b$ found one, it pushes $u_{t_b}$ onto $t_b$ and goes to $\mathit{lt}$; if neither did,
it goes to $\mathit{eq}$.
