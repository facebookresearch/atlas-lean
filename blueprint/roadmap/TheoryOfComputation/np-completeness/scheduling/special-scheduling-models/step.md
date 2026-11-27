# Steps of the one-register machine

LOAD $v$ needs $v$ in memory and puts it in the register; STORE needs a vertex in the register and adds it to memory; OP $v$ needs a vertex $u$ in the register with $v \to u$ and every other successor of $v$ in memory, and replaces $u$ by $v$ in the register.
