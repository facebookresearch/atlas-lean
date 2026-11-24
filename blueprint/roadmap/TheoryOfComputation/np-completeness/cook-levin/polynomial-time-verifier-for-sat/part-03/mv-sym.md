# Moving a symbol between stacks

For stacks $a$ and $b$, a symbol $x$ and a map $f$ from
symbols to labels, this machine instruction pops the top of $a$ (if any), pushes $x$ onto $b$ and
goes to the label $f(x)$.
