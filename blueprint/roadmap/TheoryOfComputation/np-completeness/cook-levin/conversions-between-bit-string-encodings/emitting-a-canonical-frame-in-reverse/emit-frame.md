# Reversed self-delimiting frame emitter

Write $1$ for true and $0$ for false. Consider a multi-stack Turing machine with Boolean internal state, two stacks
$a$ and $b$, a partial decoder $d$ sending each symbol of stack $a$ to a bit or to nothing, a map $g$ from bits to
symbols of stack $b$, and labels self and next. The frame-emitting statement does the following: if the top symbol
of stack $a$ is decoded by $d$ to a bit $e$, pop it, set the internal state to $e$, push $g(1)$ and then $g(e)$
onto stack $b$, and go to self; if stack $a$ is empty or its top symbol is not decoded to a bit, set the internal
state to $0$, push $g(0)$ onto stack $b$ and go to next.

When $a \ne b$, repeating it turns a block $p$ of bits on $a$ into the framed form $1 p_1 \cdots 1 p_m 0$ of $p$, written reversed
onto $b$.
