# Two-destination bit-block transfer

Consider a multi-stack Turing machine with Boolean internal state. Fix three stacks $a$, $b$, $c$, a partial
decoder $d$ sending each symbol of stack $a$ to a bit or to nothing, maps $g_b$ and $g_c$ from bits to symbols of
stacks $b$ and $c$, and labels self and next. The two-destination transfer statement does the following: if the
top symbol of stack $a$ is decoded by $d$ to a bit $e$, pop it, set the internal state to $e$, push $g_b(e)$ onto
stack $b$ and $g_c(e)$ onto stack $c$, and go to self; if stack $a$ is empty or its top symbol is not decoded to a
bit, set the internal state to $0$ (false) and go to next.

When $a$, $b$ and $c$ are pairwise distinct, repeating it pops a block of bits from $a$ onto both destinations,
reversing both copies.
