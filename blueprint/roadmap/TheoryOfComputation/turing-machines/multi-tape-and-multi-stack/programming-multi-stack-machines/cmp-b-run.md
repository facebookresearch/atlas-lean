# Correctness of the bit-block comparison

Suppose the program has at label $\ell$ the
bit-block comparison statement of stacks $a$ and $b$ (decoders $d_a$, $d_b$) with scratch stacks
$t_a$ and $t_b$ (encoders $e_a$, $e_b$), loop label $\ell$, equality label $\ell_=$ and mismatch
label $\ell_{\ne}$, and that $a$, $b$, $t_a$, $t_b$ are pairwise distinct. Let $u$ and $w$ be bit
strings, and take a configuration at label $\ell$, with any state, in which stack $a$ holds a
list $X$ on top of $A$ and stack $b$ holds a list $Y$ on top of $B$, where $X$ is the bit block
$u$ under $d_a$, $Y$ is the bit block $w$ under $d_b$, $A$ ends a bit block under $d_a$ and $B$
ends a bit block under $d_b$. Then there is a common prefix $c = c_1 \dots c_m$ of $u$ and $w$,
after which $u$ and $w$ do not continue with the same bit, such that in exactly $m + 1$ steps the
program reaches a configuration, with some state, at label $\ell_=$ if $u = w$ and at label
$\ell_{\ne}$ otherwise, in which stack $a$ holds $X$ without its first $m$ symbols on top of $A$,
stack $b$ holds $Y$ without its first $m$ symbols on top of $B$, stack $t_a$ holds
$e_a(c_m), \dots, e_a(c_1)$ on top of its old contents, stack $t_b$ holds
$e_b(c_m), \dots, e_b(c_1)$ on top of its old contents, and every other stack is unchanged.
