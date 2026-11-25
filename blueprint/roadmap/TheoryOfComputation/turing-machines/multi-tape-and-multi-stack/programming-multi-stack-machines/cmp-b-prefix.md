# Comparison pops a common prefix

Suppose the program has at label $\ell$ the bit-block
comparison statement of stacks $a$ and $b$ (decoders $d_a$, $d_b$) with scratch stacks $t_a$ and
$t_b$ (encoders $e_a$, $e_b$) and loop label $\ell$, and that $a$, $b$, $t_a$, $t_b$ are pairwise
distinct. Let $p = p_1 \dots p_n$ be a bit string, and take a configuration at label $\ell$, with
any state, in which stack $a$ holds a list $X$ on top of $A$ and stack $b$ holds a list $Y$ on
top of $B$, where $X$ is the bit block $p$ under $d_a$ and $Y$ is the bit block $p$ under $d_b$.
Then in exactly $n$ steps the program reaches a configuration at label $\ell$, with some state,
in which stack $a$ is $A$, stack $b$ is $B$, stack $t_a$ holds $e_a(p_n), \dots, e_a(p_1)$ on top
of its old contents, stack $t_b$ holds $e_b(p_n), \dots, e_b(p_1)$ on top of its old contents,
and every other stack is unchanged.
