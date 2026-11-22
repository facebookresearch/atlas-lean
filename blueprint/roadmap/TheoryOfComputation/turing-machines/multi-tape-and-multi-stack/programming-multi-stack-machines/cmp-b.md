# Bit-block comparison statement

Let $a$ and $b$ be stacks with decoders $d_a$ and $d_b$
that read each symbol either as a bit or as a marker, let $t_a$ and $t_b$ be scratch stacks with
bit encoders $e_a$ and $e_b$, and let $\ell$, $\ell_=$ and $\ell_{\ne}$ be labels. The comparison
statement with loop label $\ell$ performs one round of comparison: if the tops of $a$ and $b$ are
the same bit $x$, it pops both, pushes $e_a(x)$ onto $t_a$ and $e_b(x)$ onto $t_b$, and goes to
$\ell$. Otherwise it changes no stack: it goes to $\ell_=$ if neither top is a bit (each of $a$
and $b$ is empty or has a marker on top), and to $\ell_{\ne}$ if the tops are different bits or
exactly one of them is a bit. It records its tests in the one-bit flag of the machine state.
