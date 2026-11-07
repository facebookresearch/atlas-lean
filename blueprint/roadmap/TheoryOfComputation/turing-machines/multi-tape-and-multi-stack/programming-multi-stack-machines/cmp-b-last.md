# Deciding step of the comparison

Suppose the program has at label $\ell$ the bit-block
comparison statement of stacks $a$ and $b$ (decoders $d_a$, $d_b$; scratch stacks arbitrary) with
loop label $\ell$, equality label $\ell_=$ and mismatch label $\ell_{\ne}$. From a configuration
at label $\ell$, with any state, in which the tops of $a$ and $b$ are not the same bit, the
program takes one step to a configuration with the same stacks and some state, at label $\ell_=$
if neither top is a bit (each of $a$ and $b$ is empty or has a marker on top) and at label
$\ell_{\ne}$ otherwise.
