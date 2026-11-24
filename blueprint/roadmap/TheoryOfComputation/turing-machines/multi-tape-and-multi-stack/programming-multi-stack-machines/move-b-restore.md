# Restoring a stack after a comparison

Let $t \ne a$ be stacks with decoders $d_t$ and
$d_a$ that read each symbol either as a bit or as a marker. Let $e_t$ be a bit encoder for $t$
that $d_t$ reads back ($d_t$ reads $e_t(x)$ as the bit $x$), and let $g_a$ be a bit encoder for
$a$ that inverts $d_a$ ($g_a(x) = s$ whenever $d_a$ reads the symbol $s$ as the bit $x$). Suppose
the program has at label $\ell$ the bit-block move statement from $t$ (decoder $d_t$) onto $a$
(re-encoding $g_a$) with loop label $\ell$ and exit label $\ell'$. Let $X$ be the bit block of a
bit string $u$ under $d_a$ and let $c = c_1 \dots c_m$ be a prefix of $u$. From a configuration
at label $\ell$, with any state, in which stack $t$ holds $e_t(c_m), \dots, e_t(c_1)$ on top of a
list $R$ that ends a bit block under $d_t$, and stack $a$ holds $X$ without its first $m$ symbols
on top of a list $A$, the program reaches in exactly $m + 1$ steps a configuration at label
$\ell'$, with some state, in which stack $t$ is $R$, stack $a$ holds $X$ on top of $A$, and every
other stack is unchanged.
