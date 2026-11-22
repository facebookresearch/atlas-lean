# Moving a walked name from $D$ to $E$

Write
$\langle \ell, v \mid t, o, a, d, e, c, n\rangle$ for the configuration of the SAT-to-CLIQUE
emitter at label $\ell$ with local bit $v$, stacks $T = t$, $O = o$, $A = a$, $D = d$, $E = e$,
empty scratch stacks $B$ and $X$, and $c$ and $n$ marks on the counters $C$ and $N$;
juxtaposition of lists is concatenation. Let $p, f$ be bits, $w$ a list of bits with $\bar w$ the
corresponding list of name-bit symbols, $R$ a list of symbols that is empty or does not start
with a name-bit symbol, and $t, o, a, e, c, n, v$ arbitrary. Then for some bit $v'$ the machine
goes in exactly $|w| + 1$ steps from
$\langle \mathsf{mvN}(p, f), v \mid t, o, a, \bar w R, e, c, n\rangle$ to
$\langle \mathsf{walk}(p, f), v' \mid t, o, a, R, \bar w^{\mathrm{rev}} e, c, n\rangle$, where
$\bar w^{\mathrm{rev}}$ is the reverse of $\bar w$.
