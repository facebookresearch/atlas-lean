# Emitter run over one literal occurrence

Write
$\langle \ell, v \mid t, o, a, d, e, c, n\rangle$ for the configuration of the SAT-to-CLIQUE
emitter at label $\ell$ with local bit $v$, stacks $T = t$, $O = o$, $A = a$, $D = d$, $E = e$,
empty scratch stacks $B$ and $X$, and $c$ and $n$ marks on the counters $C$ and $N$;
juxtaposition of lists is concatenation. Let $l = (x, p)$ be a literal, $R$ a list of symbols that
is empty or does not start with a name-bit symbol, $I$ a list of items, $o$ a list of bits,
$c, n \in \mathbb{N}$ and $v$ a bit. Let $\delta$ be the concatenation of the tokens of the items
of $I$, $\lambda$ the token list of $l$ as it lies on the token stack, $\rho$ the reverse of the
walk bits of $l$ with flag false over $I$, and $\delta'$ the concatenation of the tokens of the
item $l$ followed by those of $I$. Then for some bit $v'$ the machine goes in at most
$7|\delta| + 3|\mathrm{enc}(x)| + 7$ steps, where $\mathrm{enc}(x)$ is the binary encoding of $x$,
from $\langle \mathsf{lits}, v \mid \lambda R, o, [], \delta, [], c, n\rangle$ to
$\langle \mathsf{lits}, v' \mid R, \rho\, o, [], \delta', [], c, n + 1\rangle$.
