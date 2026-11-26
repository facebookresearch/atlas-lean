# Emitter run over a formula's clauses

Write
$\langle \ell, v \mid t, o, a, d, e, c, n\rangle$ for the configuration of the SAT-to-CLIQUE
emitter at label $\ell$ with local bit $v$, stacks $T = t$, $O = o$, $A = a$, $D = d$, $E = e$,
empty scratch stacks $B$ and $X$, and $c$ and $n$ marks on the counters $C$ and $N$;
juxtaposition of lists is concatenation. Let $L \in \mathbb{N}$, let $\varphi$ be a CNF formula
with clauses $C_1, \dots, C_m$ in order, let $R$ be a list of symbols that is empty or starts
with the clause marker, $o$ a list of bits and $v$ a bit. Let $\kappa_i$ be the token list of
$C_i$ as it lies on the token stack and $\tau = \kappa_m \cdots \kappa_1$. If $|\tau| \le L$,
then for some bit $v'$ the machine goes in at most $|\tau| (7L + 7)$ steps from
$\langle \mathsf{start}, v \mid \tau R, o, [], [], [], 0, 0\rangle$ to
$\langle \mathsf{start}, v' \mid R, \rho\, o, [], \delta, [], m, s\rangle$, where $\rho$ is the
row bits of $\varphi$, $\delta$ is the concatenation of the tokens of the items of $\varphi$ and
$s = |C_1| + \dots + |C_m|$ is the total number of literals of $\varphi$.
