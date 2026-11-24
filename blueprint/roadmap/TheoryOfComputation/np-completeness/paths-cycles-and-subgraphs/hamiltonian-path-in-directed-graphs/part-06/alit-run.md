# HAMPATH emitter, phase A: one literal

For $x \in \mathbb{N}$ write $\mathrm{name}(x)$
for the canonical binary encoding of $x$ as name-bit symbols. Let $\ell = (x, p)$ be a literal
with variable $x$ and polarity $p$: its tokens are $\mathrm{name}(x)$ followed by the polarity
marker $\mathrm{lit}(p)$, and its reversed tokens $r_\ell$ are $\mathrm{lit}(p)$ followed by the
reverse of $\mathrm{name}(x)$. For a list $\mathit{vs}$ of naturals write
$\mathrm{vstk}(\mathit{vs})$ for the names of the entries of $\mathit{vs}$, each followed by the
separator $\mathrm{cl}$, and $\mathrm{ins}(x, \mathit{vs})$ for $\mathit{vs}$ if $x$ occurs in
$\mathit{vs}$ and for $\mathit{vs}$ with $x$ added at the front otherwise. Let $R$ be a list of
symbols that is empty or does not start with a name bit, let $\mathit{vs}$ be a list of
naturals, and let $s$ be a quiescent state of the HAMPATH emitter whose stack $T$ is $r_\ell$
followed by $R$, whose stack $V$ is $\mathrm{vstk}(\mathit{vs})$ and whose stacks $W$ and $X$
are empty. Then for every value $v$ of the machine's Boolean variable there is a value $v'$ such
that the emitter goes in at most $8|\mathrm{vstk}(\mathit{vs})| + 4|r_\ell| + 8$ steps from
label $\mathrm{a0}$, variable $v$ and the stacks of $s$ to label $\mathrm{a0}$, variable $v'$
and the stacks of the state obtained from $s$ by setting $T$ to $R$, $F$ to the tokens of $\ell$
followed by the old contents of $F$, and $V$ to $\mathrm{vstk}(\mathrm{ins}(x, \mathit{vs}))$.
