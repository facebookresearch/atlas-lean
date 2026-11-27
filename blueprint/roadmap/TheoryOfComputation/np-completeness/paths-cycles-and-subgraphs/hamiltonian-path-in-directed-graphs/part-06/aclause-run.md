# HAMPATH emitter, phase A: one clause

Notation: $\mathrm{name}(x)$ is the canonical
binary encoding of $x \in \mathbb{N}$ as name-bit symbols; a literal $\ell = (x, p)$ has tokens
$\mathrm{name}(x)$ followed by the polarity marker $\mathrm{lit}(p)$ and reversed tokens
$r_\ell$, namely $\mathrm{lit}(p)$ followed by the reverse of $\mathrm{name}(x)$;
$\mathrm{vstk}(\mathit{vs})$ is the list of the names of the entries of a list $\mathit{vs}$ of
naturals, each followed by the separator $\mathrm{cl}$; and $\mathrm{ins}(x, \mathit{vs})$ is
$\mathit{vs}$ if $x$ occurs in $\mathit{vs}$ and $\mathit{vs}$ with $x$ added at the front
otherwise. Let $L_b \in \mathbb{N}$ and let $C$ be a clause with literals $\ell_1, \dots, \ell_k$
and variables $x_1, \dots, x_k$. The tokens of $C$ are the concatenated tokens of
$\ell_1, \dots, \ell_k$ followed by $\mathrm{cl}$, and its reversed tokens $r_C$ are
$\mathrm{cl}$ followed by the concatenation of $r_{\ell_k}, \dots, r_{\ell_1}$. Let $R$ be a list
of symbols that is empty or starts with $\mathrm{cl}$, let $\mathit{vs}$ be a list of naturals
with $|\mathrm{vstk}(\mathit{vs})| + |r_C| \le L_b$, and let $s$ be a quiescent state of the
HAMPATH emitter whose stack $T$ is $r_C$ followed by $R$, whose stack $V$ is
$\mathrm{vstk}(\mathit{vs})$ and whose stacks $W$ and $X$ are empty. Then for every value $v$ of
the machine's Boolean variable there is a value $v'$ such that the emitter goes in at most
$|r_C|(8L_b + 12)$ steps from label $\mathrm{a0}$, variable $v$ and the stacks of $s$ to label
$\mathrm{a0}$, variable $v'$ and the stacks of the state obtained from $s$ by setting $T$ to
$R$, $F$ to the tokens of $C$ followed by the old contents of $F$, and $V$ to
$\mathrm{vstk}(\mathrm{ins}(x_1, \dots \mathrm{ins}(x_k, \mathit{vs}) \dots))$, and by
increasing the clause count by $1$ and the triple clause count by $3$.
