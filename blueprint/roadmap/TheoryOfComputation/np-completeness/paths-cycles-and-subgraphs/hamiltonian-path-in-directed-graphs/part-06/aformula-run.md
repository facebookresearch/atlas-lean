# HAMPATH emitter, phase A: the clauses of a formula

Notation: $\mathrm{name}(x)$ is the
canonical binary encoding of $x \in \mathbb{N}$ as name-bit symbols; a literal $\ell = (x, p)$
has tokens $\mathrm{name}(x)$ followed by the polarity marker $\mathrm{lit}(p)$; a clause $C$
with literals $\ell_1, \dots, \ell_k$ has tokens the concatenated tokens of
$\ell_1, \dots, \ell_k$ followed by the separator $\mathrm{cl}$, and reversed tokens $r_C$,
namely $\mathrm{cl}$ followed by, for $\ell = \ell_k, \dots, \ell_1$ in turn,
$\mathrm{lit}(p)$ and the reverse of $\mathrm{name}(x)$; $\mathrm{vstk}(\mathit{vs})$ is the
list of the names of the entries of a list $\mathit{vs}$ of naturals, each followed by
$\mathrm{cl}$; and $\mathrm{ins}(x, \mathit{vs})$ is $\mathit{vs}$ if $x$ occurs in
$\mathit{vs}$ and $\mathit{vs}$ with $x$ added at the front otherwise. Let $L_b \in \mathbb{N}$,
let $\varphi$ be a CNF formula with clauses $C_1, \dots, C_m$, whose tokens are the
concatenated tokens of $C_1, \dots, C_m$, let $y_1, \dots, y_n$ be the variables of the literals
of $\varphi$ in order of occurrence (with repetitions), let
$N = |r_{C_1}| + \dots + |r_{C_m}|$, and let $R$ be a list of symbols that is empty or starts
with $\mathrm{cl}$. Then for every list $\mathit{vs}$ of naturals with
$|\mathrm{vstk}(\mathit{vs})| + N \le L_b$, every quiescent state $s$ of the HAMPATH emitter
whose stack $T$ is the concatenation of $r_{C_m}, \dots, r_{C_1}$ followed by $R$, whose stack
$V$ is $\mathrm{vstk}(\mathit{vs})$ and whose stacks $W$ and $X$ are empty, and every value $v$
of the machine's Boolean variable, there is a value $v'$ such that the emitter goes in at most
$N(8L_b + 12)$ steps from label $\mathrm{a0}$, variable $v$ and the stacks of $s$ to label
$\mathrm{a0}$, variable $v'$ and the stacks of the state obtained from $s$ by setting $T$ to
$R$, $F$ to the tokens of $\varphi$ followed by the old contents of $F$, and $V$ to
$\mathrm{vstk}(\mathrm{ins}(y_1, \dots \mathrm{ins}(y_n, \mathit{vs}) \dots))$, and by
increasing the clause count by $m$ and the triple clause count by $3m$.
