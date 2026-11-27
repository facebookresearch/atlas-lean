# HAMPATH emitter, phase A: searching the variable stack for a name

For $y \in \mathbb{N}$
write $\mathrm{name}(y)$ for the canonical binary encoding of $y$ as name-bit symbols, and for a
list $\mathit{vs}$ of naturals write $\mathrm{vstk}(\mathit{vs})$ for the variable stack: the
names of the entries of $\mathit{vs}$, each followed by the separator $\mathrm{cl}$. Let
$x \in \mathbb{N}$ and let $A$ be a list of symbols that is empty or does not start with a name
bit. Then for every list $\mathit{vs}$ of naturals, every Boolean $f$, every quiescent state $s$
of the HAMPATH emitter whose stack $F$ is $\mathrm{name}(x)$ followed by $A$, whose stack $V$ is
$\mathrm{vstk}(\mathit{vs})$ and whose stack $X$ is empty, and every value $v$ of the machine's
Boolean variable, writing $g$ for the Boolean that is true exactly when $f$ is true or $x$
occurs in $\mathit{vs}$, there is a value $v'$ such that the emitter goes in at most
$6|\mathrm{vstk}(\mathit{vs})| + 1$ steps from label $\mathrm{aw}(f)$, variable $v$ and the
stacks of $s$ to label $\mathrm{ab}(g)$, variable $v'$ and the stacks of the state obtained
from $s$ by emptying $V$ and replacing $W$ by the reverse of $\mathrm{vstk}(\mathit{vs})$
followed by the old contents of $W$.
