# A for loop over a counter reaches its exit

Let $M$ be a multi-stack machine whose states
carry a flag bit, with $\mathrm{tag}(\beta)$ the state storing the bit $\beta$; write $(\ell, v, S)$
for the configuration at label $\ell$ with state $v$ and stack contents $S$, and $u^m$ for a stack
holding exactly $m$ copies of the symbol $u$. Let $c \ne c'$ be stacks with a symbol $u$ of stack
$c$ and a symbol $u'$ of stack $c'$, and let $h, b, r, e$ be labels such that at $h$ the machine
runs the loop head on $c$ with index stack $c'$ (pop $c$; if a symbol was popped, push $u'$ onto
$c'$ and go to $b$, otherwise go to $r$), and at $r$ it runs the transfer that drains $c'$, pushing
one $u$ onto $c$ per popped symbol, and then goes to $e$. Let $n \in \mathbb{N}$, and let $P(i, S)$
be a predicate such that $P(i, S)$ implies $P(i, S')$ whenever $S$ and $S'$ agree on every stack
other than $c$ and $c'$. Assume that for every $i < n$ and all stack contents $S$ with $S_c =
u^{n-1-i}$, $S_{c'} = u'^{\,i+1}$ and $P(i, S)$, there are a state $v'$ and stack contents $S'$ such
that $M$ goes from $(b, \mathrm{tag}(\mathrm{true}), S)$ to $(h, v', S')$ in finitely many steps,
with $S'_c = S_c$, $S'_{c'} = S_{c'}$ and $P(i + 1, S')$. Then for every state $v$ and all stack
contents $S$ with $S_c = u^n$, $S_{c'}$ empty and $P(0, S)$, there are stack contents $S'$ such that
$M$ goes from $(h, v, S)$ to $(e, \mathrm{tag}(\mathrm{false}), S')$ in finitely many steps, with
$S'_c = u^n$, $S'_{c'}$ empty and $P(n, S')$.
