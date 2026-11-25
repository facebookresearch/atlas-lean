# The 3SAT emitter processes one clause

Let $C$ be a clause, $Z_b$, $z$ and $c$ natural
numbers with $z + \mathrm{used}(C) \le Z_b$, where $\mathrm{used}(C) = \max(|C| - 1, 0)$, let $R$
be a token list that is empty or starts with a clause token, $o$ an output bit list and $v$ a
flag. Let $\mathrm{clRev}(C)$ be the tokens of $C$ as they lie on the token stack (a clause token,
then the tokens of its literals, last literal first), and let $D_1, \dots, D_k$ be the clauses of
$\mathrm{chain}(C, z)$. Then there is a flag $v'$ such that the 3SAT emitter machine, started at
its start label with flag $v$, token stack $\mathrm{clRev}(C)$ followed by $R$, output stack $o$,
fresh counter $z$, clause count $c$ and empty scratch counters, reaches in at most
$|\mathrm{clRev}(C)| \cdot (6 Z_b + 15)$ steps its start label with flag $v'$, token stack $R$,
output stack $\mathrm{enc}(D_1) \cdots \mathrm{enc}(D_k)$ followed by $o$, fresh counter
$z + \mathrm{used}(C)$, clause count $c + k$ and empty scratch counters, where $\mathrm{enc}$ is
the binary clause encoding.
