# The 3SAT emitter processes a whole formula

Let $\varphi = C_1 \cdots C_m$ be a CNF
formula, $u = \sum_{i=1}^{m} \max(|C_i| - 1, 0)$ the number of fresh variables its 3SAT
translation uses, $Z_b \ge u$ a natural number, $R$ a token list that is empty or starts with a
clause token, $o$ an output bit list and $v$ a flag. Let $T$ be the token list
$\mathrm{clRev}(C_m) \cdots \mathrm{clRev}(C_1)$, where $\mathrm{clRev}(C)$ is the list of tokens
of $C$ as they lie on the token stack, and let $D_1, \dots, D_k$ be the clauses of the 3SAT
translation $\mathrm{to3}(\varphi)$. Then there is a flag $v'$ such that the 3SAT emitter machine,
started at its start label with flag $v$, token stack $T$ followed by $R$, output stack $o$,
fresh counter $0$, clause count $0$ and empty scratch counters, reaches in at most
$|T| \cdot (6 Z_b + 15)$ steps its start label with flag $v'$, token stack $R$, output stack
$\mathrm{enc}(D_1) \cdots \mathrm{enc}(D_k)$ followed by $o$, fresh counter $u$, clause count $k$
and empty scratch counters, where $\mathrm{enc}$ is the binary clause encoding.
