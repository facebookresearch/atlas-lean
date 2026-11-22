# Indexed evaluation of a dense CNF encoding

The scan $I(r, a, j, f)$ takes the formula
bits $r$ still to be read, an assignment $a$ (a list of booleans), the position $j$ of the next
slot in the current clause and a boolean $f$ recording whether the current clause is already
satisfied. It reads $r$ two bits at a time; let $r'$ be the bits after the pair read. On $00$
(end of clause) the result is $f \wedge I(r', a, 0, \mathrm{false})$. On $01$ (an empty slot) the
result is $I(r', a, j + 1, f)$. On $1s$ (a literal with sign bit $s$) the result is
$I(r', a, j + 1, f')$, where $f'$ is true when $f$ is true, or when $j < |a|$ and the entry $a_j$
of $a$ (counting from $0$) equals $\neg s$.
When fewer than two bits remain, the result is true.
