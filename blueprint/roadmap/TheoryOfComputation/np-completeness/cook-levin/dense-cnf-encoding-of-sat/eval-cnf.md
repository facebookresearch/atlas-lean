# Single-pass evaluation of a dense CNF encoding

The scan $E(r, u, v, f)$ takes the formula
bits $r$ still to be read, the assignment bits $u$ not yet used by the current clause, the bits
$v$ already used by it (most recent first) and a boolean $f$ recording whether the current clause
is already satisfied; write $x u'$ for the list with first bit $x$ followed by the list $u'$. It
reads $r$ two bits at a time; let $r'$ be the bits after the pair read. On $00$ (end of clause)
the result is $f \wedge E(r', \overline{v}\,u, [\,], \mathrm{false})$, where $\overline{v}\,u$ is
the reversal of $v$ followed by $u$. On $01$ (an empty slot) the result is $E(r', u', x v, f)$
when $u = x u'$, and $E(r', [\,], v, f)$ when $u$ is empty. On $1s$ (a literal with sign bit $s$)
the result is $E(r', u', x v, f \vee (x = \neg s))$ when $u = x u'$, and $E(r', [\,], v, f)$
when $u$ is empty. When fewer than two bits remain, the result is true.

The scan mirrors the verifier machine step by step.
