# The MAJSAT language

MAJSAT is the decision problem that accepts a bitstring $x$ exactly
when $x$ decodes, under the canonical bitstring encoding of pairs, to a pair $(u, \varphi)$ of a
bitstring $u$ and a CNF formula $\varphi$ such that, with $n = |u|$, every literal of $\varphi$
has variable index less than $n$, and more than half of the $2^n$ assignments
$a : \{0, \dots, n-1\} \to \{\mathrm{true}, \mathrm{false}\}$ satisfy $\varphi$, that is, twice
their number exceeds $2^n$. Only the length of $u$ matters, and a bitstring that does not decode
is rejected.
