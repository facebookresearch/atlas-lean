# QMA for promise problems

A pair $(\Pi_{\mathrm{yes}}, \Pi_{\mathrm{no}})$ of sets of
bitstrings is in QMA when there are polynomials $m$, $a$ and $s$ with natural-number coefficients
and a polynomial-time computable map sending each bitstring $x$ to a list of encoded 2-local
quantum gates such that, for every bitstring $x$, writing $N = |x| + m(|x|) + a(|x|)$: the list
has at most $s(|x|)$ gates, each well-formed on $N$ qubits; if $x \in \Pi_{\mathrm{yes}}$, some
state $\psi$ on $m(|x|)$ qubits with squared norm $1$ makes the acceptance probability of the
circuit, applied to the tensor product of the basis state of $x$, $\psi$ and the all-zero state
on $a(|x|)$ qubits, at least $2/3$; and if $x \in \Pi_{\mathrm{no}}$, every state $\psi$ on
$m(|x|)$ qubits with squared norm $1$ makes this acceptance probability at most $1/3$.

No condition is imposed on bitstrings outside $\Pi_{\mathrm{yes}} \cup \Pi_{\mathrm{no}}$.
