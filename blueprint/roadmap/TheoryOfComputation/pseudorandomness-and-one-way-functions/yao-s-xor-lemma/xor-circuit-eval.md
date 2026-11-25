# Gate values of an encoded circuit

For a list $C$ of encoded gates and a list $x$ of
Booleans of length $\ell$, the gate values of $C$ on $x$ are obtained by decoding each pair of $C$
to a gate of a flat Boolean circuit on $\ell$ inputs and evaluating the decoded circuit with the
assignment that gives input $i$ the value $x_i$; the result lists the values of all gates in
order. A pair referring to an input index $i \ge \ell$ decodes to the constant false.
