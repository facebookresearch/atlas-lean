# Minimum-weight decoding of the toric code

Consider bit-flip errors on the [toric code](toric-code.md): an error $X^e$ for a set $e$ of edges. Its syndrome is the
set $D$ of faces $p$ with $B_p X^e = -X^e B_p$, the faces containing an odd number of edges of $e$ (the endpoints of the
dual chain of $e$, the defects). Given $D$, the minimum-weight decoder chooses a set $e'$ of edges of least size whose
set of odd faces is $D$, and applies $X^{e'}$; when several sets are minimal, one is chosen. Equivalently it pairs the
defects by a minimum-weight perfect matching, the weight of a pair being their distance on the dual lattice, and joins
each pair by a shortest dual path. Recovery succeeds when $e + e'$ is homologically trivial (the boundary of a set of faces), so that
$X^{e + e'}$ lies in the stabilizer, and fails when its total homology class is nonzero; two parallel winding loops
together bound a strip and do not cause failure. Phase-flip errors are decoded in the
same way using the vertex operators. When syndrome measurements are themselves faulty, a spatial matching of one round's defects
no longer works, since a single wrong readout produces an isolated apparent defect. Dennis, Kitaev, Landahl and Preskill
then work in a three-dimensional spacetime lattice, stated here for a finite record. Start from a code state with no
errors; before each of rounds $1, \dots, T$ every edge suffers a bit flip independently with probability $p$, and in each of
these rounds every face check is read out wrongly independently with probability $q$; round $T + 1$ is read out without
error, which closes the record at a temporal boundary. Write $m_\tau(f)$ for the measured syndrome of face $f$ in round
$\tau$, with $m_0 = 0$ for the error-free start. The vertices are the pairs $(f, \tau)$ with $1 \le \tau \le T + 1$, and the
detection events are the set $D$ of vertices with $m_\tau(f) \ne m_{\tau - 1}(f)$. A space-like edge joins $(f_1, \tau)$ and
$(f_2, \tau)$ for neighbouring faces and stands for a bit flip on their common edge before round $\tau$ ($\tau \le T$); a
time-like edge joins $(f, \tau)$ and $(f, \tau + 1)$ and stands for a wrong readout of $f$ in round $\tau$ ($\tau \le T$).
Then the fault chain $E$ has $\partial E = D$: a bit flip before round $\tau$ changes the syndrome of its two faces in that
round, and a wrong readout of $f$ in round $\tau$ toggles the two adjacent differences $m_\tau(f) - m_{\tau - 1}(f)$ and
$m_{\tau + 1}(f) - m_\tau(f)$; contributions add modulo $2$. In Dennis, Kitaev, Landahl and Preskill's complete history
the syndrome chain $S$ is the set of time-like links on which the measured syndrome is nontrivial, the decoder's input is
its boundary $\partial S$, not $S$ itself, and $\partial S = \partial E$. On the finite record this identification needs a
correction at the last slice, since a perfect final readout need not be trivial: if $S_{\mathrm{slab}}$ is the set of
time-like edges $(f, \tau)$–$(f, \tau + 1)$, $1 \le \tau \le T$, with $m_\tau(f)$ nontrivial, then
$D = \partial S_{\mathrm{slab}} + \iota_{T+1}(m_{T+1})$ over $\mathbb{F}_2$, where $\iota_{T+1}(m_{T+1})$ is the set of
vertices $(f, T + 1)$ with $m_{T+1}(f)$ nontrivial. With $T = 1$ and one bit flip between faces $a$ and $b$ before round
$1$, $D = \{(a, 1), (b, 1)\}$, while $\partial S_{\mathrm{slab}}$ has the four vertices $(a, 1), (b, 1), (a, 2), (b, 2)$.
The decoder uses $D$. For example, two consecutive wrong readouts of one check, with correct readouts around them and no data
error, give two adjacent time-like edges but only their two outer endpoints in $D$. The decoder chooses a chain $E'$ with
$\partial E' = D$ of least weighted length $H \log((1 - p)/p) + V \log((1 - q)/q)$, for $H$ space-like and $V$ time-like
edges and $0 < p, q < 1/2$, a finite minimum since the record is finite; when $p = 0$ or $q = 0$ the edges of that type are
not used. It then applies $X$ on the projection of the space-like edges of $E'$ onto the torus; the boundary of that
projection is the projection of $D$, which telescopes to the final syndrome $m_{T+1}$, so the correction returns the state
to the code space. Since $\partial(E + E') = 0$, $E + E'$ is a cycle, and the residual data error is the projection of its
space-like edges, a cycle on the torus. Decoding succeeds when that projection is homologically trivial and fails when
its total spatial homology class is nonzero; a cycle of $E + E'$ that winds around the torus does not by itself cause failure, since two parallel winding
loops bound a strip. A decoder that sees a finite record without a final error-free round needs its own rule at the last
round; Dennis, Kitaev, Landahl and Preskill treat that case separately, with chains closed relative to the final time
slice.

## Depends on

- [Toric code](toric-code.md)
- [Error syndrome of a stabilizer code](../stabilizer-formalism/error-syndrome.md)
- [Logical operators of the toric code](logical-operators-of-the-toric-code.md)

## Sources

- E. Dennis, A. Kitaev, A. Landahl and J. Preskill, *Topological quantum memory*, J. Math. Phys. 43 (2002), 4452–4505, arXiv:quant-ph/0110143, Section V.A, equations (44)–(46) (the weights and the minimal chain), Section V.B (success as $E_{\min}$ homologous to $E$, and failure bounded by the presence of a homologically nontrivial path in $E + E_{\min}$), Section IV.C (the syndrome chain $S$ as the time-like links on which the measured syndrome is nontrivial, and $\partial S = \partial E$ for the complete history), the opening of Section VI (the complete syndrome history assumed in Section V, which this page replaces by a finite record with an error-free final round so that the weighted minimum is finite) and Section VI.A (a finite record without that round, with chains closed relative to the final time slice).
