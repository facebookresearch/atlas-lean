# Crossing sequences of single-tape Turing machines

For a single-tape Turing machine $M$, an input $w$ and a boundary $i$ between tape cells $i$ and $i+1$, the **crossing sequence** $\mathrm{CS}_M(w,i)$ is the finite list of states in which $M$ crosses that boundary (in either direction) during its run on $w$. The running time is at least the total length $\sum_i|\mathrm{CS}_M(w,i)|$. **Cut-and-paste lemma**: if $M$ halts on $uv$ and on $u'v'$ and $\mathrm{CS}_M(uv,|u|)=\mathrm{CS}_M(u'v',|u'|)$, then on $uv'$ the machine behaves to the left of the boundary as on $uv$ and to its right as on $u'v'$ (and symmetrically for $u'v$); in particular, if $M$ accepts both $uv$ and $u'v'$, it accepts $uv'$ and $u'v$.

## Depends on

- [Polynomial time on single-tape machines](../../../complexity-classes/polynomial-time-on-single-tape-machines/single-tape-p.md)

## Sources

- F. C. Hennie, "One-tape, off-line Turing machine computations", Information and Control 8(6), 553–578, 1965 (crossing sequences and the cut-and-paste argument).
- Kojiro Kobayashi, "On the structure of one-tape nondeterministic Turing machine time hierarchy", Theoretical Computer Science 40(2–3), 175–193, 1985, Theorem 3.3 (time $o(n\log n)$ forces bounded crossing sequences).
