# Crossing sequences of single-tape Turing machines

For a single-tape Turing machine $M$, an input $w$ and a boundary $i$ between tape cells $i$ and $i+1$, the **crossing sequence** $\mathrm{CS}_M(w,i)$ is the finite list of states in which $M$ crosses that boundary (in either direction) during its run on $w$. The running time is at least the total length $\sum_i|\mathrm{CS}_M(w,i)|$. **Cut-and-paste lemma**: if $M$ accepts $uv$ and $u'v'$ and $\mathrm{CS}_M(uv,|u|)=\mathrm{CS}_M(u'v',|u'|)$, then $M$'s runs on $uv'$ and $u'v$ have the same left and right behaviour, so $M$ accepts $uv'$ iff it accepts $uv$.

## Depends on

- [Polynomial time on single-tape machines](../../../complexity-classes/polynomial-time-on-single-tape-machines/single-tape-p.md)

## Sources

- F. C. Hennie, "One-tape, off-line Turing machine computations", Information and Control 8(6), 1965.
- Kojiro Kobayashi, "On proving time constructibility of functions", Theoretical Computer Science 35, 1985.
