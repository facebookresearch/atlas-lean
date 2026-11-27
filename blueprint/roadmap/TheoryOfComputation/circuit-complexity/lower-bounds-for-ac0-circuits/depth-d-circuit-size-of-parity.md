# Depth-d circuit size of parity

Let $\mathrm{PARITY}_n$ be the parity of $n$ bits, and consider circuits of depth $d$ with unbounded fan-in AND and OR gates and inputs the variables and their
negations.

- (*Depth two.*) The depth-2 circuit complexity of $\mathrm{PARITY}_n$ and of its negation is exactly $2^{n-1}$: every DNF or CNF for $\mathrm{PARITY}_n$ has size at least
  $2^{n-1}$, and there are a DNF and a CNF of size $2^{n-1}$.
- (*Upper bound.*) For every $d \ge 2$, $\mathrm{PARITY}_n$ and its negation have depth-$d$ circuits of size $2^{O(n^{1/(d-1)})}$.
- (*Lower bound, Håstad.*) For every $d \ge 2$ there is $\varepsilon > 0$ such that $\mathrm{PARITY}_n$ has no depth-$d$ circuits of size $2^{\varepsilon n^{1/(d-1)}}$.

So the exponent $n^{1/(d-1)}$ is optimal up to the constant, and in particular parity is not in $\mathsf{AC}^0$.

## Depends on

- [Parity is not in AC0](parity-not-in-ac0.md)

## Proof depends on

- [Håstad's switching lemma](hastad-s-switching-lemma.md)

## Sources

- R. Williams, *CS294-152 Lower Bounds*, lecture notes "AC0 switching lemma", MIT, 2018, <https://people.csail.mit.edu/rrw/cs294-2018/ac0-switching-lemma.txt>: the theorem of Håstad, the depth-2 theorem with its proof, and the depth-$d$ upper bound with its construction.
