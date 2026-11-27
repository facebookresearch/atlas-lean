# KT complexity and the minimum KT problem MKTP

KT complexity charges a description both its length and the time a universal machine needs to print any single bit of the string from it. MKTP asks whether $\mathrm{KT}(x)\le\theta$. Up to polynomial factors, the KT complexity of a truth table is its circuit size.

Fix once and for all an *efficient* universal Turing machine $U$ with random access to a description $d$ (and, in relativized versions, to an oracle $A$): it simulates every machine $M$ with logarithmic time overhead and linear space overhead, so that a run of $M$ in time $t$ and space $s$ costs $U$ time $O(t\log t)$ and space $O(s)$, the constants depending on $M$. Universality alone is not enough: a universal machine that idles for a long time before answering still describes every string, but breaks the time-bounded estimates below. For $x\in\{0,1\}^*$ set $x_{|x|+1}=*$ and

$$\mathrm{KT}(x)=\min\{|d|+t : \forall b\in\{0,1,*\}\ \forall i\le |x|+1,\ U^{d}(i,b) \text{ accepts within } t \text{ steps iff } x_i=b\}.$$

The *minimum KT problem* is $\mathrm{MKTP}=\{(x,\theta) : \mathrm{KT}(x)\le\theta\}$, and for a threshold $\theta:\mathbb{N}\to\mathbb{N}$, $\mathrm{MKTP}[\theta]=\{x : \mathrm{KT}(x)\le\theta(|x|)\}$. The set of *KT-random strings* is $R_{\mathrm{KT}}=\{x : \mathrm{KT}(x)\ge |x|/2\}$; any threshold $|x|^{\varepsilon}$ with $0<\varepsilon<1$ gives the same results. Relativized versions $\mathrm{KT}^A$ give this $U$ random access to an oracle $A$. The space-bounded measure uses the same machine: $\mathrm{KS}(x)=\min\{|d|+s : U(d)=x \text{ in space at most } s\}$, and $\mathrm{KS}^A$ is its relativization. Finally, $K_U(x)$ is the least $|d|$ over the descriptions $d$ allowed in the definition of $\mathrm{KT}(x)$, with no bound on the time: a bitwise, time-unbounded complexity on the same machine $U$. It is a different object from the whole-output Kolmogorov complexity $K$ of the linked page, which minimizes over programs printing all of $x$ for a separately fixed description method.

Basic facts stated in the sources:

- $\log|x|\le\mathrm{KT}(x)\le |x|+O(\log|x|)$, and $K_U(x)\le\mathrm{KT}(x)$, since dropping the time charge from a KT description leaves a $K_U$ description.
- For $x$ of length $2^n$ read as a truth table, with $\mathrm{SIZE}(x)$ the number of gates of the smallest fan-in-two circuit computing it: $\mathrm{SIZE}(x)=O(\mathrm{KT}(x)\log\mathrm{KT}(x))$ and $\mathrm{KT}(x)=O(\mathrm{SIZE}(x)^2+\log|x|)$.
- Relative to any oracle $A$, $\mathrm{SIZE}^A(x)$ and $\mathrm{KT}^A(x)$ are polynomially related when the size of an $A$-oracle circuit is its number of input gates plus its number of connections; this charges every oracle query its length.
- Levin's measure is KT relative to E: if $A$ is complete for E under linear-time reductions then $\mathrm{Kt}=\Theta(\mathrm{KT}^A)$; if $B$ is complete for $\mathrm{DSPACE}(n)$ under linear-time reductions then $\mathrm{KS}=\Theta(\mathrm{KT}^B)$.
- $R_{\mathrm{KT}}\in\mathrm{coNP}$.

## Expansion

The bitwise convention is what allows sublinear running times: a description of a circuit for $i\mapsto x_i$ has length about its size times its logarithm and is evaluated in polynomial time, which gives the upper bound on KT; conversely a description and machine that print each bit within $t$ steps unroll into a circuit of size polynomial in $|d|+t$. Unlike Levin's Kt, the time enters additively rather than logarithmically, which makes MKTP an NP problem tied to circuit size.

## Depends on

- [Kolmogorov complexity](../../../kolmogorov-complexity/k.md)
- [Time-bounded Kolmogorov complexity K^t and Levin's Kt](../../../kolmogorov-complexity/time-bounded-kolmogorov-complexity/time-bounded-kolmogorov-complexity-and-levin-kt.md)
- [Circuit complexity of a Boolean function and truth tables](../../minimum-circuit-size-problem/circuit-complexity-of-a-boolean-function.md)
- [Oracle circuits and local circuit classes](../../hardness-magnification/oracle-circuits-and-local-circuit-classes.md)
- [The class E](../../../complexity-classes/time-and-space-complexity-classes/e.md)
- [Deterministic space classes on multi-tape machines](../../../complexity-classes/time-and-space-classes-on-multi-tape-machines/dspace.md)
- [The class coNP](../../../complexity-classes/the-classes-p-np-and-conp/co-np.md)

## Proof depends on

None.

## Sources

- Eric Allender, Harry Buhrman, Michal Koucký, Dieter van Melkebeek, Detlef Ronneburger, "Power from Random Strings", *SIAM Journal on Computing* 35(6), 2006, https://doi.org/10.1137/050628994 (Definitions 2, 3 and 6, Theorem 4 and the remarks after Definitions 2 and 6, numbering of the ECCC TR02-028 revision 1 edition; Proposition 5 and Theorem 11 of the journal version for the efficient universal machine and the oracle circuit-size relation).
- Eric Allender, Joshua A. Grochow, Dieter van Melkebeek, Cristopher Moore, Andrew Morgan, "Minimum Circuit Size, Graph Isomorphism, and Related Problems", *SIAM Journal on Computing* 47(4), 2018, https://doi.org/10.1137/17m1157970, arXiv:1710.09806v1 (Definition 2 and the paragraph after it).
- Shuichi Hirahara, Rahul Santhanam, "On the Average-Case Complexity of MCSP and Its Variants", *Computational Complexity Conference (CCC)*, 2017, https://doi.org/10.4230/LIPIcs.CCC.2017.7 (Definitions 8 to 10).
- Mahdi Cheraghchi, Shuichi Hirahara, Dimitrios Myrisiotis, Yuichi Yoshida, "One-Tape Turing Machine and Branching Program Lower Bounds for MCSP", *Theory of Computing Systems*, 2022, https://doi.org/10.1007/s00224-022-10113-9; theorem numbers from the conference version, *Symposium on Theoretical Aspects of Computer Science (STACS)*, 2021, https://doi.org/10.4230/LIPIcs.STACS.2021.23 (Definition 24, proof of Theorem 26 and its footnote 6, for $K_U(x)\le\mathrm{KT}(x)$).
- Eric Allender, Dieter van Melkebeek, "A Comment Regarding KT and Circuit Size", note, https://people.cs.rutgers.edu/~allender/papers/clarification.pdf (the circuit-size convention for the journal Theorem 11).
