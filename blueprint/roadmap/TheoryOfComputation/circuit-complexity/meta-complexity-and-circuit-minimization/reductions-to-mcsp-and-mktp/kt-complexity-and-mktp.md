# KT complexity and the minimum KT problem MKTP

KT complexity charges a description both its length and the time a universal machine needs to print any single bit of the string from it. MKTP asks whether $\mathrm{KT}(x)\le\theta$. Up to polynomial factors, $\mathrm{KT}(x)+\log|x|$ is the circuit size of the truth table $x$, when size counts input gates plus connections.

All measures below use one model, that of the journal version of Allender, Buhrman, Koucký, van Melkebeek and Ronneburger: multi-tape Turing machines with random access to their input, to a description $d$ and, in relativized versions, to an oracle $A$, where a query beyond the end of a finite string is answered $*$. Fix once and for all an *efficient* universal machine $U$ with two work tapes, as in their Proposition 5: for every oracle machine $M$ there is a constant $c_M$ such that for every oracle $A$, description $d$ and input there is a description $d'$ with $|d'|\le|d|+c_M$ on which $U$ produces the output of $M$ with $d$, using time at most $c_Mt\log t$ and space at most $c_Ms$ when $M$ runs in time $t$ and space $s$, and time at most $c_Mt$ when $M$ is a two-tape machine. Their Definition 6 makes this efficiency part of universality; a universal machine that simulates more slowly still describes every string but changes the time-bounded estimates below. For $x\in\{0,1\}^*$ set $x_{|x|+1}=*$ and

$$\mathrm{KT}(x)=\min\{|d|+t : \forall i\le |x|+1,\ U^{d}(i) \text{ halts within } t \text{ steps with output } x_i\}.$$

This is the symbol-output convention of Cheraghchi, Hirahara, Myrisiotis and Yoshida: on every index, the end-marker position $|x|+1$ included, the run must halt by the deadline and print the correct symbol. The journal version of Allender et al. phrases its definitions by letting $U^d(i,b)$ accept iff $b=x_i$, and states that its results hold as well under this output convention.

The *minimum KT problem* is $\mathrm{MKTP}=\{(x,\theta) : \mathrm{KT}(x)\le\theta\}$, and for a threshold $\theta:\mathbb{N}\to\mathbb{N}$, $\mathrm{MKTP}[\theta]=\{x : \mathrm{KT}(x)\le\theta(|x|)\}$. The set of *KT-random strings* is $R_{\mathrm{KT}}=\{x : \mathrm{KT}(x)\ge |x|/2\}$; any threshold $|x|^{\varepsilon}$ with $0<\varepsilon<1$ gives the same results. The relativized measure $\mathrm{KT}^A$ replaces $U^d(i)$ by $U^{A,d}(i)$. The same machine and convention give the bitwise measures of the journal version: $\mathrm{Kt}^A(x)=\min\{|d|+\log t : \forall i\le|x|+1,\ U^{A,d}(i) \text{ halts within } t \text{ steps with output } x_i\}$ and $\mathrm{KS}^A(x)=\min\{|d|+s : \forall i\le|x|+1,\ U^{A,d}(i) \text{ halts using space at most } s \text{ with output } x_i\}$, with $\mathrm{Kt}=\mathrm{Kt}^{\emptyset}$ and $\mathrm{KS}=\mathrm{KS}^{\emptyset}$. This bitwise Kt agrees with Levin's whole-output Kt of the linked page up to an additive $O(\log|x|)$ term. Finally, $K_U(x)=\min\{|d| : \forall i\le|x|+1,\ U^{d}(i) \text{ halts with output } x_i\}$ is the bitwise, time-unbounded complexity on the same machine $U$. It is a different object from the whole-output Kolmogorov complexity $K$ of the linked page, which minimizes over programs printing all of $x$ for a separately fixed description method.

Basic facts stated in the sources:

- $\mathrm{KT}(x)\le |x|+O(\log|x|)$, and $K_U(x)\le\mathrm{KT}(x)$: a KT description halts with the correct symbol on every index, so it is also a $K_U$ description.
- Fix an oracle $A$, with $A=\emptyset$ for the unrelativized case. For $x$ of length $2^n$ read as a truth table, let $\mathrm{SIZE}^A(x)$ be the least size of a circuit with AND, OR, negation and $A$-oracle gates computing it, where the size of a circuit is its number of input gates plus its number of connections; the first term makes the size at least $n=\log|x|$, and the second charges every oracle query its length. With this convention there is a constant $c$, independent of $A$, such that $\mathrm{SIZE}^A(x)\le c\,\mathrm{KT}^A(x)^2(\mathrm{KT}^A(x)^2+\log|x|)$ and $\mathrm{KT}^A(x)\le c\,\mathrm{SIZE}^A(x)^2(\log\mathrm{SIZE}^A(x)+\log\log|x|)$. Hence $\mathrm{SIZE}^A(x)$ and $\mathrm{KT}^A(x)+\log|x|$ are polynomially related. Counting input gates matters: if size counts only connections, the all-zero strings have circuits of size $O(1)$, while $\mathrm{KT}^A(0^m)\ge\lfloor\log m\rfloor$ for infinitely many $m$.
- KT relative to suitable complete sets recovers Kt and KS: there are a set $A$ complete for E, a set $B$ complete for $\mathrm{DSPACE}(n)$ and a constant $c$ such that $\mathrm{Kt}(x)/c\le\mathrm{KT}^A(x)\le c\,\mathrm{Kt}(x)$ and $\mathrm{KS}(x)/c\le\mathrm{KT}^B(x)\le c\,\mathrm{KS}(x)$ for all $x$, with Kt and KS the bitwise measures above.
- $R_{\mathrm{KT}}\in\mathrm{coNP}$.

## Expansion

The bitwise convention is what allows sublinear running times. A circuit of size $m$ for $i\mapsto x_i$ on $n$ input bits has an encoding of length $O(m(\log m+\log n))$ from which a two-tape machine outputs each bit in time $O(m^2\log m+m\log n)$; since $U$ simulates two-tape machines with linear overhead, this gives the upper bound on KT. Conversely, unrolling a time-$t$ run of $U^d$ and replacing the finite description $d$ by a circuit of size $O(|d|+t)$ yields a circuit of size polynomial in $|d|+t$ and $\log|x|$ (specifically $c\,m^2(m^2+\log|x|)$ for $m=|d|+t$, matching the first inequality above). Unlike Levin's Kt, the time enters additively rather than logarithmically, which makes MKTP an NP problem tied to circuit size.

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

- Eric Allender, Harry Buhrman, Michal Koucký, Dieter van Melkebeek, Detlef Ronneburger, "Power from Random Strings", *SIAM Journal on Computing* 35(6), 2006, https://doi.org/10.1137/050628994 (journal version throughout: the machine model in Section 2.1 and before Proposition 3; Propositions 3 to 5; Definition 6; the remark after Definition 7 on the output convention; Definitions 8, 10, 12 and 15 with the remarks after Definitions 8 and 15; Theorem 11; Proposition 13; Theorem 14; Proposition 20).
- Eric Allender, Dieter van Melkebeek, "A Comment Regarding KT and Circuit Size", note, https://people.cs.rutgers.edu/~allender/papers/clarification.pdf (the size convention, input gates plus connections, under which both parts of the journal Theorem 11 hold, and the all-zero example).
- Mahdi Cheraghchi, Shuichi Hirahara, Dimitrios Myrisiotis, Yuichi Yoshida, "One-Tape Turing Machine and Branching Program Lower Bounds for MCSP", *Theory of Computing Systems*, 2022, https://doi.org/10.1007/s00224-022-10113-9; theorem numbers from the conference version, *Symposium on Theoretical Aspects of Computer Science (STACS)*, 2021, https://doi.org/10.4230/LIPIcs.STACS.2021.23 (Definition 24 and footnote 6, for the symbol-output convention and $K_U(x)\le\mathrm{KT}(x)$).
- Shuichi Hirahara, Rahul Santhanam, "On the Average-Case Complexity of MCSP and Its Variants", *Computational Complexity Conference (CCC)*, 2017, https://doi.org/10.4230/LIPIcs.CCC.2017.7 (Definitions 8 to 10, which use the same symbol-output convention).
