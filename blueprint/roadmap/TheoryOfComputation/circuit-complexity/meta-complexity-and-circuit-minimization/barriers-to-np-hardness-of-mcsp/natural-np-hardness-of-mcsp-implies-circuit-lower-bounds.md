# Natural NP-hardness of MCSP implies circuit lower bounds for E

If SAT reduces to MCSP by a natural Karp reduction, then E contains functions outside P/poly infinitely often, and functions of circuit complexity $2^{\Omega(n)}$ infinitely often unless $\mathrm{NP}\subseteq\mathrm{SUBEXP}$.

Let $\mathrm{SUBEXP}=\bigcap_{\varepsilon>0}\mathrm{DTIME}(2^{n^{\varepsilon}})$. "Infinitely often" (i.o.) means for infinitely many input lengths.

**Theorem (Kabanets–Cai).** If MCSP is NP-hard under a natural reduction from SAT, then:

1. E contains a family of Boolean functions $f_n$ not in P/poly i.o.;
2. E contains a family of Boolean functions $f_n$ of circuit complexity $2^{\Omega(n)}$ i.o., unless $\mathrm{NP}\subseteq\mathrm{SUBEXP}$;
3. $\mathrm{BPP}\subseteq\mathrm{SUBEXP}$ i.o., and $\mathrm{BPP}=\mathrm{P}$ i.o. unless $\mathrm{NP}\subseteq\mathrm{SUBEXP}$;
4. $\mathrm{BPP}\ne\mathrm{E}$.

Item 4 corrects the statement of Corollary 19 as printed, "If MCSP is NP-hard under a natural reduction from SAT, then BPP ⊊ E": its proof puts BPP in SUBEXP at infinitely many lengths and diagonalizes against SUBEXP in E, which shows $\mathrm{E}\not\subseteq\mathrm{BPP}$, that is $\mathrm{BPP}\ne\mathrm{E}$, and not $\mathrm{BPP}\subseteq\mathrm{E}$.

## Expansion

A natural reduction maps formulas of size $n$ to truth tables on $k=O(\log n)$ variables with a size parameter $s_n$ depending only on $n$. If $s_n\le(\log n)^c$ for a fixed $c$, all produced instances are solvable in time $n^{\mathrm{polylog}(n)}$ by trying all small circuits, putting SAT in quasi-polynomial time, and then E already has functions outside P/poly. Otherwise apply the reduction to a trivial family of unsatisfiable formulas: the produced truth tables are computable in time $2^{O(k)}$ and, being no-instances, have circuit complexity above $s_n$. The same argument with $s_n$ versus $2^{\varepsilon\log n}$ gives item 2. Item 3 follows from items 1 and 2 by the infinitely-often forms of the hardness-versus-randomness theorems of Babai–Fortnow–Nisan–Wigderson and Impagliazzo–Wigderson, and item 4 from item 3 by diagonalization against SUBEXP.


Expanding this node to full proof readiness requires planned proof-prerequisite pages for:

- Infinitely-often Impagliazzo–Wigderson and Babai–Fortnow–Nisan–Wigderson derandomization (Kabanets–Cai Theorems 16 and 17)

## Depends on

- [Natural and parametric honest reductions to MCSP](natural-and-parametric-honest-reductions-to-mcsp.md)
- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](../../minimum-circuit-size-problem/minimum-circuit-size-problem.md)
- [The class E](../../../complexity-classes/time-and-space-complexity-classes/e.md)
- [Polynomial time with polynomial advice](../../../complexity-classes/time-and-space-complexity-classes/ppoly.md)
- [BPP](../../../complexity-classes/time-and-space-complexity-classes/bpp.md)
- [The complexity class NP](../../../complexity-classes/the-classes-p-np-and-conp/np.md)
- [The complexity class P](../../../complexity-classes/the-classes-p-np-and-conp/p.md)

## Proof depends on

- [Impagliazzo-Wigderson: exponential circuit hardness in E derandomizes BPP](../../../pseudorandomness-and-one-way-functions/nisan-wigderson.md)

## Sources

- Valentine Kabanets, Jin-Yi Cai, "Circuit Minimization Problem", *Proceedings of the 32nd Annual ACM Symposium on Theory of Computing (STOC)*, 2000, https://doi.org/10.1145/335305.335314 (Theorems 15 to 18 and Corollary 19, numbering of the full version dated 15 November 1999, ECCC TR99-045).
