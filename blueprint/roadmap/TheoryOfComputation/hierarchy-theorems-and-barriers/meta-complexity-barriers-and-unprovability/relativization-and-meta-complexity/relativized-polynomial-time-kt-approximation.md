# A relativized world where Kt is approximable in polynomial time and EXP = ZPP

Ren and Santhanam give an oracle relative to which a variant $\widetilde{Kt}$ of Levin's Kt is computable exactly in polynomial time and $\mathsf{EXP} = \mathsf{ZPP}$, so Kt is $(2+\epsilon)$-approximable there. Proving $\widetilde{Kt} \notin \mathsf{P}$, or that Kt has no such approximation, thus needs non-relativizing techniques, even combined with IP = PSPACE or the instance checkers for EXP.

For a string $x$, $\widetilde{Kt}(x)$ is the minimum of $|M| + \lfloor \log t \rfloor$ over machines $M$ such that, after $M$ runs on the empty input for $t$ steps, the content of some tape of $M$ is exactly $x$; unlike $Kt$, the machine need not halt after producing $x$, so $x$ may be an intermediate tape content. For every $x$,

$$
\widetilde{Kt}(x) \le Kt(x) \le (2 + o(1))\,\widetilde{Kt}(x).
$$

There is a relativized world in which $\widetilde{Kt}$ is computable in deterministic polynomial time and $\mathsf{EXP} = \mathsf{ZPP}$. Consequently, there is a relativized world in which $Kt$ can be approximated within a factor $2 + \epsilon$ in polynomial time, for every $\epsilon > 0$. Ren and Santhanam regard this world as an obstacle to proving $\mathrm{MKtP} \notin \mathsf{P}$; it does not place exact MKtP in polynomial time, so it does not rule out a relativizing proof of $\mathrm{MKtP} \notin \mathsf{P}$.

## Proof sketch

The oracle is a fixed point: stage $n$ enumerates all pairs $(M, t)$ with $|M| + \lfloor \log t\rfloor = n$, runs $M$ for $t$ steps and sets $O[x] = n$ for every intermediate tape content $x$ not yet fixed; a query $O[y]$ made by such an $M$ can be answered $n$ when not already fixed lower, because $\widetilde{Kt}(y) \le n$ by definition. Then $O[x] = \widetilde{Kt}^{O}(x)$ for all $x$. A second oracle embedding the truth tables of the EXP-complete language of pairs $(M, t)$ such that $M$ outputs $1$ within $t$ steps yields $\mathsf{EXP} = \mathsf{ZPP}$, so the non-relativizing instance checkers for EXP and $\mathsf{IP} = \mathsf{PSPACE}$ also hold in this world.

## Depends on

- [Time-bounded Kolmogorov complexity K^t and Levin's Kt](../../../kolmogorov-complexity/time-bounded-kolmogorov-complexity/time-bounded-kolmogorov-complexity-and-levin-kt.md)
- [The class EXP](../../../complexity-classes/time-and-space-complexity-classes/exp.md)
- [ZPP](../../../complexity-classes/time-and-space-complexity-classes/zpp.md)
- [The complexity class P](../../../complexity-classes/the-classes-p-np-and-conp/p.md)

## Proof depends on

None.

## Sources

- Hanlin Ren and Rahul Santhanam, "A Relativization Perspective on Meta-Complexity", *STACS* 2022, LIPIcs 219, Article 54, DOI 10.4230/LIPIcs.STACS.2022.54 (Theorems 14 and 15 and the paragraph after them, Section 2.2; definition of the variant and proof overview in Section 3.2).
- Hanlin Ren and Rahul Santhanam, "A Relativization Perspective on Meta-Complexity", full version, ECCC TR21-089, 25 June 2021, <https://eccc.weizmann.ac.il/report/2021/089/> (Theorem 1.15; Lemma 4.1 and Theorem 4.2, Section 4; the world with $\mathsf{EXP} = \mathsf{ZPP}$ in Section 4.1, Lemmas 4.3 and 4.4).
