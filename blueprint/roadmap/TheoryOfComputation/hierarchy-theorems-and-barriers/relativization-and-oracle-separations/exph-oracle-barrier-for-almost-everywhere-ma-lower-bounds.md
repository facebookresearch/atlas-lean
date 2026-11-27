# EXPH-oracle barrier for almost-everywhere Merlin–Arthur circuit lower bounds

Santhanam's lower bound $\mathsf{MA}/1\not\subseteq\mathrm{SIZE}[n^k]$ is $\mathsf{PSPACE}$-relativizing, but an $\mathsf{EXPH}$-computable oracle makes promise-MA infinitely often easy for linear-size circuits, so an almost-everywhere version would need techniques beyond $\mathsf{PSPACE}$-relativizing ones or would prove $\mathsf{L}\ne\mathsf{NP}$.

1. For every oracle $O\in\mathsf{PSPACE}$ and every $k\ge 1$, $\mathsf{MA}^O/1\not\subseteq\mathrm{SIZE}^O[n^k]$.
2. There is an oracle $O\in\mathsf{EXPH}$ such that $\mathsf{pr}\text{-}\mathsf{MATIME}^O[2^n]\subseteq\mathrm{i.o.}\text{-}\mathrm{SIZE}^O[O(n)]$; in particular $\mathsf{MATIME}^O[2^n]/1\subseteq\mathrm{i.o.}\text{-}\mathrm{SIZE}^O[O(n)]$.
3. Consequently, if there is a $\mathsf{PSPACE}$-relativizing proof that $\mathsf{MA}/1\not\subseteq\mathrm{i.o.}\text{-}\mathrm{SIZE}[n^k]$ for every constant $k\ge 1$, then $\mathsf{PSPACE}\ne\mathsf{EXPH}$, and hence $\mathsf{L}\ne\mathsf{NP}$.

Here $\mathrm{i.o.}\text{-}\mathrm{SIZE}[s]$ is the class of languages that agree with circuits of size $s(n)$ on infinitely many input lengths, so a language outside it is hard on almost every length. To the authors' knowledge, this is the first evidence that current techniques cannot make fixed-polynomial lower bounds for $\Sigma_2^p\supseteq\mathsf{pr}\text{-}\mathsf{MA}$ hold almost everywhere.

## Expansion

Item 1 follows Santhanam's win-win argument with a $\mathsf{PSPACE}$-complete language $L_{\mathrm{hard}}$ that is same-length instance-checkable, replacing $\mathsf{IP}=\mathsf{PSPACE}$ by its $\mathsf{PSPACE}$-relativizing form: if $L_{\mathrm{hard}}\in\mathrm{SIZE}^O[\mathrm{poly}]$ then already $\mathsf{MA}^O\not\subseteq\mathrm{SIZE}^O[n^k]$, and otherwise padding with one advice bit gives the lower bound. Item 2 modifies the Buhrman–Fortnow–Thierauf oracle construction. Oracle inputs have the form $(r,i,x)$ with an advice string $r\in\{0,1\}^{cn}$, and the construction finds, for infinitely many $n$, an unfrozen $r_n^*$ such that $(r_n^*,i,x)\in O$ whenever the $i$-th $2^n$-time Merlin–Arthur machine $M_i$ accepts $x$ with probability at least $3/4$ on some certificate and $(r_n^*,i,x)\notin O$ whenever it accepts with probability at most $1/4$ on every certificate; a linear-size oracle circuit with $r_n^*$ hardwired then decides $M_i$ at length $n$. Stage by stage, pairs $(i,x)$ that some oracle extension makes accept are forced and the advice strings their computations query heavily are frozen; approximate counting in $\mathsf{PH}$ replaces exact acceptance probabilities, which places the oracle in $\mathsf{EXPH}$. Item 3 combines item 2 with the barrier principle of bounded relativization.

## Depends on

- [Bounded relativization](bounded-relativization.md)
- [The class MA (Merlin–Arthur)](../../complexity-classes/time-and-space-complexity-classes/ma.md)

## Proof depends on

- [MA with one bit of advice lacks fixed-polynomial-size circuits](../../circuit-complexity/circuit-lower-bounds-for-merlin-arthur-classes/ma-with-one-bit-of-advice-lacks-fixed-polynomial-size-circuits.md)

## Sources

- Shuichi Hirahara, Zhenjian Lu and Hanlin Ren, "Bounded Relativization", *38th Computational Complexity Conference (CCC 2023)*, LIPIcs, 2023, https://doi.org/10.4230/LIPIcs.CCC.2023.6 (Proposition 17, Theorem 18, Theorem 57, Definition 58, Lemmas 59 to 62, Corollary 63, Section 6).
