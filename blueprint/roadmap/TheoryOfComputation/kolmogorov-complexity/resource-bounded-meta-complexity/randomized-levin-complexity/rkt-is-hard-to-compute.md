# Unconditional lower bounds for computing rKt

Deciding or approximating randomized Levin complexity is provably hard for randomized algorithms: MrKtP is not in randomized quasi-polynomial time (Oliveira), and its additive-$O(\log n)$ gap version is not even in randomized time $2^{\varepsilon n}$ on infinitely many lengths (Hirahara), so exhaustive search is essentially optimal.

1. Let $1/2<\alpha\le\beta<1$ and let $n^\gamma\le s(n)\le n/2$ for all large $n$, for a fixed $\gamma>0$. Then $\mathrm{MrKtP}[\beta,\alpha,s]\notin\text{Promise-BPTIME}[n^{\mathrm{poly}(\log n)}]$.
2. For every $0<\gamma<1$, $\mathrm{Gap}\text{-}\mathrm{MrKtP}[n^\gamma,n/2]\notin\text{Promise-BPTIME}[n^{\mathrm{poly}(\log n)}]$, an $n^{1-\varepsilon}$-inapproximability result; for a large enough constant $C$ and constructive $s$, $\mathrm{Gap}\text{-}\mathrm{MrKtP}[s(n),s(n)+C\log n]\in\text{Promise-BPTIME}[2^{O(n)}]$.
3. Either $\mathrm{MKtP}\notin\mathrm{P}$ or $\mathrm{MrKtP}\notin\text{Promise-EXP}$.
4. Let $\mathrm{GapMrKtP}$ separate $\{(x,s):\mathrm{rKt}(x)\le s\}$ from $\{(x,s):\mathrm{rKt}(x)>s+c\log|x|\}$ for a large enough constant $c$. There is a constant $\varepsilon>0$ with $\mathrm{GapMrKtP}\notin\text{i.o.}\mathrm{BPTIME}(2^{\varepsilon n})$; in particular $\mathrm{MrKtP}=\{(x,1^s):\mathrm{rKt}(x)\le s\}\notin\mathrm{BPTIME}(2^{\varepsilon n})$.

## Expansion

Items 1 and 2 use indirect diagonalization: every language in BPE has polynomial-size oracle circuits with a nonadaptive oracle for MrKtP, built from the Nisan–Wigderson and Impagliazzo–Wigderson reconstruction paradigm, and $\mathrm{PSPACE}\subseteq\mathrm{BPP}^{\mathrm{MrKtP}}$ via a PSPACE-complete self-reducible language; a fast algorithm for MrKtP would then collapse a space class below a circuit bound that diagonalization forbids. Item 4 implements Kolmogorov's approach to lower bounds: symmetry of information fails for Kt (Ronneburger), hence conditionally for rKt, while an efficient algorithm for GapMrKtP would prove symmetry of information for rKt by the meta-complexity argument.

## Depends on

- [Randomized Levin complexity rKt and the problem MrKtP](randomized-levin-complexity-rkt.md)
- [The minimum Kt problem MKtP](../../time-bounded-kolmogorov-complexity/the-minimum-kt-problem.md)

## Proof depends on

- [Distinguishers for the Nisan–Wigderson generator give short time-bounded descriptions](../../time-bounded-kolmogorov-complexity/nisan-wigderson-reconstruction-gives-short-descriptions.md)

## Sources

- Igor Carboni Oliveira, "Randomness and Intractability in Kolmogorov Complexity", *46th International Colloquium on Automata, Languages, and Programming (ICALP 2019)*, LIPIcs 132, 2019, [doi:10.4230/LIPIcs.ICALP.2019.32](https://doi.org/10.4230/LIPIcs.ICALP.2019.32) (Theorems 1, 2 and 3, Theorem 11, Lemmas 12, 13 and 14).
- Shuichi Hirahara, "Symmetry of Information from Meta-Complexity", *37th Computational Complexity Conference (CCC 2022)*, LIPIcs 234, 2022, [doi:10.4230/LIPIcs.CCC.2022.26](https://doi.org/10.4230/LIPIcs.CCC.2022.26) (Theorems 1.4, 5.3 and 5.8).
