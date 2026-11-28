# Randomized Levin complexity rKt and the problem MrKtP

$\mathrm{rKt}(w)$ is the minimum of $|M|+\lceil\log t\rceil$ over probabilistic machines $M$ that print $w$ with probability at least $2/3$ within $t$ steps. It extends Levin's $\mathrm{Kt}$ to randomized, pseudodeterministic decoding, and MrKtP asks for its value.

**Definition.** Machines have an extra tape of random bits, and $M_{\le t}$ is the random variable giving the output tape of $M$ after at most $t$ steps on empty input. For $\lambda\in[0,1]$ and $w\in\{0,1\}^*$,

$$
\mathrm{Kt}_\lambda(w)=\min_{M,t}\bigl\{|M|+\lceil\log t\rceil : \Pr[M_{\le t}=w]\ge\lambda\bigr\},\qquad \mathrm{rKt}(w)=\mathrm{Kt}_{2/3}(w).
$$

Levin's $\mathrm{Kt}$ is $\mathrm{Kt}_1$, and $\mathrm{Kt}_\alpha(w)\le\mathrm{Kt}_\beta(w)$ when $\alpha\le\beta$. The threshold is robust: $\mathrm{rKt}(x)\le\mathrm{Kt}_\lambda(x)+O(\log(1/\lambda))$ for $\lambda\in(0,1]$ (Lu and Oliveira; Hirahara writes $\mathrm{rKt}_\lambda$ for $\mathrm{Kt}_\lambda$). A conditional version $\mathrm{Kt}_\lambda(x\mid y)$ gives the program $y$ as input.

**Decision problems.** For $0<\alpha\le\beta\le 1$ and $s:\mathbb{N}\to\mathbb{N}$, $\mathrm{MrKtP}[\beta,\alpha,s]$ is the promise problem with yes-instances $\{w\in\{0,1\}^n : \mathrm{Kt}_\beta(w)\le s(n)\}$ and no-instances $\{w\in\{0,1\}^n : \mathrm{Kt}_\alpha(w)>s(n)\}$; by default $\beta=3/4$, $\alpha=2/3$, $s=n/2$. For $s_1\le s_2$, $\mathrm{Gap}\text{-}\mathrm{MrKtP}[s_1,s_2]$ separates $\mathrm{rKt}(w)\le s_1(n)$ from $\mathrm{rKt}(w)>s_2(n)$. For rationals $0<\alpha<\beta\le 1$, $\mathrm{MrKtP}[\beta,\alpha,s]\in\text{Promise-BPE}$, and $\mathrm{Gap}\text{-}\mathrm{MrKtP}[s_1,s_2]\in\text{Promise-BPE}$ when $s_1(n)+c\log n\le s_2(n)$ for a large enough constant $c$.

## Expansion

The Promise-BPE upper bound fixes a rational $\eta$ with $\alpha<\eta<\beta$, estimates for every machine and time bound of combined complexity at most $s$ the probability of printing $w$ with confidence $1-2^{-\omega(n)}$, and accepts iff some pair has estimate at least $\eta$; it uses that $\mathrm{Kt}_\lambda(w)=O(|w|)$. The gap version reduces to $\mathrm{MrKtP}[2/3,3/5,s_1]$ by amplification, which costs $O(\log n)$ in description length. As an example, infinitely many primes have $\mathrm{rKt}$ at most $|p|^{\varepsilon}$ for every $\varepsilon>0$, while no comparable Kt bound is known.

## Depends on

- [Time-bounded Kolmogorov complexity K^t and Levin's Kt](../../time-bounded-kolmogorov-complexity/time-bounded-kolmogorov-complexity-and-levin-kt.md)
- [The minimum Kt problem MKtP](../../time-bounded-kolmogorov-complexity/the-minimum-kt-problem.md)

## Proof depends on

None.

## Sources

- Igor Carboni Oliveira, "Randomness and Intractability in Kolmogorov Complexity", *46th International Colloquium on Automata, Languages, and Programming (ICALP 2019)*, LIPIcs 132, 2019, [doi:10.4230/LIPIcs.ICALP.2019.32](https://doi.org/10.4230/LIPIcs.ICALP.2019.32) (Definitions 6, 7 and 9, Lemmas 8 and 10).
- Shuichi Hirahara, "Symmetry of Information from Meta-Complexity", *37th Computational Complexity Conference (CCC 2022)*, LIPIcs 234, 2022, [doi:10.4230/LIPIcs.CCC.2022.26](https://doi.org/10.4230/LIPIcs.CCC.2022.26) (Definition 5.1, Lemma 5.2).
