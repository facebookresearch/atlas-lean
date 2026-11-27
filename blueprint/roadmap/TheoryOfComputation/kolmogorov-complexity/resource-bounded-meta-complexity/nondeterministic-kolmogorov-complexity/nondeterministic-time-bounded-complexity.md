# Nondeterministic time-bounded Kolmogorov complexity CND^t = nK^t

Nondeterministic time-bounded complexity measures a string by the shortest nondeterministic program that, within $t$ steps, outputs it on some witness and outputs only it or $\bot$ on every witness; equivalently, accepts it and nothing else. It is $\mathrm{CND}^t$ of Buhrman, Fortnow and Laplante and $\mathrm{nK}^t$ of Hu, Lu and Oliveira.

**Distinguishing form.** With a universal nondeterministic machine $U_n$,

$$
\mathrm{CND}^t(x\mid y)=\min_p\bigl\{|p| : U_n(p,x,y)\text{ accepts};\ U_n(p,z,y)\text{ rejects for all } z\ne x;\ U_n(p,z,y)\text{ runs at most } t(|z|+|y|)\text{ steps for all } z\bigr\},
$$

where acceptance and rejection have the usual nondeterministic meaning, and $\mathrm{CND}^t(x)=\mathrm{CND}^t(x\mid\varepsilon)$. Every deterministic computation is nondeterministic, so for every $t$ there is $c$ with $\mathrm{CND}^{c\,t\log t}(x\mid y)\le\mathrm{CD}^t(x\mid y)+c$.

**Output form.** For strings $x,y,r$ and $t\in\mathbb{N}$,

$$
\mathrm{nK}^t(x\mid y;r)=\min_{\Pi}\bigl\{|\Pi| : \forall w\in\{0,1\}^t\ \Pi(y;w;r)\text{ outputs } x\text{ or }\bot\text{ in } t\text{ steps};\ \exists w\in\{0,1\}^t\ \Pi(y;w;r)\text{ outputs } x\text{ in } t\text{ steps}\bigr\},
$$

with $\mathrm{nK}^t(x\mid y)=\mathrm{nK}^t(x\mid y;\varepsilon)$ and $\mathrm{nK}^t(x)=\mathrm{nK}^t(x\mid\varepsilon)$. Hu, Lu and Oliveira note that this measure is the one studied as $\mathrm{CND}^t$, with a slightly different but equivalent definition. They count time as steps of the program $\Pi$ in a computational model that simulates and is simulated by Turing machines with polynomial overhead, extends to longer witness and random strings, and composes nondeterministic programs with polynomial time and logarithmic length overhead.

The associated problem $\mathrm{MINnKT}$ asks, given $(x,1^s,1^t)$, whether $\mathrm{nK}^t(x)\le s$; it lies in $\Sigma_2^p$.

## Expansion

The two forms describe the same object: a nondeterministic distinguisher for $x$ can be turned into a program that guesses a candidate and an accepting computation and outputs the candidate, and conversely an output program accepts $z$ iff some witness yields $z$. Membership of MINnKT in $\Sigma_2^p$ follows by guessing $\Pi$ with $|\Pi|\le s$, checking all witnesses universally and one witness existentially.

## Depends on

- [Distinguishing complexity CD^t](../distinguishing-and-instance-complexity/distinguishing-complexity-cdt.md)
- [The time-bounded Kolmogorov complexity problem MINKT](../../time-bounded-kolmogorov-complexity/the-minkt-problem.md)

## Proof depends on

None.

## Sources

- Harry Buhrman, Lance Fortnow and Sophie Laplante, "Resource-Bounded Kolmogorov Complexity Revisited", *SIAM Journal on Computing* 31(3), 2001, [doi:10.1137/S009753979834388X](https://doi.org/10.1137/S009753979834388X) (Section 2, definition of CND and Lemma 2.2; numbering of the May 2001 author version).
- Jinqiao Hu, Zhenjian Lu and Igor C. Oliveira, "Hardness of Computing Nondeterministic Kolmogorov Complexity", *41st Computational Complexity Conference (CCC 2026)*, LIPIcs, 2026, [doi:10.4230/LIPIcs.CCC.2026.9](https://doi.org/10.4230/LIPIcs.CCC.2026.9) (Definitions 12 and 15, Section 1.2.1, Theorem 33).
