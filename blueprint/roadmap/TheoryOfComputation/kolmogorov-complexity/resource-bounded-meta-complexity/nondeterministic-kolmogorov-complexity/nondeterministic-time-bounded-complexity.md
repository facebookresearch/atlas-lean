# Nondeterministic time-bounded Kolmogorov complexity nK^t

The nondeterministic time-bounded complexity $\mathrm{nK}^t(x\mid y)$ is the length of a shortest program that, within $t$ steps and on every witness in $\{0,1\}^t$, outputs $x$ or $\bot$, and outputs $x$ on some witness. Buhrman, Fortnow and Laplante studied a distinguishing-form variant, $\mathrm{CND}^t$, which Hu, Lu and Oliveira call equivalent.

**Definition.** For strings $x,y,r$ and $t\in\mathbb{N}$,

$$
\mathrm{nK}^t(x\mid y;r)=\min_{\Pi}\bigl\{|\Pi| : \forall w\in\{0,1\}^t\ \Pi(y;w;r)\text{ outputs } x\text{ or }\bot\text{ in } t\text{ steps};\ \exists w\in\{0,1\}^t\ \Pi(y;w;r)\text{ outputs } x\text{ in } t\text{ steps}\bigr\},
$$

with $\mathrm{nK}^t(x\mid y)=\mathrm{nK}^t(x\mid y;\varepsilon)$ and $\mathrm{nK}^t(x)=\mathrm{nK}^t(x\mid\varepsilon)$. Time counts steps of the program $\Pi$ in a strongly efficient computational model: it simulates and is simulated by Turing machines with polynomial overhead, extends to longer witness and random strings, and composes nondeterministic programs with polynomial time and logarithmic length overhead.

The associated problem $\mathrm{MINnKT}$ asks, given $(x,1^s,1^t)$, whether $\mathrm{nK}^t(x)\le s$; it lies in $\Sigma_2^p$.

**Remark: the distinguishing form $\mathrm{CND}^t$.** Buhrman, Fortnow and Laplante fix a universal nondeterministic Turing machine $U_n$ and a time bound $t$, and define

$$
\mathrm{CND}^t(x\mid y)=\min_p\bigl\{|p| : U_n(p,x,y)\text{ accepts};\ U_n(p,z,y)\text{ rejects for all } z\ne x;\ U_n(p,z,y)\text{ runs at most } t(|z|+|y|)\text{ steps for all } z\bigr\},
$$

where acceptance and rejection have the usual nondeterministic meaning, and $\mathrm{CND}^t(x)=\mathrm{CND}^t(x\mid\varepsilon)$. Here the time bound is a function of the input length and holds on every input $z$, whereas $\mathrm{nK}^t$ bounds the program's own steps by the number $t$ and draws witnesses from $\{0,1\}^t$. Hu, Lu and Oliveira note that the measure they define was studied as $\mathrm{CND}^t$ under a slightly different definition and that the two definitions are equivalent (footnote 1 of their paper). Every deterministic computation is nondeterministic, so for every $t$ there is $c$ with $\mathrm{CND}^{c\,t\log t}(x\mid y)\le\mathrm{CD}^t(x\mid y)+c$ (Buhrman, Fortnow and Laplante, Lemma 2.2).

## Expansion

The conversion behind that equivalence: a nondeterministic distinguisher for $x$ becomes an output program that guesses a candidate and an accepting computation and outputs the candidate, and conversely an output program accepts $z$ iff some witness yields $z$. The time bounds and program lengths change in the conversion, so the two measures are not literally equal and theorems cite the form they use. Membership of MINnKT in $\Sigma_2^p$ follows by guessing $\Pi$ with $|\Pi|\le s$, checking all witnesses universally and one witness existentially.

## Depends on

- [Distinguishing complexity CD^t](../distinguishing-and-instance-complexity/distinguishing-complexity-cdt.md)
- [The time-bounded Kolmogorov complexity problem MINKT](../../time-bounded-kolmogorov-complexity/the-minkt-problem.md)

## Proof depends on

None.

## Sources

- Jinqiao Hu, Zhenjian Lu and Igor C. Oliveira, "Hardness of Computing Nondeterministic Kolmogorov Complexity", *41st Computational Complexity Conference (CCC 2026)*, LIPIcs, 2026, [doi:10.4230/LIPIcs.CCC.2026.9](https://doi.org/10.4230/LIPIcs.CCC.2026.9) (Definitions 12 and 15, Section 1.2.1 and its footnote 1, Theorem 33).
- Harry Buhrman, Lance Fortnow and Sophie Laplante, "Resource-Bounded Kolmogorov Complexity Revisited", *SIAM Journal on Computing* 31(3), 2001, [doi:10.1137/S009753979834388X](https://doi.org/10.1137/S009753979834388X) (Section 2, definition of CND and Lemma 2.2; numbering of the May 2001 author version).
