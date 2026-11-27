# The promise problem GapMINKT

$\mathrm{Gap}_\tau\mathrm{MINKT}$ asks to distinguish strings with $K^t(x)\le s$ from strings with $K^{\tau(|x|,t)}(x)>s+\log\tau(|x|,t)$: a gap in both the time bound and the size. It is the approximation version of MINKT on which non-black-box worst-case to average-case reductions operate.

Fix an efficient universal machine $U$. For strings $x,y$, a time bound $t\in\mathbb{N}\cup\{\infty\}$ and an oracle $A$,

$$
K^{t,A}(x\mid y)=\min\bigl\{|d| : U^{A,y,d}\text{ outputs } x_i\text{ on input } i\text{ in time } t\text{ for every } i\in[1,|x|+1]\bigr\},
$$

where $U^{A,y,d}$ has oracle access to $A$ and to the bits of $y$ and $d$, and $x_{|x|+1}$ is an end marker. For a polynomial $\tau:\mathbb{N}\times\mathbb{N}\to\mathbb{N}$, $\mathrm{Gap}_\tau\mathrm{MINKT}$ is the promise problem $(\Pi_{\mathrm{Yes}},\Pi_{\mathrm{No}})$ with

$$
\Pi_{\mathrm{Yes}}=\{(x,1^t,1^s) : K^t(x)\le s\},\qquad \Pi_{\mathrm{No}}=\{(x,1^t,1^s) : K^{\tau(|x|,t)}(x)>s+\log\tau(|x|,t)\}.
$$

One writes $\mathrm{GapMINKT}\in\mathrm{P}$ if $\mathrm{Gap}_\tau\mathrm{MINKT}\in\mathrm{P}$ for some polynomial $\tau$. Equivalently, there are a polynomial-time algorithm $\widetilde{K}$ and a polynomial $p$ with

$$
K^{p(t)}(x)-\log p(t)\le\widetilde{K}(x,1^t)\le K^t(x)
$$

for every string $x$ and every $t\ge|x|$. Hirahara's non-black-box reductions show that $\mathrm{DistNP}\subseteq\mathrm{AvgP}$ implies $\mathrm{GapMINKT}\in\mathrm{P}$.

## Expansion

The two formulations are interchangeable: an algorithm for the promise problem yields $\widetilde{K}$ by searching for the least accepted threshold $s$, and conversely $\widetilde{K}$ decides the promise problem by comparing $\widetilde{K}(x,1^t)$ with $s$. Since few strings have small time-bounded complexity, the yes-instances are rare among random strings, which is what an average-case algorithm can detect.

## Depends on

- [The time-bounded Kolmogorov complexity problem MINKT](../../time-bounded-kolmogorov-complexity/the-minkt-problem.md)
- [Time-bounded Kolmogorov complexity K^t and Levin's Kt](../../time-bounded-kolmogorov-complexity/time-bounded-kolmogorov-complexity-and-levin-kt.md)

## Proof depends on

None.

## Sources

- Shuichi Hirahara, "Symmetry of Information from Meta-Complexity", *37th Computational Complexity Conference (CCC 2022)*, LIPIcs 234, 2022, [doi:10.4230/LIPIcs.CCC.2022.26](https://doi.org/10.4230/LIPIcs.CCC.2022.26) (Definitions 3.1 and 3.3, Fact 3.4, Lemma 2.1).
