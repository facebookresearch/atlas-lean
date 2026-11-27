# Ren–Santhanam random-access Kt and K^t, parallel variants NC^1-K^t and L-K^t, and average-case hardness

Ren–Santhanam measure strings by descriptions from which a universal machine decides each bit with random access: their forms of Levin's $\mathrm{Kt}$ and of $\mathrm{K}^t$, the parallel variants $\mathsf{NC}^1\text{-}\mathrm{K}^t$ and $\mathsf{L}\text{-}\mathrm{K}^t$, and bounded-error average-case hardness, exact or approximate, of such a measure.

Fix an efficient universal Turing machine $U$ with random (oracle) access to a description $d$, and for a string $x$ set artificially $x_{|x|+1}=\star$. Call $d$ a *time-$t$ description* of $x$ if for every $1\le i\le |x|+1$ and every $b\in\{0,1,\star\}$, $U^{d}(i,b)$ accepts within $t$ steps if and only if $x_i=b$. For a resource bound $t:\mathbb{N}\to\mathbb{N}$,

$$
\mathrm{Kt}(x)=\min\{|d|+\log t : d\text{ is a time-}t\text{ description of }x\},\qquad \mathrm{K}^t(x)=\min\{|d| : d\text{ is a time-}t(|x|)\text{ description of }x\}.
$$

Minimizing $|d|+t$ instead gives the KT complexity of Allender, Buhrman, Koucký, van Melkebeek and Ronneburger. These random-access measures agree with Levin's whole-output $\mathrm{Kt}$ and with whole-output $\mathrm{K}^t$ only up to an additive $O(\log|x|)$ and a polynomial change of $t$; results stated with them refer to the random-access forms.

For a resource bound $t$, $\mathsf{NC}^1\text{-}\mathrm{K}^t(x)$ is the least $|d|$ such that, for every $1\le i\le|x|+1$ and $b\in\{0,1,\star\}$, an alternating universal machine $U_a^{d}(i,b)$ accepts in alternating time $\log t(|x|)$ iff $x_i=b$, and $\mathsf{L}\text{-}\mathrm{K}^t(x)$ is the least $|d|$ such that a space-bounded universal machine $U_s^{d}(i,b)$ accepts in space $\log t(|x|)$ iff $x_i=b$. The results stated with these measures hold for every efficient enough universal machine, so the subscript $U$ is dropped.

A function $f:\{0,1\}^*\to\mathbb{N}$ (such as $\mathrm{KT}$ or $\mathrm{Kt}$) is **(bounded-error) hard on average** if there is a constant $c>0$ such that every probabilistic polynomial-time machine $A$ satisfies $\Pr_{x\leftarrow U_n}[A(x)=f(x)]\le 1-1/n^{c}$ for all large $n$; it is **hard on average to $(d\log n)$-approximate** if $\Pr_{x\leftarrow U_n}[f(x)\le A(x)\le f(x)+d\log n]\le 1-1/n^{c}$ instead.

## Expansion

Random access is what allows sublinear decoding time: a description much shorter than $x$ can still let each bit be decided quickly, which ties KT to circuit size and lets $\mathsf{NC}^1$ and logspace decoders define parallel analogues of $\mathrm{K}^t$. Every string has a trivial description listing it bit by bit, so all these measures are at most $|x|+O(\log|x|)$ for suitable $t$, and hardness on average asks an efficient algorithm to beat that baseline on uniformly random strings.

## Depends on

- [Time-bounded Kolmogorov complexity K^t and Levin's Kt](../../../kolmogorov-complexity/time-bounded-kolmogorov-complexity/time-bounded-kolmogorov-complexity-and-levin-kt.md)
- [Probabilistic polynomial-time Turing machines](../../../../ComputerScience/cryptography/security-games/asymptotic-security/probabilistic-polynomial-time-turing-machines.md)

## Proof depends on

None.

## Sources

- Hanlin Ren and Rahul Santhanam, "Hardness of KT Characterizes Parallel Cryptography", *36th Computational Complexity Conference (CCC 2021)*, LIPIcs, 2021, https://doi.org/10.4230/LIPIcs.CCC.2021.35 (Definitions 14, 15 and 20).
