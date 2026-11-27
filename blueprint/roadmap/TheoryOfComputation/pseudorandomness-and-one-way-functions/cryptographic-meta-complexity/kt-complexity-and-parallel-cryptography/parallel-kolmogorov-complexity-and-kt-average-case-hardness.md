# Parallel time-bounded Kolmogorov complexity and average-case hardness of KT

Parallel variants $\mathrm{NC}^1\text{-}\mathrm{K}^t$ and $\mathrm{L}\text{-}\mathrm{K}^t$ measure description length under logarithmic alternating time or log-space decoding, and average-case hardness of $\mathrm{KT}$ measures how accurately probabilistic polynomial-time algorithms approximate random-access time-bounded complexity.

Fix an efficient universal Turing machine $U$ with random (oracle) access to a description $d$, and for a string $x$ set artificially $x_{|x|+1}=\star$. Then

$$
\mathrm{KT}(x)=\min\{|d|+t : \forall\, 1\le i\le |x|+1,\ \forall\, b\in\{0,1,\star\},\ U^{d}(i,b) \text{ accepts within } t \text{ steps iff } x_i=b\}.
$$

Replacing $|d|+t$ by $|d|+\log t$ gives Levin's $\mathrm{Kt}$, and fixing the time to $t(|x|)$ and minimizing $|d|$ gives $\mathrm{K}^t$. For a resource bound $t$, $\mathrm{NC}^1\text{-}\mathrm{K}^t(x)$ is the least $|d|$ such that an alternating universal machine $U_a^{d}(i,b)$ accepts in alternating time $\log t(|x|)$ iff $x_i=b$, and $\mathrm{L}\text{-}\mathrm{K}^t(x)$ is the least $|d|$ such that a space-bounded universal machine $U_s^{d}(i,b)$ accepts in space $\log t(|x|)$ iff $x_i=b$. The results stated with these measures hold for every efficient enough universal machine, so the subscript $U$ is dropped.

The **Minimum KT Problem** is $\mathrm{MKTP}=\{(x,1^k):\mathrm{KT}(x)\le k\}$; its search version asks for an optimal description $d$ from which $x$ is generated implicitly in time at most $k-|d|$. There is an absolute constant $c'$ with $\mathrm{KT}(x)\le |x|+c'\log|x|$ for every $x$.

A function $f:\{0,1\}^*\to\mathbb{N}$ (such as $\mathrm{KT}$) is **(bounded-error) hard on average** if there is a constant $c>0$ such that every probabilistic polynomial-time machine $A$ satisfies $\Pr_{x\leftarrow U_n}[A(x)=f(x)]\le 1-1/n^{c}$ for all large $n$; it is **hard on average to $(d\log n)$-approximate** if $\Pr_{x\leftarrow U_n}[f(x)\le A(x)\le f(x)+d\log n]\le 1-1/n^{c}$ instead.

## Expansion

KT was introduced by Allender, Buhrman, Koucký, van Melkebeek and Ronneburger as a Kolmogorov analogue of circuit size: a description with random access to $d$ that prints each bit in time $t$ is close to a circuit of size about $|d|+t$, so $\mathrm{KT}$ and the circuit size of the truth table are polynomially related. Every string has a trivial description listing $x$ bit by bit, which gives the bound $|x|+O(\log|x|)$; most strings come within a logarithmic term of it because few strings have small Kolmogorov complexity.

## Depends on

- [Time-bounded Kolmogorov complexity K^t and Levin's Kt](../../../kolmogorov-complexity/time-bounded-kolmogorov-complexity/time-bounded-kolmogorov-complexity-and-levin-kt.md)

## Proof depends on

- [Few strings have small complexity](../../../kolmogorov-complexity/incompressible-strings-and-kolmogorov-complexity/card-lt-two-pow.md)

## Sources

- Hanlin Ren and Rahul Santhanam, "Hardness of KT Characterizes Parallel Cryptography", *36th Computational Complexity Conference (CCC 2021)*, LIPIcs, 2021, https://doi.org/10.4230/LIPIcs.CCC.2021.35 (Definitions 14, 15, 17 and 20; Fact 18).
