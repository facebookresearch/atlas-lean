# Stationary probabilities and large deviation rates of constrained random walks are uncomputable

Even for a constrained homogeneous random walk known to be stable through a given linear Lyapunov function, no algorithm decides whether the stationary probability of the origin is at most a given rational number, or whether a large deviation rate of the stationary distribution is at most a given value.

A *linear Lyapunov function* for a [constrained homogeneous random walk](constrained-homogeneous-random-walks.md) is a vector $w\in\mathbb R_+^d$ such that for some $\gamma>0$ and every nonempty $\Lambda\subseteq\{1,\dots,d\}$

$$
\sum_{\Delta\in\{-1,0,1\}^d}(w^{\mathsf T}\Delta)\,p(\Lambda,\Delta)\le-\gamma .
$$

In Gamarnik's theorems it is given as part of the input to certify that the walk is positive recurrent, so that an irreducible walk has a unique stationary distribution $\pi$. The transition probabilities are rational numbers. Gamarnik states the theorems for any $w\in\mathbb R_+^d$ satisfying the inequality; the walks built in the proof have the linear Lyapunov function $\sum_iQ_i+q_1+Cq_2$ with an integer $C\ge 2/(1-p)$, so the problems stay undecidable when $w$ is given as a vector of nonnegative integers, which is the finite-input form stated below.

For such an irreducible walk with stationary distribution $\pi$ and $v\in\mathbb R_+^d$, the lower and upper *large deviation rates* are

$$
L_-(v)=-\limsup_{n\to\infty}\frac{\log\pi(\lfloor vn\rfloor)}{n},\qquad L_+(v)=-\liminf_{n\to\infty}\frac{\log\pi(\lfloor vn\rfloor)}{n},
$$

with values in $[0,\infty]$ and $L_\pm(v)=+\infty$ when $\pi(\lfloor vn\rfloor)=0$ for all large $n$, so that $\pi(\lfloor vn\rfloor)$ is roughly $\exp(-L(v)n)$. This is the convention under which the source reads the rates (it calls the rate $+\infty$ when these probabilities vanish and describes $\pi(\lfloor vn\rfloor)$ as asymptotically $\exp(-L(v)n)$); its displayed formulas (6) and (7) omit the minus sign, and with them the question $L_\pm(v)\le r$ for $0\le r\le1$ would always have the answer yes.

**Theorem (Gamarnik).**
1. Given an irreducible constrained homogeneous random walk with rational transition probabilities, a linear Lyapunov function $w$ for it with nonnegative integer entries, and a rational $0\le r\le1$, it is undecidable whether $\pi(0)\le r$ (Theorem 2).
2. Given such a walk and such a $w$, a rational $0\le r\le1$ and $v\in\mathbb Z_+^d$, it is undecidable whether $L_-(v)\le r$, and whether $L_+(v)\le r$, with the rates defined as above (Theorem 3).

The same paper shows that the analogous problems are undecidable for single-station queueing systems under generalized priority policies given a linear Lyapunov function: whether $\pi(0)\le r$ for the stationary distribution, and whether the large deviation rate $L(v)$ is at most $r$ (Theorem 4). In contrast, when a geometric Lyapunov function is available, the stationary probability of a given state can be computed approximately to any accuracy $\varepsilon>0$, by the computable mixing bounds of Meyn and Tweedie (Theorem 6); no such approximation is possible for large deviation rates.

## Depends on

- [Constrained homogeneous random walks in the orthant](constrained-homogeneous-random-walks.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The reduction is from the halting problem of a two-counter machine started and halting in the same configuration with both counters zero, which is undecidable. The machine is embedded into a deterministic walk, which is then interleaved with an independent Bernoulli process of parameter $p$. If the machine never returns to its initial configuration, the walk started at the origin returns to it after $2t+2$ steps with probability $(1-p)p^t$; if the machine returns after $T$ steps, the return time is cut off at $2T+2$. Since $\pi(0)$ is the reciprocal of the expected return time, $\pi(0)=(1-p)/2$ if the machine never returns and $\pi(0)>(1-p)/2$ if it does. For large deviation rates, an extra coordinate makes $\pi(nv)$ vanish for large $n$ if the machine halts, so $L(v)=+\infty$, and makes $\lim_n \log\pi(nv)/n=\log p$ if it does not, so $L(v)=-\log p$. Taking the Bernoulli parameter $p$ rational with $-\log p<r$ (for instance $p=2/3$ and $r=1/2$) makes $L(v)\le r$ hold exactly when the machine does not halt; the source phrases this as taking $r>\log p$ in its sign convention.

## Sources

- David Gamarnik, "On the Undecidability of Computing Stationary Distributions and Large Deviation Rates for Constrained Random Walks", *Mathematics of Operations Research* 32(2), 2007, pp. 257–265, doi:[10.1287/moor.1060.0247](https://doi.org/10.1287/moor.1060.0247); read in arXiv:math/0204268v1 ([arXiv](https://arxiv.org/abs/math/0204268v1)), whose numbering is used here: Sections 3 (model and linear Lyapunov functions), 4 (counter machines, Theorem 1), 5 (Theorem 2 and Proposition 1), 6 (Theorem 3), 7 (Theorem 4) and 8 (Theorem 6).
