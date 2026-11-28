# Time-bounded instance complexity

The $t$-bounded instance complexity $\mathrm{ic}^t(x:A)$ is the length of a shortest program that runs in time $t$, never errs about membership in $A$ on any input (it may answer "don't know"), and answers on $x$ itself. It measures how hard one instance is relative to a set.

Fix a universal machine $U$ whose outputs are $0$, $1$ or $\bot$ ("don't know"). For a time bound $t$, a set $A$ and a string $x$,

$$
\mathrm{ic}^t(x:A)=\min_p\bigl\{|p| : \forall y\ U(p,y)\text{ runs in time }t(|y|);\ \forall y\ (U(p,y)=1\Rightarrow y\in A);\ \forall y\ (U(p,y)=0\Rightarrow y\notin A);\ U(p,x)\ne\bot\bigr\}.
$$

A program attaining the minimum is consistent with $A$ on every input and decides the given instance. Hardwiring the answer for $x$ into a distinguishing program and answering $\bot$ elsewhere gives

$$
\mathrm{ic}^t(x:A)\le\mathrm{CD}^t(x)+c
$$

for a constant $c$ independent of $x$ and $A$. For $A$ computable in polynomial time, the polynomial-time instance complexity is bounded by a constant depending only on $A$.

## Expansion

The notion is due to Orponen, Ko, Schöning and Watanabe. The upper bound runs the distinguisher for $x$ on the input $y$: if it accepts, then $y=x$ and the program outputs the stored bit telling whether $x\in A$; otherwise it outputs $\bot$. This program never errs and answers on $x$.

## Depends on

- [Distinguishing complexity CD^t](distinguishing-complexity-cdt.md)

## Proof depends on

None.

## Sources

- Lance Fortnow, "Kolmogorov Complexity and Computational Complexity", in *Complexity of Computations and Proofs* (J. Krajíček, ed.), Quaderni di Matematica 13, 2004, [author copy](https://lance.fortnow.com/papers/files/quaderni.pdf) (Definition 2.7, Theorem 3.5).
