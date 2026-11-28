# Distinguishing complexity CD^t

The $t$-time-bounded distinguishing complexity $\mathrm{CD}^t(x\mid y)$ is the length of a shortest program that, given auxiliary input $y$, accepts $x$, rejects every other string, and halts within the time bound on every input. It describes a string by recognizing it instead of printing it.

Fix a universal Turing machine $U$ and a fully time-constructible $t(n)\ge n$. Sipser's distinguishing complexity is

$$
\mathrm{CD}^t(x\mid y)=\min_p\bigl\{|p| : U(p,x,y)\text{ accepts};\ U(p,z,y)\text{ rejects for all } z\ne x;\ U(p,z,y)\text{ runs at most } t(|z|+|y|)\text{ steps for all } z\bigr\},
$$

and $\mathrm{CD}^t(x)=\mathrm{CD}^t(x\mid\varepsilon)$. The time bound is required on every input $z$, not only on $x$. The relativized measure $\mathrm{CD}^{t,A}(x\mid y)$ gives $U$ oracle access to $A$. All logarithms are base $2$.

Write $C^t(x\mid y)$ for the length of a shortest $p$ with $U(p,y)=x$ within $t(|x|+|y|)$ steps. Generating a string lets one distinguish it: for every $t$ there is a constant $c$ such that for all $x,y$,

$$
\mathrm{CD}^{c\,t\log t}(x\mid y)\le C^t(x\mid y)+c .
$$

## Expansion

Given a program $q$ printing $x$ from $y$, the distinguisher on input $z$ runs $q$, compares the output with $z$, and accepts iff they are equal; the simulation overhead accounts for the $c\,t\log t$ time bound and the comparison wrapper for the additive constant. The converse direction, finding the unique accepted string, is not known to be efficient; its status is settled by the Unique-SAT characterization.

## Depends on

- [Time-bounded Kolmogorov complexity K^t and Levin's Kt](../../time-bounded-kolmogorov-complexity/time-bounded-kolmogorov-complexity-and-levin-kt.md)

## Proof depends on

None.

## Sources

- Harry Buhrman, Lance Fortnow and Sophie Laplante, "Resource-Bounded Kolmogorov Complexity Revisited", *SIAM Journal on Computing* 31(3), 2001, [doi:10.1137/S009753979834388X](https://doi.org/10.1137/S009753979834388X) (Section 2, definition of CD and Lemma 2.1; numbering of the May 2001 author version).
- Lance Fortnow, "Kolmogorov Complexity and Computational Complexity", in *Complexity of Computations and Proofs* (J. Krajíček, ed.), Quaderni di Matematica 13, 2004, [author copy](https://lance.fortnow.com/papers/files/quaderni.pdf) (Definition 2.4, Theorem 3.1).
