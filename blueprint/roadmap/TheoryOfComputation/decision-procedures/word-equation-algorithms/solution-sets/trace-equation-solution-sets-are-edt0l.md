# Solution sets of trace equations are EDT0L

For an equation with recognizable constraints in a free partially commutative monoid with involution and a fixed number of resources, a trim automaton over endomorphisms computed in nondeterministic space $O(n \log n)$ describes all solutions as an EDT0L set of tuples and decides solvability and finiteness.

Fix the number of resources. There is a nondeterministic algorithm using $O(n \log n)$ bits of space, with $n$ the input size below, for the following task. The input is a resource alphabet $(A \cup \mathcal{X}, \rho)$ with involution and a [trace equation with constraints](trace-equations-with-constraints.md) $(U, V, \mu)$ with constants $A$, variables $\mathcal{X} = \{X_1, \dots, X_k\}$ and input size $n$. The algorithm computes an alphabet $C \supseteq A$ of size $O(n)$, constants $c_1, \dots, c_k \in C$ and a nondeterministic finite automaton $\mathcal{A}$ accepting a rational set $R$ of $A$-endomorphisms of $C^*$ such that $h(C^*) \subseteq A^*$ for all $h \in R$ and, for the projection $\pi : A^* \to M(A, \rho)$,

$$
\{ (\pi h(c_1), \dots, \pi h(c_k)) : h \in R \} = \{ (\sigma(X_1), \dots, \sigma(X_k)) : \sigma \text{ solves } (U, V, \mu) \text{ in } M(A, \rho) \} .
$$

Thus the solution set is an effectively computable [EDT0L](edt0l-language.md) set of $k$-tuples of traces. Furthermore, $(U, V, \mu)$ has a solution if and only if $\mathcal{A}$ accepts a nonempty set, and it has infinitely many solutions if and only if $\mathcal{A}$ has a directed cycle; both conditions can be tested nondeterministically in the same space. The result extends to finite systems of trace equations. With one resource shared by all letters this covers equations over free monoids with involution.

## Depends on

- [Trace equations with recognizable constraints](trace-equations-with-constraints.md)
- [EDT0L language](edt0l-language.md)

## Proof depends on

None.

## Expansion

The automaton is specific. In a preprocessing step the initial equation is made free of self-involuting constants, and a new marker $\#$ is introduced as the only self-involuting constant, with $\rho(\#) = \mathcal{R}$ and $\emptyset \neq \rho(a) \neq \mathcal{R}$ for all other constants; the nonempty resource sets matter, since a constant with no resource would commute with $\#$. The equation is then packed into the single trace $W_{\mathrm{init}} = \#X_1\#\cdots X_k\#U\#V\#\bar{U}\#\bar{V}\#\bar{X}_k\#\cdots\bar{X}_1\#$, so that a solution is a morphism with $\sigma(W) = \overline{\sigma(W)}$, and $\#$ is never compressed. The states are extended equations of weight at most a constant times $n$; substitution transitions erase a variable or pop at least one constant out of it, compression transitions replace a factor by a new constant, each transition is labelled by its associated morphism in the opposite direction, final states are variable-free equations beginning with $\#c_1\#\cdots\#c_k\#$, and the automaton is trimmed.

This page becomes ready once the following are pages of their own: the preprocessing that removes self-involuting constants (Diekert, Jeż and Kufleitner, Section 3, citing Diekert and Muscholl), the automaton of Section 4.1, its soundness step (Lemma 2), the linear bound on the equations met (Lemma 8), its completeness (Lemma 9), and the argument from Section 4 that the trim automaton has a directed cycle exactly when there are infinitely many solutions.

## Sources

- Volker Diekert, Artur Jeż, Manfred Kufleitner, "Solutions of Word Equations over Partially Commutative Structures", ICALP 2016, LIPIcs 55, Article 127 (2016), https://doi.org/10.4230/LIPIcs.ICALP.2016.127, Theorem 1, monoid version, and the remark after it on systems; Section 3 for $W_{\mathrm{init}}$ and the extended equations, Section 4.1 for the automaton, Lemma 2 (Section 4.2), Lemma 8 and Lemma 9 (Sections 4.3–4.4)
