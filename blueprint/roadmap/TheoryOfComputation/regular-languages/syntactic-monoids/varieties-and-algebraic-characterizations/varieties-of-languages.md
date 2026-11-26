# Varieties of languages

A *class of recognizable languages* $\mathcal{V}$ assigns to each finite alphabet $A$ a set $\mathcal{V}(A^*)$ of regular languages over $A$,
compatibly with bijections between alphabets. It is a *variety of languages* if, for all alphabets $A$ and $B$:

1. $\mathcal{V}(A^*)$ is a Boolean algebra of languages;
2. for every monoid morphism $\varphi : A^* \to B^*$, $X \in \mathcal{V}(B^*)$ implies $\varphi^{-1}(X) \in \mathcal{V}(A^*)$;
3. if $X \in \mathcal{V}(A^*)$ and $u \in A^*$, then the quotients $u^{-1} X = \{w : uw \in X\}$ and $X u^{-1} = \{w : wu \in X\}$ belong to $\mathcal{V}(A^*)$.

## Sources

- J.-É. Pin, *Mathematical Foundations of Automata Theory*, lecture notes, version of March 24, 2025, <https://www.irif.fr/~jep/PDF/MPRI/MPRI.pdf>: Section XIII.1 (classes of recognisable languages) and Section XIII.3 (positive varieties and varieties of languages).
