# Feasible instances of ADDITIONAL KEY

Let $(n, F, R, K)$ be an instance, and read each list of names as the set of names below $n$ that it lists, so that $R$, every dependency and every member of $K$ become sets of attributes. The instance is feasible when some set $R'$ of attributes below $n$ satisfies

- $R' \subseteq R$;
- $R'$ is a key for $\langle R, F \rangle$: the dependency $R' \to R$ follows from $F$ by Armstrong's axioms (reflexivity, augmentation and transitivity), and no proper subset $R'' \subsetneq R'$ has $R'' \to R$ following from $F$;
- $R'$ is not in $K$: it differs, as a set, from every member of $K$ read as a set.

Feasibility compares sets of attributes, not raw lists. A name $n$ or larger in a list is not rejected here; it is simply not an attribute, so it drops out of the set. Out-of-range names are rejected by well-formedness instead, which the decision problem checks separately.
