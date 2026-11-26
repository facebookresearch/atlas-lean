# Well-formed instances of ADDITIONAL KEY

An instance $(n, F, R, K)$ is well-formed when every name listed in a dependency of $F$, in $R$ and in a member of $K$ is below $n$, and every member of $K$, read as a set of attributes, is a key for $\langle R, F \rangle$: a subset of $R$ from which the dependency onto $R$ follows by Armstrong's axioms, and no proper subset of which has this property. This test is where a name $n$ or larger is rejected; feasibility reads each list as the set of names below $n$ that it contains.
