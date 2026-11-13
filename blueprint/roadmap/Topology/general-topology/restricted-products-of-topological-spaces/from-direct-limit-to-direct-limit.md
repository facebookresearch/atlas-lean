# The backward map undoes the forward map

Let $(X_i)_{i \in \iota}$ be topological spaces
with subsets $U_i \subseteq X_i$, and for a finite set $S \subseteq \iota$ let $X_S$ be the set of
tuples $x \in \prod_i X_i$ with $x_i \in U_i$ for all $i \notin S$. For every $x$ in the
restricted product $\prod'_i (X_i, U_i)$ with respect to the cofinite filter, let $S(x)$ be the
finite set of indices $i$ with $x_i \notin U_i$. Sending $x$ to its class in $X_{S(x)}$ in the
direct limit $\varinjlim_S X_S$, and then sending that class to the tuple carried by its
representative, returns $x$.

This holds definitionally: unfolding both maps, the quotient lift applied to the canonical
representative returns the representative itself.
