# Semantic action of the rule VP → TV Obj

Over the base types $e$ (entities) and $t$ (truth values), write $P = e \to t$,
$Q = (e \to t) \to t$ and $R = e \to e \to t$; the categories S, Subj, Obj, TV, VP and SP have types
$t$, $Q$, $Q$, $R$, $P$ and $P$. For terms $\rho : R$ and $q : Q$ in any context, the action of
$\mathrm{VP} \to \mathrm{TV}\ \mathrm{Obj}$ is $\lambda x.\, q\, (\lambda y.\, \rho\, x\, y) : P$,
with $\rho$ and $q$ weakened under the new binders.
