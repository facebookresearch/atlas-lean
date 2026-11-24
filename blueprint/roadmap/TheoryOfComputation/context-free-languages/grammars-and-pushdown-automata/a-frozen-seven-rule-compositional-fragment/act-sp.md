# Semantic action of the rule SP → Subj TV

Over the base types $e$ (entities) and $t$ (truth values), write $P = e \to t$,
$Q = (e \to t) \to t$ and $R = e \to e \to t$; the categories S, Subj, Obj, TV, VP and SP have types
$t$, $Q$, $Q$, $R$, $P$ and $P$. For terms $q : Q$ and $\rho : R$ in any context, the action of
$\mathrm{SP} \to \mathrm{Subj}\ \mathrm{TV}$ is $\lambda y.\, q\, (\lambda x.\, \rho\, x\, y) : P$,
with $q$ and $\rho$ weakened under the new binders.
