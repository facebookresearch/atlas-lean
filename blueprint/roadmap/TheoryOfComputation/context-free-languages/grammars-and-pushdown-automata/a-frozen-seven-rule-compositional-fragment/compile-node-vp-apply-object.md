# Compiling a node of the rule VP → TV Obj

The fragment has tokens everybody, admires and someone and the rules
$S \to \mathrm{Subj}\ \mathrm{VP}$, $\mathrm{VP} \to \mathrm{TV}\ \mathrm{Obj}$,
$S \to \mathrm{SP}\ \mathrm{Obj}$, $\mathrm{SP} \to \mathrm{Subj}\ \mathrm{TV}$, $\mathrm{Subj} \to$
everybody, $\mathrm{Obj} \to$ someone and $\mathrm{TV} \to$ admires, numbered $0$ to $6$. Over the
base types $e$ (entities) and $t$ (truth values), write $P = e \to t$, $Q = (e \to t) \to t$ and
$R = e \to e \to t$; the categories S, Subj, Obj, TV, VP and SP have types $t$, $Q$, $Q$, $R$, $P$
and $P$. Lexical terms live in the context $[Q, Q, R]$, whose variables in slots $0$, $1$ and $2$
stand for everybody, someone and admires. The compiler sends each valid derivation tree to a simply
typed term of its root category's type in that context. Let $l$ and $r$ be valid derivation trees
rooted at TV and Obj whose combination by the rule $\mathrm{VP} \to \mathrm{TV}\ \mathrm{Obj}$ is
valid, and let $\rho$ and $q$ be the compiled terms of $l$ and $r$. Then compiling the combined tree
gives $\lambda x.\, q\, (\lambda y.\, \rho\, x\, y)$, the rule's semantic action applied to the
compiled children.
