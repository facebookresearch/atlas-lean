# Compiling the leaf Subj → everybody

The fragment has tokens everybody, admires and someone and the rules
$S \to \mathrm{Subj}\ \mathrm{VP}$, $\mathrm{VP} \to \mathrm{TV}\ \mathrm{Obj}$,
$S \to \mathrm{SP}\ \mathrm{Obj}$, $\mathrm{SP} \to \mathrm{Subj}\ \mathrm{TV}$, $\mathrm{Subj} \to$
everybody, $\mathrm{Obj} \to$ someone and $\mathrm{TV} \to$ admires, numbered $0$ to $6$. Over the
base types $e$ (entities) and $t$ (truth values), write $P = e \to t$, $Q = (e \to t) \to t$ and
$R = e \to e \to t$; the categories S, Subj, Obj, TV, VP and SP have types $t$, $Q$, $Q$, $R$, $P$
and $P$. Lexical terms live in the context $[Q, Q, R]$, whose variables in slots $0$, $1$ and $2$
stand for everybody, someone and admires. The compiler sends each valid derivation tree to a simply
typed term of its root category's type in that context. Compiling the valid leaf
${\mathrm{Subj}} \to$ everybody gives the lexical term of everybody, the variable in slot $0$.
