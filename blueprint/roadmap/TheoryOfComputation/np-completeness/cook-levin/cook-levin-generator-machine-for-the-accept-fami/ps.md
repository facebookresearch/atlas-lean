# Precomputation stages of the accept generator

Write $A$, $K$ and $g$ for the
label/state block size, the number of stacks and the number of symbol codes of the generator's
layout, and $k_1$ for the index of the stack whose top cell it checks. A precomputation stage is
one of eight plain stages or one of five multiplication stages, each of which carries a stage $s$
of the multiplication routine. Named by the step the generator takes there, in the order it runs
them, they are: push $g$ units on $\mathsf{Gc}$; multiply into $\mathsf{HG}$ at $s$; push $A$
units on $\mathsf{Wc}$; push $K$ units on $\mathsf{Kc}$; multiply into $\mathsf{Wc}$ at $s$;
multiply into $\mathsf{TW}$ at $s$; increment $\mathsf{Tn}$; multiply into $\mathsf{Vc}$ at $s$;
drain $\mathsf{TW}$ onto both $\mathsf{CB}$ and $\mathsf{tmp}$; drain $\mathsf{tmp}$ back onto
$\mathsf{TW}$; push $A$ units on $\mathsf{CB}$; push $k_1$ units on $\mathsf{K1}$; multiply into
$\mathsf{CB}$ at $s$.
