# Correctness and running time of the KG-map machine

Let $m$ be a mode and $x$ a list of
bits, and let $F_m$ be the clique-to-independent-set map on bit strings for flip and the
independent-set-to-vertex-cover map for vc. From any configuration of the KG-map machine $M_m$
at its start label, with any internal bit, in which stack $X$ holds the input symbols
$\mathrm{bit}(b)$ for the bits $b$ of $x$, top first, and every other stack is empty, $M_m$
reaches the halting label in at most $3(|x| + 1)$ steps with the output stack $O$ equal to
$F_m(x)$, top first.
