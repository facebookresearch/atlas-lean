# The counter program

For a polynomial $k$ with natural-number coefficients, whose
coefficient list $\kappa_0, \dots, \kappa_{D-1}$ has length $D$, and $c, e, d \in \mathbb{N}$,
the counter program is the program with the labels of the counter program for $D$ Horner rounds
that acts on a Boolean output stack and on the scratch and target counters of the counter
program as follows. It runs $D$ Horner rounds, round $i$ with coefficient $\kappa_i$, base $N$,
accumulator $P$, product counter $Q$, index counter $AD$ and scratch counter $TMP$. It moves $P$
onto both $Mc$ and the target $iE$, moves $N$ onto both $Mc$ and the target $iX$, and adds one
unit to each of $Mc$ and $iX$. It adds $Mc$ to $B$, restoring $Mc$ through $TMP$, adds $c$ units
to $B$, $e$ units to $KC$ and one unit to $Tc$, and runs the power loop with base $B$, round
counter $KC$, accumulator $Tc$, product counter $Q$, index counter $AD$ and scratch counter
$TMP$. It adds $d$ units to $Dd$, adds $Dd \cdot Tc$ to $Fx$ (index counter $AD$, scratch
counter $TMP$) and adds $d + 1$ more units to $Fx$. It moves $Fx$ onto both $Hc$ and the target
$iF$ and moves $Mc$ onto $Hc$. Finally it moves $Tc$ onto each of the targets
$uT, sT, hT, aT, iT$, moves $Hc$ onto each of the targets $uH, sH, hH, aH$, and halts.

Started with $n$ on $N$ and every other counter empty, the program computes $P = k(n)$ by
Horner's rule, $m = n + 1 + k(n)$ on $Mc$, $T = (m + c)^e$ on $Tc$, $dT + d + 1$ on $Fx$ and
$m + dT + d + 1$ on $Hc$, and so loads the twelve target counters.
