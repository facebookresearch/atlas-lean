# Correspondence of labels between the code evaluator and the wrapped machine

Let $c$ be a
code for a partial recursive function on lists of natural numbers and let $\mathrm{tr}$ be
Mathlib's multi-stack machine that evaluates such codes. An optional label $o$ of $\mathrm{tr}$
(a label, or none for halting) corresponds to an optional label $o'$ of the wrapped machine for
$c$ when either $o$ is none and $o'$ is the first post-phase label $\mathrm{post}_1$, or $o$ is a
label $l$ of $\mathrm{tr}$ that lies in the support $\mathrm{supp}(c)$ of $c$ and $o'$ is $l$,
read as a label of the wrapped machine.
