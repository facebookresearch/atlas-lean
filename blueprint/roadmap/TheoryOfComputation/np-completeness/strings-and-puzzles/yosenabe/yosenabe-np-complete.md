# YOSENABE is NP-complete

Statement: the decision problem YOSENABE belongs to NP, and every decision problem $L$ in NP is polynomial-time many-one reducible to it: there is a function $f$ from bitstrings to bitstrings, computable in polynomial time, such that $x \in L$ exactly when $f(x)$ is accepted, for every bitstring $x$.

An instance is a rectangular grid in which some cells are gray, some gray areas (maximal sets of side-connected gray cells) are labelled with numbers, and some non-gray cells contain circles with positive numbers. The question is whether arrows can be drawn vertically or horizontally from all circles to gray areas so that the arrows do not bend and do not cross other circles or lines of other arrows, the label of each labelled gray area equals the total of the numbers of the circles entering it, and at least one circle enters each gray area.

## Sources

- C. Iwamoto, "Yosenabe is NP-complete", *Journal of Information Processing* 22(1) (2014), 40–43, <https://doi.org/10.2197/ipsjjip.22.40>.
