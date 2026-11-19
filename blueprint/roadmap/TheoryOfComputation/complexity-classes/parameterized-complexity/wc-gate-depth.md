# Depth of one encoded gate

Let $d = (d_0, d_1, \dots)$ be a list of natural numbers
(the depths of earlier gates), where $d_a$ is read as $0$ when $a$ is out of range, and let
$(c, r)$ be a gate encoded as a (kind, references) pair. Its depth is $0$ if $c = 0$ or $c = 1$
(an input or constant gate), and otherwise one plus the maximum of $d_a$ over the entries $a$ of
$r$, the maximum over no entries being $0$.
