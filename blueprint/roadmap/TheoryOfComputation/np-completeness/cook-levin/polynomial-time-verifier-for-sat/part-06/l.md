# Lookup labels in the clause-check driver

The relabelling that places the lookup's labels
among the driver's labels, whose label set consists of the driver's own labels together with the
lookup's labels: the lookup's final label $\mathsf{done}$ goes to the driver's return label
$\mathsf{ret}$, and every other lookup label $l$ goes to the copy of $l$ among the lookup's
labels.
