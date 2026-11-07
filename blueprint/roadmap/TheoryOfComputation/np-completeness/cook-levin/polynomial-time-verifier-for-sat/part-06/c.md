# Driver labels in the SAT host

The map from the labels of the clause-check driver (its
own labels and those of the lookup embedded in it) to the host labels sends the driver's label
for the answer yes to the cleanup label with answer true, its label for the answer no to the
cleanup label with answer false, and every other label $l$ to the host label running the
driver at $l$.
