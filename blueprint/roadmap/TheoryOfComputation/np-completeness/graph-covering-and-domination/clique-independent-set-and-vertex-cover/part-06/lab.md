# Labels of the KG-map machine

The type of the ten instruction labels of the KG-map
machine: read $k$, read $n$, move the pair bits, subtract, output the pair bits, output $n$, write
the separator, output the last number, the failure label and the halting label.

The machine reaches the subtraction label only in the vertex-cover mode, and at the failure label
it writes the fixed no-instance.
