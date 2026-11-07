# Control labels of the one-hot generator

For a natural number $g$, the labels are: a
precomputation label for each precomputation stage; for the time loop, a head, a rest label, a
multiplication label for each multiplication stage, and an end label; for the stack loop, a
head, a rest label, an emission label, two copy labels, a multiplication label for each
multiplication stage, and an end label; for the depth loop, a head, a rest label, two copy
labels, a multiplication label for each multiplication stage, and a drain label; for each
clause kind $c$ of a cell with $g$ symbol codes, a start label, two copy labels, a literal
label for each literal index $l < g$ and each literal stage, and a finishing label; and a
halting label.

The type is finite: each field ranges over a finite type (a stage, a clause kind of a cell with
$g$ symbol codes, or an index below $g$).
