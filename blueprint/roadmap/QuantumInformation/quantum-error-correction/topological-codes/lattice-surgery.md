# Lattice surgery

Let two [planar surface code](planar-surface-code.md) patches of distance $d$ each encode one logical qubit, side by side
with a row of fresh qubits between two of their boundaries of the same type. A *rough merge* prepares the intermediate
qubits in $|0\rangle$ and then measures the check operators of the merged patch, which include new $X$-type checks
spanning the join; repeating this for $d$ rounds of error correction determines reliably the product of these new checks,
which equals the logical operator $\bar X_1 \bar X_2$, so the merge is a measurement of $\bar X_1 \bar X_2$ and leaves a
single patch. A *smooth merge*, with the intermediate qubits prepared in $|+\rangle$ across the other boundaries,
measures $\bar Z_1 \bar Z_2$. A *split* measures the intermediate qubits and cuts the joint checks, turning one patch into
two. With single-patch operations, these joint Pauli measurements give logical CNOT and the other Clifford operations on
planar patches with only nearest-neighbour checks.

## Expansion

A sound expansion states the merge and split as maps on the encoded state: after a rough merge with outcome $m$ the logical
state is projected by $(I + (-1)^m \bar X_1 \bar X_2)/2$, with the Pauli frame corrections for the measured new checks and
an odd number of unreliable syndromes along the join; it needs the stabilizer measurement rule for the new checks and the
logical operators of the planar code. Horsman et al. derive these maps in the stabilizer formalism (Sections 3.1–3.4) and
build CNOT from them (Section 4); each step is a page to write and check.

## Depends on

- [Planar surface code](planar-surface-code.md)
- [Positive-operator-valued measurements and the Born rule](../../quantum-operations/povms-and-measurement-readout/povm-and-born-rule.md)

## Sources

- C. Horsman, A. G. Fowler, S. Devitt and R. Van Meter, *Surface code quantum computing by lattice surgery*, New J. Phys. 14 (2012), 123011, arXiv:1111.4022, Section 3 (lattice merging and splitting, "The merge procedure described above is thus equivalent to measuring $X_L X_L$" and the smooth merge) and Section 4.
