# Explore Tree

The geometric exploration tree: a single-pass exploration from the initial
discovered set. It is sound (every discovered vertex is connected to `B`, via
`geomInv`) but does not in general discover the whole open connected component;
completeness is the subject of `TreeComplete`, not this tree.
