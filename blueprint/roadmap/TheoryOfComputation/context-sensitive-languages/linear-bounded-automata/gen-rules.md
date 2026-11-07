# Generation rules of the LBA grammar

The generation rules: the start symbol produces the first cell and the
generator (or, for a one-cell word, the first cell alone, tagged `both`);
the generator produces a middle non-head cell and itself, or a final
right non-head cell. The first cell of a longer word is tagged `left`.
