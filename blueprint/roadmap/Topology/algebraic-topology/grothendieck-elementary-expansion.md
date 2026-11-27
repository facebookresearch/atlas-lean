# Elementary expansions of cellular models of a Grothendieck coherator

Let $C$ be a globular theory on finite globular pasting shapes, with structure functor preserving globular sums. Assume it is a coherator: it is an $\omega$-colimit starting at the initial theory, freely adjoining chosen fillers for families of parallel $n$-arrows into shapes of height at most $n+1$, and every such pair in $C$ admits a filler. A $C$-model is a presheaf taking the designated globular sums to pullbacks. Let $X$ be boundary-cellular, obtained from an initial model by a well-ordered colimit of stages freely attaching cells with specified full boundaries.

For every $n\ge0$ and map $D_n\to X$ from the representable $n$-disk, form a pushout of this map along the source-face inclusion $D_n\to D_{n+1}$. The resulting $i:X\to Y$ is a weak equivalence in the following precise sense: it bijects the quotients of 0-cells by being joined by a 1-cell and, at each 0-cell of $X$ and for every $n\ge0$, the quotients of based $(n+1)$-loops by being joined by an $(n+2)$-cell. Loops have both faces the iterated unit on the basepoint, using fillers of the parallel unit pairs. The pushout is a hypothesis of the statement.

## Depends on

- Globular sums, algebraic coherators and their models, free boundary attachments and based homotopy quotients.

## Proof depends on

- Elementary-expansion comparison on components and all based loop quotients, using the boundary-cellular hypothesis.

## Expansion

Build the disk and generating source face via Yoneda. Verify the shapes and model-cell universal properties, and isolate the invariance of the quotient sets under adding a disk along just its source. This is not the full homotopy hypothesis.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GrothendieckElementaryExpansion.lean#L465-L473) and [its definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GrothendieckElementaryExpansion.lean).
