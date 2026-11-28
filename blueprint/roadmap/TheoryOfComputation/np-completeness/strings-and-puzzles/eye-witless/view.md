# View

For any natural coordinate $x$ and any closed walk on the grid, the view is the list of four [arm](arm.md) lengths on the walk's [edges](edges-of.md), in the order up, right, down, left, each capped at rows + cols. On `[[0, 0]]`, walking across and back gives `[0, 1, 0, 0]` at the left cell even with no eye and no cycle. When $x$ is an eye and the walk is a solution cycle, these are the arms the eye sees.
