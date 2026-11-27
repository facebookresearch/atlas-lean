# Register evaluation of straight-line programs is black pebbling

Let $P$ be a straight-line program and let $G_P$ be its computation DAG (inputs are sources; the arguments of a gate are its predecessors). A *register evaluation* of $P$ with $k$ registers is a sequence of moves each of which loads an input into a free register, computes a gate whose argument values are all held in registers into a free register, or frees a register, never occupying more than $k$ registers, and ending with the values of all outputs held in registers. Then $P$ has a register evaluation with $k$ registers if and only if $G_P$ admits a black pebbling strategy (without sliding) with at most $k$ pebbles that ends with every output vertex pebbled: the occupied registers at each time are exactly the pebbled vertices.

## Proof sketch

Translate moves one to one: loading an input or computing a gate is placing a pebble on a vertex all of whose predecessors carry pebbles, and freeing a register is removing a pebble.

## Depends on

- [Straight-line programs and circuits over a basis](straight-line-program-over-a-basis.md)
- [Black pebble game and black pebbling price](../../../../complexity-classes/space-and-time-complexity/space-bounded-computation/pebble-games/black-pebble-game.md)

## Sources

- Ravi Sethi, "Complete Register Allocation Problems", SIAM Journal on Computing 4(3), 226–248, 1975.
- John E. Savage, "Models of Computation: Exploring the Power of Computing", Addison-Wesley, 1998, Chapter 10.
