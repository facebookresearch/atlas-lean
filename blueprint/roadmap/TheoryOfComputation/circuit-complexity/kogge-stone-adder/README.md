# Kogge–Stone adder

## Appending a block of gates

- [Appending a block of gates](append-gates.md)
- [Appending gates keeps the old gate values](append-gates-eval-lt.md)
- [Appending one more gate keeps the earlier gate values](append-gates-eval-le.md)
- [Values of appended gates](append-gates-eval-ge.md)

## Generate and propagate

- [Combining generate–propagate pairs](combine.md)
- [Generate and propagate signals of a bit](gp-bit.md)
- [Generate and propagate signals of a block](gp-range.md)
- [Adjacent blocks compose](gp-range-add.md)
- [The carry out of a block of bits](carry-add.md)
- [Lowest bit of a Kogge-Stone block](low-bit.md)
- [The block held after Kogge-Stone levels](gp-spec.md)
- [The Kogge-Stone step](gp-spec-succ.md)
- [Carries from the Kogge–Stone prefixes](carry-of-gp-spec.md)

## The circuit

- [Gate count of the first Kogge-Stone levels](level-base.md)
- [Index of the generate gate](g-num.md)
- [Propagate gate of a bit in the Kogge–Stone adder](p-num.md)
- [Kogge–Stone partner bit](partner.md)
- [Gates of level 0](line0.md)
- [Gates of a Kogge-Stone level](line-k.md)
- [The first Kogge-Stone levels](levels.md)
- [Gates of the final level](line-f.md)
- [Gates of the carry-lookahead adder](cla-program.md)
- [Kogge–Stone carry-lookahead adder](carry-lookahead-adder.md)
- [Number of carry-lookahead levels](cla-levels.md)

## Correctness

- [Level 0 computes generate and propagate](levels-zero-eval.md)
- [Each Kogge-Stone level is correct](levels-eval.md)
- [Level-0 gates are unchanged by later levels](levels-eval-base.md)
- [The carry gates](cla-program-carry.md)
- [The sum gates](cla-program-sum.md)
- [Sum bits of the carry-lookahead adder](carry-lookahead-adder-sum.md)
- [Carry out of the carry-lookahead adder](carry-lookahead-adder-carry.md)
- [Gate count of the carry-lookahead adder](carry-lookahead-adder-size.md)

## Depth as evaluation

- [The depth interpretation](depth-interpretation.md)
- [Gate depths are evaluation in the depth interpretation](depths-eq-eval.md)
- [Depth of an arithmetic gate](depth-interpretation-arith.md)

## Depth of the adder

- [Depths after each level](levels-depth.md)
- [Depth of the carry gates](cla-program-carry-depth.md)
- [Depth of the sum gates](cla-program-sum-depth.md)
- [Exact depth of the carry-lookahead adder](carry-lookahead-adder-depth.md)
- [Depth of the carry-lookahead adder with logarithmically many levels](carry-lookahead-adder-depth-cla-levels.md)

## Depth of the ripple-carry adder, for comparison

- [Carry depth in the ripple-carry adder](carry-depth.md)
- [Gate-depth formula for the ripple-carry adder](gate-depth.md)
- [Gate depths of the ripple-carry adder](rca-program-depth.md)
- [The ripple-carry adder has linear depth](ripple-carry-adder-depth.md)
