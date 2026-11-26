# A halted costed RAM run gives an output of the RAM semantics

Let a RAM program be run from the initial state for the inputs for at most a given budget of steps,
with cost annotations. If the resulting program counter is at or past the end of the program and the
accumulator holds $y$, then $y$ is an output of the program on these inputs under the partial RAM
semantics, which returns the accumulator at the least number of steps after which the program
counter has left the program.
