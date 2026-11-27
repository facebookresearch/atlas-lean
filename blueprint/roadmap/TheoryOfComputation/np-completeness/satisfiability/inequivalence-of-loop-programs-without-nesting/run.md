# Run

Runs a program on a store by one left-to-right scan. The second argument is `none` outside a loop and `some (x, b)` inside `loop x`, with `b` the buffer read so far.

- At the end of the program, return the current store; an unfinished buffer is discarded, so an increment inside a `loop` without its `end` need not execute.
- Outside a loop, opcode `3` starts a buffer for its variable; every other instruction is applied by [`step`](step.md).
- Inside a loop, every instruction other than `4` is buffered, even another `3`. On `4`, the buffered instructions are folded left to right with `step`, as many times as the current value of the stored loop variable, and the scan resumes outside the loop.

There is no recursive evaluation of nested loops.
