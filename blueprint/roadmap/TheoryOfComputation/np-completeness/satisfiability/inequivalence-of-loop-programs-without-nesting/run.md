# Run

Runs a program on the store `s`. The second argument is `none` outside a loop and `some (x, b)`
inside `loop x`, with `b` the body read so far; at the matching `end` the body runs `s x` times,
`s` being the store on entering the loop.
