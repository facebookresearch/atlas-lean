# Stack alphabets of the SAT-to-3SAT emitter

The output stack of the emitter machine holds
Booleans; each of its other stacks (the token stack, the fresh counter, the two scratch counters
and the output clause count) holds symbols of the SAT verifier's token alphabet.

The counters are unary: they hold only the clause token.
