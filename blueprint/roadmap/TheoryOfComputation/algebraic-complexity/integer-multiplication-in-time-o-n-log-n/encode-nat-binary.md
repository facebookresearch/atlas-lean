# Binary encoding of natural numbers

The binary encoding of a natural number $n$ is the
list of its base-$2$ digits, least significant first, with the digit $1$ written as the Boolean
value true and the digit $0$ as false. The list has no trailing zero digit, so $0$ is encoded by
the empty list.

Unlike the unary encoding, this encoding of $n > 0$ has length $\lfloor \log_2 n \rfloor + 1$,
which is the size model of the bit-complexity bound $O(n \log n)$ for integer multiplication;
with the unary encoding that bound could not hold.

## Sources

- Adapted from the AnnalsChallenge statement of Harvey and van der Hoeven's theorem (https://github.com/ImperialCollegeLondon/AnnalsChallenge, v1.0.0, commit e32eb14), which encodes natural numbers in unary with `Computability.encodeNat`; this binary encoding replaces it.
