# Polynomial-time hitting lists for noncommutative rational formulas

There is one deterministic finite-state one-tape machine with a four-symbol alphabet (blank, the two output bits, and a work symbol) and positive integers $C,k$ with the following property. On unary input $1^n 0 1^s$ with $n,s\ge1$ it halts within $C(n+s+1)^k$ transitions. Its right tape, starting at the head, gives an encoded list of rational matrix tuples of one common positive dimension; that dimension and the full binary output length are both at most $C(n+s+1)^k$.

Formulas use rational scalars, $n$ variables, binary addition and ordered multiplication, and unary inverse, with size the node count. Evaluation is defined only when every inverse gate has a two-sided inverse. For every size-at-most-$s$ formula admissible at some positive matrix dimension and nonzero at some defined rational matrix evaluation, the list contains a tuple at which evaluation is defined and is invertible. Encode dimension and list length followed by the entries in tuple/row/column order; a rational uses its sign and the encodings of its reduced absolute numerator and positive denominator, and natural numbers use a unary bit-length, a zero terminator and the little-endian binary digits.

## Depends on

- Partial formula semantics, finite-tape transition costs and the explicit full-output encoding.

## Proof depends on

- Uniform rational hitting construction producing invertible hits, and simulation of the generator with the stated unary input and bit-time accounting.

## Expansion

Prove the semantic bridge to the free-skew-field construction and separate invertibility from mere nonzeroness. Derive the dimension, output length and transition bound for one common exponent and machine.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/RationalHitting.lean#L108-L110) and [its definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/RationalHitting.lean).
