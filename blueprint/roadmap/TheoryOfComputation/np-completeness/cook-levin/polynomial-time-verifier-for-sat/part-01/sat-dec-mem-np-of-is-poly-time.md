# SAT is in NP if its verifier is polynomial-time

If the function sending a pair $(x, w)$
of lists of Booleans to the Boolean returned by the SAT verifier on $(x, w)$ is polynomial-time
computable, by a multi-stack Turing machine under the canonical bitstring encodings, then the
SAT decision problem belongs to NP.

This hypothesis must be proved separately: it does not follow from the polynomial bound on the
SAT verifier's declared time, which constrains only a trusted cost annotation and leaves the
decoding of the input uncharged.
