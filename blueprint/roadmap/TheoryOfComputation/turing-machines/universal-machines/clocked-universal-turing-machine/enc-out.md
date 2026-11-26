# Output encoding of the clocked universal machine

The output bits of an optional list of
numbers: no result (a timeout) is encoded as the single bit false, and a result $l$ is encoded as
the bit true followed by the cells of $l$, where a number $n$ is written as $n$ bits true followed
by one bit false.
