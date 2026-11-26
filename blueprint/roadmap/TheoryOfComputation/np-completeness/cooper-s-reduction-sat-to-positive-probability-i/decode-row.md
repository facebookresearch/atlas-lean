# Decoding a table row

The row decoder reads, from the front of a bit string, a length $\ell$ in unary (ones ended by a
zero), then a numerator in unary after skipping the next $\ell$ bits, then a denominator in unary.
It returns the row made of those $\ell$ bits, the numerator and the denominator, together with the
unread suffix, and fails when a unary number is missing or fewer than $\ell$ bits follow the length.
