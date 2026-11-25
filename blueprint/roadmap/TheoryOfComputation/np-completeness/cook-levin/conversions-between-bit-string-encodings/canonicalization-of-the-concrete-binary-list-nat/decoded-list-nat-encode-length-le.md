# Re-encoded decoded list of naturals is linear in raw input

For every bit string $x$, if the [decoder of lists of natural numbers](decode-list-nat.md) returns a list $a$ on
$x$, then the canonical code of $a$ has length at most $3|x|$. The bound depends on $|x|$ only, not on the sizes of
the decoded numbers.
