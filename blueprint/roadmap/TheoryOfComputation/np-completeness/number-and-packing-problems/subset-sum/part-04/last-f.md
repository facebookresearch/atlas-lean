# Whether a bit string ends in false

For a Boolean $z$ and a list of bits $p$, the value
is $z$ when $p$ is empty and the negation of the last bit of $p$ otherwise. So if $z$ records
whether the bits read so far end in false, the value records whether those bits followed by $p$
end in false.

With $z$ false the value is true exactly when $p$ is non-empty and ends in false, that is, when
$p$ is not the canonical binary code of a number, least significant bit first.
