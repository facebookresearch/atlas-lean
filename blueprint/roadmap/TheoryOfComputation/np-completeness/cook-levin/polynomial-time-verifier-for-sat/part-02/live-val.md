# Live value of a name in a table

Given a list of table entries, each pairing a name (a
bit string) with either a boolean value or no value, and a bit string $q$, the live value of
$q$ is the value of the first entry whose name is $q$ and which carries a value, or false if
there is no such entry.
