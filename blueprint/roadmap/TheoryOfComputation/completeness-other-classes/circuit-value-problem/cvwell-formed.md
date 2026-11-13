# Well-formed encoded circuits

A list $C$ of encoded gates, each a (kind, references)
pair, is well formed as a circuit on $n$ inputs when the flat Boolean circuit on $n$ inputs
obtained by decoding each pair of $C$ is well formed: every decoded gate references only strictly
earlier gates.
