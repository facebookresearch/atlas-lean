# Pair-frame splitter fails on malformed first-field framing

Let $x$ be a bit string no prefix of which is the framed form $1 p_1 \cdots 1 p_m 0$ of a bit string $p$, let $o$
be a bit string and $v$ a Boolean. Started at label read with internal state $v$, input $x$, left stack $o$ and
empty scratch stack, the [pair-frame splitter](prog.md) reaches label bad, with some internal state and some stack
contents, in at most $|x| + 1$ steps. The scratch stack may then hold part of the first field.
