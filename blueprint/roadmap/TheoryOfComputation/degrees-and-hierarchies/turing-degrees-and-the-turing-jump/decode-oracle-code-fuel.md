# Fuel-indexed decoder of oracle codes

Write $\langle a, b \rangle$ for the pairing
bijection $\mathbb{N} \times \mathbb{N} \to \mathbb{N}$ of the Gödel numbering. Given a fuel $f$,
a tag $t$ and a payload $p$, the decoder either returns an oracle code or fails; to decode a
number $n = \langle n_1, n_2 \rangle$ with fuel $f$ means to run it with fuel $f$, tag $n_1$ and
payload $n_2$. With fuel $0$ it fails. With fuel $f + 1$, writing $p = \langle p_1, p_2 \rangle$:
if $p = 0$ and $t$ is $0$, $1$, $2$, $3$ or $8$, it returns the instruction zero, successor, left
projection, right projection or oracle query respectively; if $t$ is $4$, $5$ or $6$, it decodes
$p_1$ and $p_2$ with fuel $f$ and, when these give codes $a$ and $b$, returns the pairing,
composition or primitive recursion code built from $a$ and $b$ respectively, failing otherwise;
if $t = 7$, it decodes $p$ with fuel $f$ and, when this gives a code $a$, returns the unbounded
search code built from $a$, failing otherwise; in all other cases it fails.

The recursion is structural in the fuel and uses no classical choice, so the decoder is a
computable function; with enough fuel it inverts the Gödel numbering of oracle codes.

## Sources

- Rogers, *Theory of Recursive Functions and Effective Computability*, §1.6 (Gödel numberings; decoding).
