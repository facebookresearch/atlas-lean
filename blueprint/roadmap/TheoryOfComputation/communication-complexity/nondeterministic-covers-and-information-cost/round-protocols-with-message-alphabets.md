# Round protocols with messages from an alphabet

A *round protocol* with message alphabet $M$ and at most $d$ messages is a protocol in which, at each step, the player to speak (determined by the previous messages) sends one symbol of $M$ computed from their input and the transcript so far, and the output is a function of the full transcript. Bit protocols of depth $d$ are round protocols with $M = \{0,1\}$ and $d$ messages; a round protocol with at most $d$ messages over a finite nonempty $M$ is simulated by a bit protocol of depth $d \lceil \log_2 |M| \rceil$, by encoding each symbol in $\lceil \log_2 |M| \rceil$ bits. Counting messages rather than bits measures round complexity, as in protocols with few rounds and in Karchmer–Wigderson round games.

## Depends on

- [Deterministic two-party protocol](../deterministic-communication-protocols/protocol.md)

## Sources

- E. Kushilevitz and N. Nisan, "Communication Complexity", Cambridge University Press, 1997.
