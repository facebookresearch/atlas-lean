# Labels of the clocked universal machine

The labels of the program of the clocked
universal machine: the tape update (`act0`–`act3`, `wr0`, `wr1`, `mvL0`–`mvL3`, `mvR0`–`mvR3`)
and the clock tick `fin`; the scan, which starts at `sc0` and has labels for the state
(`rq0`–`rq2`; `cqA o` and `cqB o` for each comparison outcome `o`; `sq0 m` and `sq1 m` for each
bit `m`), for the head cell (`ra0`–`ra2`; `caA o`, `caB o`; `sa0 m`, `sa1 m`), for skipping the
rest of an entry (`sk3a`, `sk3b`, `sk2a`, `sk2b`, `sk1a`, `sk1b`) and for reading a match
(`rd0`–`rd7`); the restores `rs` and `nf`; the exits `hlt` and `tmo`; the parse of the encoded
input (`pc0`, `pc1`, `px0`–`px6`, `pk0`); and the output phase (`o1`–`o6`, `done`).
