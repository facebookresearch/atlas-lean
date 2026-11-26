# Interactive reductions and round-by-round (knowledge) soundness

An **interactive reduction** from a relation $R_{\mathrm{in}}$ to $R_{\mathrm{out}}$ is a public-coin protocol in which a prover holding $(x,w)\in R_{\mathrm{in}}$ and a verifier holding $x$ interact for a fixed sequence of rounds, after which the verifier outputs a new statement $x'$ and the prover a witness $w'$. It is **round-by-round sound** with errors $\varepsilon_i$ if there is a 'doomed' predicate on partial transcripts, true initially when $x\notin L(R_{\mathrm{in}})$, such that from any doomed state the next verifier challenge leaves it doomed except with probability $\varepsilon_i$, and a doomed full transcript yields $x'\notin L(R_{\mathrm{out}})$. It is **round-by-round knowledge sound** if moreover a straight-line extractor maps each prefix and an output witness to an input witness so that a successful round can be explained. Round-by-round knowledge soundness implies knowledge soundness and soundness with error $\sum_i\varepsilon_i$.

## Depends on

- [Public-coin interactive proofs](../../goldwasser-sipser-theorem/pub-ip.md)

## Sources

- Ran Canetti et al., "Fiat–Shamir: From Practice to Theory", Proceedings of the 51st Annual ACM SIGACT Symposium on Theory of Computing, 2019.
- Eli Ben-Sasson, Alessandro Chiesa and Nicholas Spooner, "Interactive Oracle Proofs", Theory of Cryptography – TCC 2016-B, Part II, 2016.
- Alessandro Chiesa and Eylon Yogev, "Building Cryptographic Proofs from Hash Functions", 2024.
