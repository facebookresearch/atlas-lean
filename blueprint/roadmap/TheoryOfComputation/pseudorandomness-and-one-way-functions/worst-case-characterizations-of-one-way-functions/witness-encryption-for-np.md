# Witness encryption for an NP relation

A **witness encryption** scheme for an $\mathsf{NP}$ language $L$ with witness relation $R_L$ is a pair of probabilistic polynomial-time algorithms $(\mathrm{Enc},\mathrm{Dec})$: $\mathrm{Enc}(1^\lambda,\varphi,m)$ encrypts a bit $m$ under an instance $\varphi$, and $\mathrm{Dec}(c,w)$ decrypts. **Correctness:** if $(\varphi,w)\in R_L$ then $\mathrm{Dec}(\mathrm{Enc}(1^\lambda,\varphi,m),w)=m$ with overwhelming probability. **Security:** for every $\varphi\notin L$, the distributions $\mathrm{Enc}(1^\lambda,\varphi,0)$ and $\mathrm{Enc}(1^\lambda,\varphi,1)$ are computationally indistinguishable; it is **subexponentially secure** if distinguishers of size $2^{\lambda^{c}}$ have advantage at most $2^{-\lambda^{c}}$ for some constant $c>0$. Subexponentially secure witness encryption follows from subexponentially secure indistinguishability obfuscation, which Jain, Lin and Sahai built from well-founded assumptions.

## Depends on

- [One-way function families](../../complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)

## Sources

- Yizhi Huang, Rahul Ilango and Hanlin Ren, "NP-Hardness of Approximating Meta-Complexity: A Cryptographic Approach", STOC (2023), ECCC TR23-046.
