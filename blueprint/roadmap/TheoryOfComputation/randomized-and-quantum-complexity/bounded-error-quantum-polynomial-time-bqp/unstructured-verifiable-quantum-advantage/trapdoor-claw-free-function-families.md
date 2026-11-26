# Trapdoor claw-free function families

A *trapdoor claw-free function family* consists of efficiently sampleable pairs of injective functions $f_{k,0}, f_{k,1} : \mathcal{X} \to \mathcal{Y}$ with the same image, such that (i) given the key $k$ it is computationally hard (for the relevant adversaries) to find a *claw* $(x_0, x_1)$ with $f_{k,0}(x_0) = f_{k,1}(x_1)$; (ii) given a trapdoor $t_k$, both preimages of any image point can be computed efficiently; and (iii) in the *adaptive hardcore bit* variant, it is hard to produce simultaneously an image $y$, a bit $b$ with a preimage $x_b$, and a nontrivial string $d$ with $d \cdot (x_0 \oplus x_1)$ correctly predicted.

## Sources

- Zvika Brakerski, Paul Christiano, Urmila Mahadev, Umesh Vazirani, Thomas Vidick, "A cryptographic test of quantumness and certifiable randomness from a single quantum device", FOCS (2018), Journal of the ACM 68(5) (2021); arXiv:1804.00640.
