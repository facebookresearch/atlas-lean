# Zero-temperature SK Brownian control value

Use an integrable nonnegative, right-continuous, nondecreasing $\gamma$ on $[0,1)$, with zero extension away from that interval. At time $t\in[0,1]$ the control is bounded pointwise by one and is progressive for the natural filtration of Brownian increments after $t$. The payoff at state $x$ is the expected absolute value of $x+B_1-B_t+\int_t^1\gamma(s)a_{s-t}\,ds$, minus one half the expectation of $\int_t^1\gamma(s)a_{s-t}^2\,ds$. Take its real supremum over controls for $\Phi_\gamma(t,x)$. The functional minimized at zero temperature is $\Phi_\gamma(0,0)-\tfrac12\int_0^1t\gamma(t)\,dt$, and the state derivatives refer to that same value. The feedback diffusion and claims about its existence, value identities or minimizing measures are not part of the definition.

The value-identity formulation takes the order parameter as a real function, with monotonicity, nonnegativity and right-continuity on $[0,1)$ and integrability on $(0,1]$; it does not require the zero extension used by the full-support formulation. The associated process is the prescribed Brownian feedback diffusion. The finite scheme increments with Gaussian mesh steps and uses an independent terminal coordinate for the rounding sign. Derivatives are totalized as zero when the derivative fails to exist.

## Sources

- [Pinned source definition](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SKFullSupport.lean#L12-L66)
- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SKValue.lean#L10-L161)
