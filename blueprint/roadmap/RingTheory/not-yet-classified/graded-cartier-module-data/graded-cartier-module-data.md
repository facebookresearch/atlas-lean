# Graded Cartier module data

For a prime `p`, a commutative ring `B` and
a ring map `j : Zp2 p →+* B`: a module `M` over `WittVector p B` with additive
maps `F` (`frobenius`) and `V` (`verschiebung`), a `WittVector p B`-linear map
`ϖ` (`varpi`) and submodules `piece 0` and `piece 1`, such that, writing `σ`
for the Frobenius of `WittVector p B`, `F (w • x) = σ w • F x`,
`w • V x = V (σ w • x)`, `V (w • F x) = WittVector.verschiebung w • x`,
`F (V x) = p • x`, `ϖ (V x) = V (ϖ x)`, `ϖ (F x) = F (ϖ x)` and
`ϖ (ϖ x) = p • x`; the two pieces are complementary, and `F`, `V` and `ϖ` each
map `piece i` into `piece (i + 1)`. No field involves `j`: with the pieces it
determines how the Teichmüller representatives of `Zp2 p` act
(`teichmullerAct`), and a map along a ring map `φ` (`IsBaseChangeAlong`) goes
to data with coefficient map `φ.comp j`.
