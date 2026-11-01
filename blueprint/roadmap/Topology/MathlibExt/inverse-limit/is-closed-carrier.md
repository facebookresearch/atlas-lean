---
article_id: af_f93bc8d125adadfa5568cff9
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: InverseLimit.isClosed_carrier
---

# Is Closed carrier

The inverse limit set is closed in the product when every factor is
Hausdorff and every transition map is continuous. Each compatibility equation
`f h (x j) = x i` cuts out a closed set by `isClosed_eq`, and the limit is the
intersection of all of them.

## Depends on

- [Carrier](carrier.md)

## Sources

- [MathlibExt, MathlibExt.Topology.InverseLimit](../../../../sources/v2/MathlibExt.md)
