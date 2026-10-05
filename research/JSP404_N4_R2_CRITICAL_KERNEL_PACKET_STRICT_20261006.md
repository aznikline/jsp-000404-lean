# Necessary four-packet lemma: strict and normal receipt (2026-10-06)

**SCOPED PASS — necessary packet property only.** `Jsp404.N4R2CriticalKernel.model_packet_monotone` passed actual Lean `--trust=0` and the actual Lake module target with exit0. Both print only `propext`, `Classical.choice`, `Quot.sound`. The source and this receipt are frozen.

| Check | Seconds | Maximum RSS |
|---|---:|---:|
| strict0 | 3.84 | 2.913 GiB |
| real Lake target | 6.61 | 2.913 GiB |

For any GenericModel and ordered a<b<c<d, the four actual triangle fields imply one of the eight words `0000,0001,0011,0111,1000,1100,1110,1111` in packet order `(abc,abd,acd,bcd)`. The ordinary proof internally covers all16 triangle-arm choices. Eight permitted choices construct the disjunction; the other eight produce strict shared-chord cycles closed by linarith. No orientation mask is supplied by the caller and no new Model field is assumed.

Source: `Jsp000404/N4R2CriticalKernelPacket.lean` (4,469 bytes). Actual logs: `.lake/n4-r2-critical-kernel-packet-strict-20261006.log` and `.lake/n4-r2-critical-kernel-packet-normal-20261006.log`. The JSON binds the final source, actual compiled artifacts, real trace/hash files and logs by SHA-256. New scope warnings are0; existing dependency warnings are replayed in the normal output.

The accompanying Boolean packet-propagation diagnostic counted24,698 complete assignments for35 triples/35 packets at m7 in5.289816 seconds. It counts only packet consistency. It is not a theorem that every word is realizable, not a check of all real corridor/floor constraints, and not an inverse Model/signotope equivalence.

**No eight-point exclusion or full R2 n4 capacity is proved by this module.** The27 earlier RAW UNSAT cases remain diagnostics. The next exporter may use this checked necessary lemma for valid structural propagation, while every remaining direction alternative and every floor-score case still needs ordinary proof coverage.
