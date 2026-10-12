# DIAGNOSTIC_NOT_PROOF
`S8N8CoreSlice_F1.lean.txt` and `S8N8CoreSlice_F2.lean.txt` are the original S8N8Core memory-diagnostic slices, byte for byte (renamed from `.lean` to `.lean.txt` at publication).
They contain `sorry` on purpose, to measure elaboration cost. They are not proofs and not accepted sources; nothing imports them and no acceptance relies on them.
Their raw run evidence is still logs/18_diag_S8N8Core_slice_F{1,2}.log(.receipt.json). Those receipts name the old `.lean` path.
sha256:
4eb5112c2dc832a7cb8a62216d7c3997a45be10bf2b2021bad24d61ae34441f8  verification/r1-interfaces-20261012/probe/S8N8CoreSlice_F1.lean.txt
7ccda6676ac48ae87b0244d604bece3ff83974b087829314f723289f574dc5f9  verification/r1-interfaces-20261012/probe/S8N8CoreSlice_F2.lean.txt
The other probe/*Slice*.lean files are also diagnostic only. They contain no sorry/admit/native_decide, and none of them counts toward acceptance.
