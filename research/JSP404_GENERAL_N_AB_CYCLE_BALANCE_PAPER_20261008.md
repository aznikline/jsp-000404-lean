# General-n A/B: safe certificate lifting and the exact missing bridge

PAPER only, 2026-10-08. Read-only source inspection; no Lean, solver, numerical search, certificate generation, or Lean-source edit was performed. This note proves a conditional certificate-lifting lemma. It proves neither general-n A/B exclusion nor a scalar SAT example at n5.

## Where n first enters

- SatScalarModel.lean:27–28: the upper corridor is d_ij <= theta_j+n+delta-1. The lower corridor, strict theta ordering, and triangle alternatives at lines 29–31 do not contain n.
- SatScalarModel.lean:37–38: rowDefect is n minus the full linear-gap score, whose right endpoint is theta_i+n+delta.
- SixOuterReplay.lean:43 and 79–81: the fixed wrap lower arc uses constant 4-L. At general n this is n-L.
- SixOuterReplay.lean:98–99: the fixed upper-corridor arc uses constant 3 and coefficient 1 of delta. At general n its constant is n-1.
- SixOuterFloorProfiles.lean:127–129: the exact score-plus-defect identity is currently exported only at n4, with right side 4.
- SixWeakOuterFloorProfiles.lean:55–57 and 68–74: positivity and the 15 weak-two profiles use that fixed-n4 identity. The source interfaces themselves are not yet parameterized.
- N4R2ThinReplay.lean:136–140: acceptance uses cycle closure, B>=0, A+B<=0, and either A+B<0, B>0, or a strict edge.

The ten triangle arms and their order catalog are combinatorially n-free. The currently checked catalog export still has a fixed-n4 model type; no new generic API is claimed here.

## One reusable lemma: residual-balanced cycle lifting

Let n>=4 and 0<=delta<1. Fix the same closed directed cycle, origins, direction word, full row orders, and strict flags as an accepted n4 lower-only certificate. Write its original summed weight as

\[
W_4(\delta)=A+B\delta.
\]

Assume that every lower-gap occurrence e has a valid general-model lower bound

\[
L_e(n)=L_e(4)+t_e,\qquad t_e\ge0.
\]

Counts and sums below include repeated edge occurrences. Let U be the number of upper-corridor occurrences, Z the number of wrap-gap-lower occurrences, and T=sum_e t_e over all lower-gap occurrences. Then the exact general-model cycle weight is

\[
W_n(\delta)=A+B\delta+(U+Z)(n-4)-T.
\]

Consequently, the original accepted certificate remains contradictory whenever

\[
T\ge (U+Z)(n-4).
\]

Proof. An upper corridor changes 3 to n-1, adding n-4. A wrap lower arc changes 4-L_e(4) to n-L_e(n), adding n-4-t_e. A non-wrap lower arc changes -L_e(4) to -L_e(n), subtracting t_e. All other allowed origins are unchanged. Summing gives the displayed identity. Under the balance condition, W_n<=W_4. The n4 acceptance conditions make W_4<0 for delta<1 whenever A+B<0 or B>0; otherwise W_4=0 and a retained strict edge makes the summed inequality strict. In either case cycle closure gives a contradiction. This is a statement about valid actual GenericModel inequalities, not about a solver label.

An equivalent affine form sets t_e=alpha_e(n-4). It suffices that

\[
Q=U+Z-\sum_e\alpha_e\le0.
\]

At n=4 every extra term vanishes: n-1=3 and n=4 recover the checked decoder exactly. With unchanged lower profiles, T=0 and the old cycle acquires the nonnegative term (U+Z)(n-4). A positive slope prevents an automatic all-n lift. It does not prove failure already at n5: a particular cycle may retain enough negative slack. It certainly does not prove scalar SAT.

## The precise missing bridge

For complete nonnegative row gaps g_k summing to n+delta, let s_k=max(floor(g_k)-1,0). Then S=sum s_k<=sum floor(g_k)<=n, so the natural subtraction in rowDefect is exact and S+rowDefect=n. Therefore the same defect bounds require scores n-2/n-3 for A and n-2/n-2 for B, rather than the n4 scores 2/1 and 2/2.

For n>=4 the old 15 weak-two and five positive-cell profiles remain necessary weaker consequences, but their fixed lower bounds do not supply T. A sound general-n extension needs an internally produced full-gap profile that accounts for the remaining n-4 score units, together with a certificate selection whose used lower-bound increments satisfy the balance inequality. Those units may be distributed among several gaps; it is not justified to place them all in one chosen gap. No unchecked caller profile or capacity premise may supply this bridge.

No n5 full-floor GenericModel witness was constructed. The current defensible conclusion is: n4 A/B cannot be directly reused; certificate soundness has the safe parameter-balanced extension above, while actual profile production plus balanced certificate coverage is still missing. True scalar SAT from n5 onward is not established by this note. A later separately authorized search would have to verify the full sorted row multisets and actual floor defects, not just weakened gap inequalities; planar realizability would be a further question because GenericModel contains no such field.
