/-!
# Staircase falsification checker (B′ step 2)

Numerical audit of the `StaircaseBound` tail-count constraints on
numerically generated center configurations.  For `s` centers we compute,
at each center `oᵢ`, the cyclic gaps `φⱼ` (in units of `π`) between
consecutive directions `oᵢ oⱼ` mod `π`, then

  `k'(i) = Σⱼ max(⌊u·φⱼ/2⌋ - 1, 0)`,   `u = 2n + 2δ`,

and check the conjectured tail bounds

  `N(m) = #{i : k'(i) ≥ m} ≤ n - m`   for `n+2-s ≤ m ≤ n-1`

with the `δ ≥ 1/2` bottom-level relaxation `N(n+2-s) ≤ s-1`, and the
resulting sum bound `Σᵢ 2^{k'(i)}`.

Legality proxy: optionally keep only configurations whose maximal
triangle angle among centers is `≤ π - 2π/u` (the trivial-GC analogue of
the `maxGA ≤ π - λ` premise).

Deterministic LCG sampling; run with `lean --run`.
-/

/-- π as a Float literal (Lean core has no `piF`). -/
def piF : Float := 3.141592653589793

/-- LCG (Numerical Recipes constants). -/
def lcgNext (s : UInt64) : UInt64 :=
  s * 6364136223846793005 + 1442695040888963407

def rand01 (s : UInt64) : Float × UInt64 :=
  let s' := lcgNext s
  ((s' >>> 11).toFloat / (2.0 ^ 53), s')

structure Pt where
  x : Float
  y : Float
  deriving Inhabited

/-- Direction (mod π) of `b - a` in `[0, π)`: `atan(dy/dx)` folded. -/
def dirModPi (a b : Pt) : Float :=
  let t := Float.atan ((b.y - a.y) / (b.x - a.x))
  if t < 0 then t + piF else t

/-- Cyclic gaps (in units of π, so they sum to 1) between consecutive
sorted directions. -/
def gaps (ds : Array Float) : Array Float :=
  Id.run do
    let n := ds.size
    let mut out := #[]
    for i in [:n] do
      let a := ds[i]!
      let b := if i + 1 < n then ds[i + 1]! else ds[0]! + piF
      out := out.push (b - a)
    return out

/-- `k'(i) = Σⱼ max(⌊u·φⱼ/2⌋ - 1, 0)`; `φⱼ` are radian gaps (sum = π),
so the normalized gap `φ/π` enters `⌊u·(φ/π)/2⌋ = ⌊u·φ/(2π)⌋`. -/
def kPrime (u : Float) (φs : Array Float) : Nat :=
  φs.foldl (fun acc φ =>
    let t := Float.floor (u * φ / (2.0 * piF))
    acc + max (t.toUInt64.toNat - 1) 0) 0

/-- Tail count `#{i : kᵢ ≥ m}`. -/
def tailCount (ks : Array Nat) (m : Nat) : Nat :=
  ks.foldl (fun acc k => acc + if m ≤ k then 1 else 0) 0

/-- Max/min triangle angle among a point set, via `atan2(|cross|, dot)`.
Per (4.12), every center-triangle angle lies in `[2π/u, π - 2π/u]`. -/
def angleOf (a b c : Pt) : Float :=
  let ux := a.x - b.x; let uy := a.y - b.y
  let vx := c.x - b.x; let vy := c.y - b.y
  let cross := ux * vy - uy * vx
  let dot := ux * vx + uy * vy
  Float.atan2 cross.abs dot

def minMaxAngle (pts : Array Pt) : Float × Float :=
  Id.run do
    let n := pts.size
    let mut mx := 0.0
    let mut mn := 4.0
    for i in [:n] do
      for j in [:n] do
        for l in [:n] do
          if i ≠ j ∧ j ≠ l ∧ i ≠ l then
            let a := angleOf pts[i]! pts[j]! pts[l]!
            if a > mx then mx := a
            if a < mn then mn := a
    return (mn, mx)

/-- Profile of a center set for parameter `u`. -/
def profile (u : Float) (pts : Array Pt) : Array Nat :=
  Id.run do
    let s := pts.size
    let mut ks := #[]
    for i in [:s] do
      let mut ds := #[]
      for j in [:s] do
        if i ≠ j then
          ds := ds.push (dirModPi pts[i]! pts[j]!)
      ds := ds.qsort (· < ·)
      ks := ks.push (kPrime u (gaps ds))
    return ks.qsort (· ≥ ·)

/-- Signed side of `c` relative to directed line `a → b` (cross product). -/
def sideOf (a b c : Pt) : Float :=
  (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x)

/-- Angular distance in `[0, π)` between two directions (mod π). -/
def angDist (d₁ d₂ : Float) : Float :=
  let d := (d₂ - d₁).abs
  if d > piF / 2 then piF - d else d

/-- Gap at `i` adjacent to direction `dᵢⱼ` on a given side of line `ij`:
the angle from `dᵢⱼ` to the nearest direction `dᵢₖ` with `k` on that
side (as a fraction of the cyclic structure: the single adjacent gap,
in units of π).  Returns `none` if no center lies on that side. -/
def facingGap (pts : Array Pt) (i j : Nat) (σ : Float) : Option Float :=
  Id.run do
    let s := pts.size
    let dij := dirModPi pts[i]! pts[j]!
    let mut best : Option Float := none
    for k in [:s] do
      if k ≠ i ∧ k ≠ j then
        let sd := sideOf pts[i]! pts[j]! pts[k]!
        if σ * sd > 0 then
          let dik := dirModPi pts[i]! pts[k]!
          let d := angDist dij dik
          match best with
          | none => best := some d
          | some b => if d < b then best := some d
    return best

/-- Model-B legality: for every edge `(i,j)` and every side that
contains centers, the two facing gaps satisfy `gᵢ + gⱼ ≥ 2/u`
(in π units).  This is the natural s ≥ 4 generalization of (4.12)'s
lower bound; the upper bound is handled by the `maxGA` proxy. -/
def facingLegal (u : Float) (pts : Array Pt) : Bool :=
  Id.run do
    let s := pts.size
    for i in [:s] do
      for j in [:s] do
        if i < j then
          for σ in [1.0, -1.0] do
            match facingGap pts i j σ, facingGap pts j i (-σ) with
            | some gi, some gj =>
              if (gi + gj) / piF < 2.0 / u then
                return false
            | _, _ => pure ()
    return true

/-- One audit run: returns (weighted-excess violations, worst signed
excess over budget, sum 2^{kᵢ}).  The weighted bound is
`Σ_{m=a}^{n-1} 2^{m-1} N(m) ≤ Σ 2^{m-1}(n-m) + bonus`, where
`bonus = 2^{n-2}` (big) or `0` — the minimal sufficient condition for
Sendov's sum bound, compatible with both observed profile shapes. -/
def audit (n s : Nat) (δ : Float) (big : Bool) (pts : Array Pt) :
    Nat × Int × Nat := Id.run do
  let u := 2.0 * n.toFloat + 2.0 * δ
  let ks := profile u pts
  let a := n + 2 - s      -- bottom staircase level
  let mut lhs : Int := 0
  let mut rhs : Int := 0
  if 1 ≤ a then           -- weighted bound only meaningful for a ≥ 1
    for m in [a:n] do     -- m ∈ [a, n-1]
      let nm := tailCount ks m
      lhs := lhs + (2 ^ (m - 1) : Int) * nm
      rhs := rhs + (2 ^ (m - 1) : Int) * (n - m)
  if big then rhs := rhs + (2 ^ (n - 2) : Int)
  let excess := lhs - rhs
  let viol := if excess > 0 then 1 else 0
  let sum := ks.foldl (fun acc k => acc + 2 ^ k) 0
  return (viol, max excess 0, sum)

/-- Describe the profile and per-level excess of a config. -/
def violLevels (n s : Nat) (δ : Float) (big : Bool) (pts : Array Pt) :
    String := Id.run do
  let u := 2.0 * n.toFloat + 2.0 * δ
  let ks := profile u pts
  let a := n + 2 - s
  let mut out := ""
  let mut wexc : Int := 0
  for m in [a:n] do
    let nm := tailCount ks m
    let ex : Int := (nm : Int) - (n - m : Int)
    if ex > 0 then
      out := out ++ s!" m={m}:N={nm}>cap={n - m}"
    wexc := wexc + (2 ^ (m - 1) : Int) * ex
  return s!"ks={ks.toList} sum={ks.foldl (fun acc k => acc + 2 ^ k) 0} wexcess={wexc}|{out}"

/-- Exponent list in *index order* (deletion audit needs alignment). -/
def profileIdx (u : Float) (pts : Array Pt) : Array Nat :=
  Id.run do
    let s := pts.size
    let mut ks := #[]
    for i in [:s] do
      let mut ds := #[]
      for j in [:s] do
        if i ≠ j then
          ds := ds.push (dirModPi pts[i]! pts[j]!)
      ds := ds.qsort (· < ·)
      ks := ks.push (kPrime u (gaps ds))
    return ks

/-- Erase index `v` from a point array. -/
def eraseAt (pts : Array Pt) (v : Nat) : Array Pt := Id.run do
  let mut out := #[]
  for i in [:pts.size] do
    if i ≠ v then out := out.push pts[i]!
  return out

/-- Hull data at `v`: `(maxGap, prevIdx, nextIdx)` where `maxGap` is the
largest gap in the 2π direction order at `v`, and `prev`/`next` are the
point indices bounding that gap (the two hull neighbors of `v` when `v`
is extreme).  `v` is a convex-hull vertex iff `maxGap > π`: all other
points then lie inside an open half-plane through `v`. -/
def hullData (pts : Array Pt) (v : Nat) : Float × Nat × Nat := Id.run do
  let s := pts.size
  let mut angs := #[]
  for j in [:s] do
    if j ≠ v then
      angs := angs.push
        (Float.atan2 (pts[j]!.y - pts[v]!.y) (pts[j]!.x - pts[v]!.x), j)
  angs := angs.qsort (fun a b => a.1 < b.1)
  let mut maxGap := 0.0
  let mut prev := 0
  let mut next := 0
  for i in [:angs.size] do
    let a := angs[i]!
    let (b, bidx) := if i + 1 < angs.size then (angs[i + 1]!.1, angs[i + 1]!.2)
      else (angs[0]!.1 + 2.0 * piF, angs[0]!.2)
    if b - a.1 > maxGap then
      maxGap := b - a.1
      prev := a.2
      next := bidx
  return (maxGap, prev, next)

/-- `v` is a convex-hull vertex iff all other points lie inside some
open half-plane through `v`, i.e. the 2π direction order at `v` has a
gap `> π`. -/
def isHull (pts : Array Pt) (v : Nat) : Bool :=
  (hullData pts v).1 > piF + 1e-9

/-- Projective (mod π) gap data at `v`: `(maxGap, prev, next)` over the
sorted `dirModPi` directions — `prev`/`next` are the two centers whose
directions bound `v`'s largest projective gap (the wedge edges). -/
def projGapData (pts : Array Pt) (v : Nat) : Float × Nat × Nat := Id.run do
  let s := pts.size
  let mut ds := #[]
  for j in [:s] do
    if j ≠ v then
      ds := ds.push (dirModPi pts[v]! pts[j]!, j)
  ds := ds.qsort (fun a b => a.1 < b.1)
  let mut maxGap := 0.0
  let mut prev := 0
  let mut next := 0
  for i in [:ds.size] do
    let a := ds[i]!
    let (b, bidx) := if i + 1 < ds.size then (ds[i + 1]!.1, ds[i + 1]!.2)
      else (ds[0]!.1 + piF, ds[0]!.2)
    if b - a.1 > maxGap then
      maxGap := b - a.1
      prev := a.2
      next := bidx
  return (maxGap, prev, next)

/-- Per-vertex deletion certificate data.  `cert` classes:
`0` = A (a `gain ≥ 1` neighbor with `k_i ≥ k_v`),
`1` = B (a `gain = 2` neighbor with `k_v ≤ k_i + 1`),
`2` = C (two `gain ≥ 1` neighbors each with `k_v ≤ k_i + 1`),
`3` = D (removable only via ≥ 3 charge terms),
`4` = not removable,
`5` = certificate predicted removable but `F(Q-v) < F(Q)` (inconsistency
flag — should never appear; would signal a Float/model mismatch).
`b1`/`b2` = min `k_v - k_i` over `gain = 1`/`gain = 2` neighbors (`999`
if none); `p1`/`p2` = two smallest `k_v - k_i` over `gain > 0`
neighbors. -/
structure VInfo where
  hull : Bool
  maxGap : Float
  ear : Float
  kv : Nat
  fv : Nat
  net : Int
  cert : Nat
  b1 : Int
  b2 : Int
  p1 : Int
  p2 : Int
  closeIn : Nat
  deriving Inhabited

/-- **Deletion audit** for D1/D2 + charge certificates:
`F(Q) = Σᵢ 2^{kᵢ}`; for each `v` recompute `F(Q∖{v})`.
Returns `(F, ΣᵥF(Q-v), Σᵢ 2^{kᵢ}·Σᵥ 2^{gᵢᵥ}, anyGE, anyHullGE,
maxGain, nRem, nHullRem, vinfos)` where the third component is the exact
identity `Σ_v F(Q-v) = Σ_i 2^{k_i} Σ_v 2^{g_iv}` (self-check: the two
sums must agree).  `g_iv = kᵢ(Q-v) - kᵢ(Q)` is the merge gain —
predicted `∈ {0,1,2}` (2 only when both adjacent gaps ≥ λ).
`vinfos[v]` carries the charge data `C_i(v) = 2^{k_i}(2^{g_{iv}}-1)`:
net charge `Σ_i C_i(v) - 2^{k_v}`, the A/B/C/D certificate class, and
exponent margins `k_v - k_i` for the best gain-1/gain-2 candidates. -/
def deletionAudit (u : Float) (pts : Array Pt) :
    Nat × Nat × Nat × Bool × Bool × Nat × Nat × Nat × Array VInfo ×
      (Nat × Nat × Nat) × (Int × Int × Int × Int × Nat × Nat × Nat) := Id.run do
  let s := pts.size
  let ks := profileIdx u pts
  let f := ks.foldl (fun a k => a + 2 ^ k) 0
  -- boundary-emission probe: `bt` = vertex whose row has the global max
  -- projective gap; `ba`/`bb` = the two centers bounding that gap.
  let mut pgMax := 0.0
  let mut bt := 0
  let mut ba := 0
  let mut bb := 0
  for v in [:s] do
    let (g2, pa, pb) := projGapData pts v
    if g2 > pgMax then
      pgMax := g2; bt := v; ba := pa; bb := pb
  let mut bga : Int := -1
  let mut bgb : Int := -1
  let mut bka : Int := -1
  let mut bkb : Int := -1
  let mut tEm : Nat := 0   -- #emitters into bt
  let mut tClose : Nat := 0 -- #close (jump=1) arcs into bt
  let mut tDown : Nat := 0  -- #down/level arcs into bt (jump ≤ 0)
  let mut sumFv := 0
  let mut rhsSum := 0
  let mut anyGE := false
  let mut anyHullGE := false
  let mut maxGain := 0
  let mut nRem := 0
  let mut nHullRem := 0
  let mut gainSum := Array.replicate s 0
  -- emitter-side arc stats: hasEmit/hasClose/hasDown per emitter i,
  -- closeRecv[v] = #close arcs (jump = 1) received by v
  let mut hasEmit := Array.replicate s false
  let mut hasClose := Array.replicate s false
  let mut hasDown := Array.replicate s false
  let mut closeRecv := Array.replicate s 0
  let mut vinfos := #[]
  for v in [:s] do
    let ptsv := eraseAt pts v
    let ksv := profileIdx u ptsv
    let fv := ksv.foldl (fun a k => a + 2 ^ k) 0
    sumFv := sumFv + fv
    let (maxGap, pr, nx) := hullData pts v
    let hull := maxGap > piF + 1e-9
    let ear := angleOf pts[pr]! pts[v]! pts[nx]!
    if fv ≥ f then
      anyGE := true
      nRem := nRem + 1
      if hull then
        anyHullGE := true
        nHullRem := nHullRem + 1
    let kv := ks[v]!
    let mut chg : Int := 0
    let mut hasA := false
    let mut hasB := false
    let mut nC := 0
    let mut b1 : Int := 999
    let mut b2 : Int := 999
    let mut pos : Array Int := #[]
    for i' in [:s - 1] do
      let i := if i' < v then i' else i' + 1
      let g := ksv[i']! - ks[i]!
      if v == bt ∧ i == ba then bga := (g : Int); bka := (ks[i]! : Int)
      if v == bt ∧ i == bb then bgb := (g : Int); bkb := (ks[i]! : Int)
      if v == bt ∧ g ≥ 1 then
        tEm := tEm + 1
        if (kv : Int) - (ks[i]! : Int) == 1 then tClose := tClose + 1
        if (ks[i]! : Int) ≥ kv then tDown := tDown + 1
      if g > maxGain then maxGain := g
      gainSum := gainSum.set! i (gainSum[i]! + 2 ^ g)
      let ki := ks[i]!
      if g ≥ 1 then
        hasEmit := hasEmit.set! i true
        let jump : Int := (kv : Int) - (ki : Int)
        if jump == 1 then
          hasClose := hasClose.set! i true
          closeRecv := closeRecv.set! v (closeRecv[v]! + 1)
        if jump ≤ 0 then hasDown := hasDown.set! i true
      chg := chg + (2 ^ ki : Int) * ((2 ^ g : Int) - 1)
      if g ≥ 1 then
        let r : Int := (kv : Int) - (ki : Int)
        pos := pos.push r
        if ki ≥ kv then hasA := true
        if kv ≤ ki + 1 then nC := nC + 1
        if g == 1 ∧ r < b1 then b1 := r
        if g == 2 then
          if r < b2 then b2 := r
          if kv ≤ ki + 1 then hasB := true
    pos := pos.qsort (· < ·)
    let p1 := if pos.size > 0 then pos[0]! else 999
    let p2 := if pos.size > 1 then pos[1]! else 999
    let net := chg - (2 ^ kv : Int)
    let rem := fv ≥ f
    let cert := if hasA then (if rem then 0 else 5)
      else if hasB then (if rem then 1 else 5)
      else if nC ≥ 2 then (if rem then 2 else 5)
      else if rem then 3 else 4
    vinfos := vinfos.push ⟨hull, maxGap, ear, kv, fv, net, cert, b1, b2, p1, p2, 0⟩
  for v in [:s] do
    vinfos := vinfos.set! v { vinfos[v]! with closeIn := closeRecv[v]! }
  for i in [:s] do
    rhsSum := rhsSum + (2 ^ ks[i]!) * gainSum[i]!
  let mut nFarOnly := 0
  let mut nDownEmit := 0
  let mut maxCloseRecv := 0
  for i in [:s] do
    if hasEmit[i]! ∧ ¬hasClose[i]! ∧ ¬hasDown[i]! then nFarOnly := nFarOnly + 1
    if hasDown[i]! then nDownEmit := nDownEmit + 1
    if closeRecv[i]! > maxCloseRecv then maxCloseRecv := closeRecv[i]!
  return (f, sumFv, rhsSum, anyGE, anyHullGE, maxGain, nRem, nHullRem, vinfos,
    (nFarOnly, maxCloseRecv, nDownEmit),
    (bga, bgb, (ks[bt]! : Int) - bka, (ks[bt]! : Int) - bkb,
     tEm, tClose, tDown))

/-- Deterministic hull-vertex selectors.  `sel`:
`0` = hull vertex with minimum `k_v` (ties: lowest index),
`1` = largest external empty sector (max 2π gap at `v`),
`2` = minimum `k_v`, ties broken by largest hull gap,
`3` = hull vertex maximizing net charge `Σᵢ Cᵢ(v) - 2^{k_v}`,
`4` = smallest ear angle `∠(prev) v (next)` at the hull neighbors
      (should coincide with `sel 1` — implementation cross-check). -/
def pickHull (vinfos : Array VInfo) (sel : Nat) : Option Nat := Id.run do
  let mut best : Option Nat := none
  for idx in [:vinfos.size] do
    let vi := vinfos[idx]!
    if vi.hull then
      match best with
      | none => best := some idx
      | some b =>
        let vb := vinfos[b]!
        let better :=
          if sel == 0 then vi.kv < vb.kv
          else if sel == 1 then vi.maxGap > vb.maxGap
          else if sel == 2 then
            vi.kv < vb.kv ∨ (vi.kv == vb.kv ∧ vi.maxGap > vb.maxGap)
          else if sel == 3 then vi.net > vb.net
          else vi.ear < vb.ear
        if better then best := some idx
  return best

/-- Selector/certificate statistics per bucket. -/
structure CertStats where
  selFail : Array Nat      -- nonflat: chosen hull v not removable, per sel
  selFailFlat : Array Nat  -- flat: chosen hull v not removable, per sel
  selBug : Nat             -- cert predicted removable but F(Q-v) < F(Q)
  bestCert : Array Nat     -- histogram over configs: best hull cert
                           -- [A,B,C,D,noHullRem]
  wB1 : Int                -- worst-case (max over configs) best gain-1
                           -- margin `min k_v - k_i` among hull-removable v
  wB2 : Int                -- same for gain-2 candidates
  wP2 : Int                -- worst-case 2nd-smallest positive-gain margin
  qFail : Array Nat        -- [36] fails per candidate-set × property:
                           -- sets 0=Q4(rK<2∨rG<2) 1=Q3a(rK<2∨rG<1)
                           --      2=Q3b(rK<1∨rG<2) 3=Q4strict
                           --      4=minK1(rK<1) 5=maxG1(rG<1)
                           --      6=top2K(rK<2) 7=top2G(rG<2)
                           --      8=U(rK<1∨rG<1)
                           -- props 0=rem 1=A∨B∨C 2=A∨C 3=A
  needBC : Nat             -- Q4 has an A∨B∨C candidate but no A candidate
  nearMiss : Nat           -- max net over Q4 candidates ∈ {0,1}
  anyA : Nat               -- nonflat fails: NO vertex (any, incl
                           -- interior) has cert A
  anyABC : Nat             -- same for A∨B∨C
  anyDonly : Nat           -- nonflat configs where removable exists but
                           -- EVERY removable vertex is class D
  gmK : Nat                -- nonflat fails: NO removable vertex attains
                           -- the GLOBAL minimum exponent
  gmKA : Nat               -- same for cert-A vertices at global min k
  gmKpos : Nat             -- nonflat fails: NO global-min-k vertex has
                           -- any positive-gain neighbor
  gmKpAll : Nat            -- nonflat fails: SOME global-min-k vertex has
                           -- NO positive-gain neighbor ("every" version)
  anyAC : Nat              -- nonflat fails: NO vertex has cert A or C
  emFar : Nat              -- nonflat: some non-silent vertex emits ONLY far
                           -- arcs (jump ≥ 2) — breaks the close-arc chain
  emDown : Nat             -- nonflat: some vertex emits a down/level arc
                           -- (jump ≤ 0 — that is cert A at the receiver)
  emC2 : Nat               -- nonflat: some vertex receives ≥2 close arcs
  emNoAC : Nat             -- nonflat: NO down arc AND no vertex receives 2
                           -- close arcs — the case where A∨C must come from
                           -- a different mechanism
  emC2top : Nat            -- nonflat: some MAX-level vertex receives ≥2
                           -- close arcs (the star-sink mechanism)
  beNone : Nat             -- nonflat: NEITHER boundary center of the
                           -- global max projective gap emits to `t`
  beA : Nat                -- a boundary arc `a→t` has gain ≥ 1 with
                           -- jump ≤ 0 (cert A at `t`)
  beC : Nat                -- both boundary arcs emit with jump = 1
                           -- (cert C at `t`)
  beX : Nat                -- boundary emits but neither A- nor
                           -- C-pattern (single or far jump)
  beNnoA : Nat             -- nonflat: NEITHER boundary emits AND no
                           -- down-arc anywhere (no cert-A witness) —
                           -- breaks the 3-disjunct boundary lemma
  tRecv0 : Nat             -- nonflat: bt receives NO positive-gain arc
  tRecvC : Nat             -- nonflat: bt receives ≥2 close arcs (C at bt)
  tRecvD : Nat             -- nonflat: bt receives a down/level arc (A at bt)
  nCfg : Nat
  nNF : Nat

def emptyCertStats : CertStats :=
  ⟨Array.replicate 5 0, Array.replicate 5 0, 0, Array.replicate 5 0,
   (-999 : Int), (-999 : Int), (-999 : Int), Array.replicate 36 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0⟩

/-- Fold one configuration's `vinfos` into the selector statistics.
Returns `(stats, dumpFlag)` where `dumpFlag` is `1` when the rank-Q4
candidate set contains no A/B/C certificate, `2` when some hull vertex
is certificate class D, `3` on a near-miss (max net over Q4 ∈ {0,1}),
else `0`. -/
def updCert (vinfos : Array VInfo) (f s : Nat) (em : Nat × Nat × Nat)
    (be : Int × Int × Int × Int × Nat × Nat × Nat) (cs : CertStats) : CertStats × Nat := Id.run do
  let flat := f == s
  let mut cs : CertStats :=
    { cs with nCfg := cs.nCfg + 1, nNF := cs.nNF + (if flat then 0 else 1) }
  if ¬flat then
    let (nFarOnly, maxCloseRecv, nDownEmit) := em
    let (bga, bgb, bja, bjb, tEm, tClose, tDown) := be
    let aEmit := bga ≥ 1
    let bEmit := bgb ≥ 1
    cs := { cs with
      tRecv0 := cs.tRecv0 + (if tEm == 0 then 1 else 0),
      tRecvC := cs.tRecvC + (if tClose ≥ 2 then 1 else 0),
      tRecvD := cs.tRecvD + (if tDown ≥ 1 then 1 else 0),
      beNone := cs.beNone + (if ¬aEmit ∧ ¬bEmit then 1 else 0),
      beA := cs.beA + (if (aEmit ∧ bja ≤ 0) ∨ (bEmit ∧ bjb ≤ 0)
        then 1 else 0),
      beC := cs.beC + (if aEmit ∧ bEmit ∧ bja == 1 ∧ bjb == 1
        then 1 else 0),
      beX := cs.beX + (if (aEmit ∨ bEmit) ∧
          ¬((aEmit ∧ bja ≤ 0) ∨ (bEmit ∧ bjb ≤ 0)) ∧
          ¬(aEmit ∧ bEmit ∧ bja == 1 ∧ bjb == 1) then 1 else 0) }
    let mut kmax := 0
    for vi in vinfos do
      if vi.kv > kmax then kmax := vi.kv
    let mut topC2 := false
    for vi in vinfos do
      if vi.kv == kmax ∧ vi.closeIn ≥ 2 then topC2 := true
    cs := { cs with
      emFar := cs.emFar + (if nFarOnly > 0 then 1 else 0),
      emDown := cs.emDown + (if nDownEmit > 0 then 1 else 0),
      emC2 := cs.emC2 + (if maxCloseRecv ≥ 2 then 1 else 0),
      emC2top := cs.emC2top + (if topC2 then 1 else 0),
      emNoAC := cs.emNoAC +
        (if nDownEmit == 0 ∧ maxCloseRecv < 2 then 1 else 0) }
  for sel in [:5] do
    match pickHull vinfos sel with
    | none => pure ()
    | some v =>
      let vi := vinfos[v]!
      if vi.cert == 5 then
        cs := { cs with selBug := cs.selBug + 1 }
      else if vi.cert ≥ 4 then
        cs := if flat
          then { cs with selFailFlat :=
                 cs.selFailFlat.set! sel (cs.selFailFlat[sel]! + 1) }
          else { cs with selFail :=
                 cs.selFail.set! sel (cs.selFail[sel]! + 1) }
  -- best hull certificate + exponent margins over hull-removable v
  let mut bc := 9
  let mut mb1 : Int := 999
  let mut mb2 : Int := 999
  let mut mp2 : Int := 999
  for vi in vinfos do
    if vi.hull ∧ vi.cert ≤ 3 then
      if vi.cert < bc then bc := vi.cert
      if vi.b1 < mb1 then mb1 := vi.b1
      if vi.b2 < mb2 then mb2 := vi.b2
      if vi.p2 < mp2 then mp2 := vi.p2
  let bci := if bc ≥ 4 then 4 else bc
  cs := { cs with bestCert := cs.bestCert.set! bci (cs.bestCert[bci]! + 1) }
  if ¬flat ∧ bc ≤ 3 then
    cs := { cs with wB1 := max cs.wB1 mb1, wB2 := max cs.wB2 mb2, wP2 := max cs.wP2 mp2 }
  -- rank-based candidate-set predicates (tie-independent):
  -- rK(v) = #{hull w : k_w < k_v}, rG(v) = #{hull w : g_w > g_v}
  let mut flag := 0
  if ¬flat then
    let mut hullIdx : Array Nat := #[]
    for idx in [:vinfos.size] do
      if vinfos[idx]!.hull then hullIdx := hullIdx.push idx
    let byK := hullIdx.qsort (fun a b =>
      vinfos[a]!.kv < vinfos[b]!.kv ∨ (vinfos[a]!.kv == vinfos[b]!.kv ∧ a < b))
    let byG := hullIdx.qsort (fun a b =>
      vinfos[a]!.maxGap > vinfos[b]!.maxGap ∨
      (vinfos[a]!.maxGap == vinfos[b]!.maxGap ∧ a < b))
    let inSet (idx : Nat) (st : Nat) : Bool := Id.run do
      let vi := vinfos[idx]!
      let mut rK := 0
      let mut rG := 0
      for widx in hullIdx do
        let w := vinfos[widx]!
        if w.kv < vi.kv then rK := rK + 1
        if w.maxGap > vi.maxGap then rG := rG + 1
      if st == 0 then return rK < 2 ∨ rG < 2
      if st == 1 then return rK < 2 ∨ rG < 1
      if st == 2 then return rK < 1 ∨ rG < 2
      if st == 3 then
        let mut mem := false
        for j in [:min 2 byK.size] do if byK[j]! == idx then mem := true
        for j in [:min 2 byG.size] do if byG[j]! == idx then mem := true
        return mem
      if st == 4 then return rK < 1
      if st == 5 then return rG < 1
      if st == 6 then return rK < 2
      if st == 7 then return rG < 2
      return rK < 1 ∨ rG < 1
    let propOk (cert : Nat) (p : Nat) : Bool :=
      if p == 0 then cert ≤ 3
      else if p == 1 then cert ≤ 2
      else if p == 2 then cert == 0 ∨ cert == 2
      else cert == 0
    let mut okArr := Array.replicate 36 false
    for st in [:9] do
      for p in [:4] do
        let mut ok := false
        for idx in hullIdx do
          if inSet idx st ∧ propOk vinfos[idx]!.cert p then ok := true
        okArr := okArr.set! (st * 4 + p) ok
        if ¬ok then
          cs := { cs with qFail := cs.qFail.set! (st * 4 + p) (cs.qFail[st * 4 + p]! + 1) }
    if okArr[1]! ∧ ¬okArr[3]! then
      cs := { cs with needBC := cs.needBC + 1 }
    let mut bestNet : Int := -999999
    for idx in hullIdx do
      if inSet idx 0 ∧ vinfos[idx]!.cert ≤ 3 then
        if vinfos[idx]!.net > bestNet then bestNet := vinfos[idx]!.net
    if bestNet ≥ 0 ∧ bestNet ≤ 1 then
      cs := { cs with nearMiss := cs.nearMiss + 1 }
    if ¬okArr[1]! then flag := 1
    if flag == 0 then
      for idx in hullIdx do
        if inSet idx 0 ∧ vinfos[idx]!.cert == 3 then flag := 2
    if flag == 0 then
      for idx in hullIdx do
        if vinfos[idx]!.cert == 3 then flag := 2
    if flag == 0 ∧ bestNet ≥ 0 ∧ bestNet ≤ 1 then flag := 3
    -- global (any-vertex, incl interior) certificate availability
    let mut gmin : Nat := 999
    for vi in vinfos do
      if vi.kv < gmin then gmin := vi.kv
    let mut oA := false
    let mut oABC := false
    let mut anyRem := false
    let mut allRemD := true
    let mut oGmK := false
    let mut oGmKA := false
    let mut oGmKpos := false
    let mut oGmKpAll := true
    let mut oAC := false
    for vi in vinfos do
      if vi.cert == 0 then oA := true
      if vi.cert == 0 ∨ vi.cert == 2 then oAC := true
      if vi.cert ≤ 2 then oABC := true
      if vi.cert ≤ 3 then
        anyRem := true
        if vi.cert ≠ 3 then allRemD := false
      if vi.kv == gmin then
        if vi.cert ≤ 3 then oGmK := true
        if vi.cert == 0 then oGmKA := true
        if vi.p1 < 999 then oGmKpos := true
        if vi.p1 ≥ 999 then oGmKpAll := false
    let nnoA : Nat :=
      let (bga, bgb, _, _, _, _, _) := be
      if ¬(bga ≥ 1) ∧ ¬(bgb ≥ 1) ∧ ¬oA then 1 else 0
    cs := { cs with anyA := cs.anyA + (if oA then 0 else 1), anyABC := cs.anyABC + (if oABC then 0 else 1), anyDonly := cs.anyDonly + (if anyRem ∧ allRemD then 1 else 0), gmK := cs.gmK + (if oGmK then 0 else 1), gmKA := cs.gmKA + (if oGmKA then 0 else 1), gmKpos := cs.gmKpos + (if oGmKpos then 0 else 1), gmKpAll := cs.gmKpAll + (if oGmKpAll then 0 else 1), anyAC := cs.anyAC + (if oAC then 0 else 1) }
    cs := { cs with beNnoA := cs.beNnoA + nnoA }
    -- flag 4: no cert-A vertex anywhere (all positive-gain arcs go
    -- strictly upward) — the configs where B/C must fire
    if flag == 0 ∧ ¬oA then flag := 4
    -- flag 5: a D-class vertex exists anywhere (cert forced past C)
    if flag == 0 then
      for vi in vinfos do
        if vi.cert == 3 then flag := 5
    -- flag 6: a boundary arc of the global max gap emits but lands as
    -- neither A- nor C-pattern (single emission or far jump);
    -- flag 7: NEITHER boundary center emits (would break the route)
    if flag == 0 then
      let (bga, bgb, bja, bjb, _, _, _) := be
      let aEmit := bga ≥ 1
      let bEmit := bgb ≥ 1
      if (aEmit ∨ bEmit) ∧
          ¬((aEmit ∧ bja ≤ 0) ∨ (bEmit ∧ bjb ≤ 0)) ∧
          ¬(aEmit ∧ bEmit ∧ bja == 1 ∧ bjb == 1) then flag := 6
      if ¬aEmit ∧ ¬bEmit then flag := 7
  return (cs, flag)

def showCert (cs : CertStats) : String :=
  let q (st p : Nat) := cs.qFail[st * 4 + p]!
  s!"sel=[{cs.selFail[0]!},{cs.selFail[1]!},{cs.selFail[2]!}," ++
  s!"{cs.selFail[3]!},{cs.selFail[4]!}] " ++
  s!"flat=[{cs.selFailFlat[0]!},{cs.selFailFlat[1]!},{cs.selFailFlat[2]!}," ++
  s!"{cs.selFailFlat[3]!},{cs.selFailFlat[4]!}] " ++
  s!"bug={cs.selBug} " ++
  s!"best=[A:{cs.bestCert[0]!} B:{cs.bestCert[1]!} C:{cs.bestCert[2]!} " ++
  s!"D:{cs.bestCert[3]!} no:{cs.bestCert[4]!}] " ++
  s!"marg=[{cs.wB1},{cs.wB2},{cs.wP2}] " ++
  s!"Q4=[r:{q 0 0} abc:{q 0 1} ac:{q 0 2} a:{q 0 3}] " ++
  s!"Q3a=[r:{q 1 0} abc:{q 1 1} ac:{q 1 2} a:{q 1 3}] " ++
  s!"Q3b=[r:{q 2 0} abc:{q 2 1} ac:{q 2 2} a:{q 2 3}] " ++
  s!"Q4s=[r:{q 3 0} abc:{q 3 1} ac:{q 3 2} a:{q 3 3}] " ++
  s!"mK1={q 4 0} mG1={q 5 0} t2k={q 6 0} t2g={q 7 0} U={q 8 0} " ++
  s!"nBC={cs.needBC} nm={cs.nearMiss} " ++
  s!"anyA={cs.anyA} anyABC={cs.anyABC} Don={cs.anyDonly} " ++
  s!"gmK={cs.gmK} gmKA={cs.gmKA} gmKp={cs.gmKpos} gmKpA={cs.gmKpAll} " ++
  s!"anyAC={cs.anyAC} em=[F:{cs.emFar} D:{cs.emDown} C2:{cs.emC2} " ++
  s!"C2t:{cs.emC2top} noAC:{cs.emNoAC}] " ++
  s!"be=[N:{cs.beNone} A:{cs.beA} C:{cs.beC} X:{cs.beX} NnoA:{cs.beNnoA}] " ++
  s!"tR=[0:{cs.tRecv0} C:{cs.tRecvC} D:{cs.tRecvD}] " ++
  s!"nf={cs.nNF}/{cs.nCfg}"

/-- Full dump of one configuration: coordinates, hull cyclic order,
per-vertex deletion data (with rank rK/rG), and the (i,v) gain matrix.
`flag`: 1 = no A/B/C certificate inside rank-Q4, 2 = a D-class vertex,
3 = near-miss (max net over Q4 ∈ {0,1}). -/
def dumpConfig (u : Float) (pts : Array Pt) (vinfos : Array VInfo)
    (flag : Nat) : String := Id.run do
  let s := pts.size
  let ks := profileIdx u pts
  let mut out := s!"  [DUMP flag={flag}] s={s}\n"
  for i in [:s] do
    out := out ++ s!"    p{i}=({pts[i]!.x},{pts[i]!.y})\n"
  let mut cx := 0.0
  let mut cy := 0.0
  for i in [:s] do
    cx := cx + pts[i]!.x
    cy := cy + pts[i]!.y
  cx := cx / s.toFloat
  cy := cy / s.toFloat
  let mut hp := #[]
  for i in [:s] do
    if vinfos[i]!.hull then
      hp := hp.push (Float.atan2 (pts[i]!.y - cy) (pts[i]!.x - cx), i)
  hp := hp.qsort (fun a b => a.1 < b.1)
  let mut hs := ""
  for p in hp do hs := hs ++ s!"{p.2} "
  out := out ++ s!"    hullOrder=[{hs}]\n"
  for i in [:s] do
    let vi := vinfos[i]!
    let mut rK := 0
    let mut rG := 0
    for w in vinfos do
      if w.hull then
        if w.kv < vi.kv then rK := rK + 1
        if w.maxGap > vi.maxGap then rG := rG + 1
    out := out ++ s!"    v{i}: hull={vi.hull} k={vi.kv} gap={vi.maxGap}" ++
      s!" ear={vi.ear} fv={vi.fv} net={vi.net} cert={vi.cert}" ++
      s!" b1={vi.b1} b2={vi.b2} p1={vi.p1} p2={vi.p2} cIn={vi.closeIn} rK={rK} rG={rG}\n"
  -- projective-gap boundary: mark the global argmax vertex and its two
  -- gap-boundary centers
  let mut pgMax := 0.0
  let mut bt := 0
  let mut ba := 0
  let mut bb := 0
  for v in [:s] do
    let (g2, pa, pb) := projGapData pts v
    if g2 > pgMax then
      pgMax := g2; bt := v; ba := pa; bb := pb
  out := out ++ s!"    maxProjGap: t={bt} G={pgMax} a={ba} b={bb}\n"
  for v in [:s] do
    let ptsv := eraseAt pts v
    let ksv := profileIdx u ptsv
    let mut row := ""
    for i' in [:s - 1] do
      let i := if i' < v then i' else i' + 1
      row := row ++ s!"{ksv[i']! - ks[i]!} "
    out := out ++ s!"    gains(v={v}): [{row}]\n"
  return out

/-- Draw `s` random points from the LCG stream. -/
def drawPts (s : Nat) (seed : UInt64) : Array Pt × UInt64 :=
  Id.run do
    let mut pts := #[]
    let mut st := seed
    for _ in [:s] do
      let (x, st₁) := rand01 st
      let (y, st₂) := rand01 st₁
      pts := pts.push ⟨x, y⟩
      st := st₂
    return (pts, st)

/-- Regular s-gon with per-vertex radial perturbation (stays inside the
angle window when `s ≤ u/2`). -/
def drawGon (s : Nat) (seed : UInt64) : Array Pt × UInt64 :=
  Id.run do
    let mut pts := #[]
    let mut st := seed
    for i in [:s] do
      let (r, st₁) := rand01 st
      let θ := 2.0 * piF * i.toFloat / s.toFloat
      let ρ := 0.9 + 0.1 * r
      pts := pts.push ⟨ρ * Float.cos θ, ρ * Float.sin θ⟩
      st := st₁
    return (pts, st)

/-- Also generate "staircase-friendly" configurations: a sharp chain of
points clustered directionally (to hit the deep-tail regime). -/
def drawCluster (s : Nat) (seed : UInt64) : Array Pt × UInt64 :=
  Id.run do
    let mut pts := #[]
    let mut st := seed
    for i in [:s] do
      let (r, st₁) := rand01 st
      -- points nearly collinear, spread along a shallow arc
      pts := pts.push ⟨i.toFloat * 0.9, r * 0.05⟩
      st := st₁
    return (pts, st)

def main (_args : List String) : IO Unit := do
  let trials := 1500
  for n in [5] do
    for (δ, big) in [(0.2, false), (0.7, true)] do
      for s in [3:2*n+3] do
        if s ≤ 2 * n + 2 then
          let u := 2.0 * n.toFloat + 2.0 * δ
          let lim := piF * (1 - 2.0 / u)
          let low := piF * 2.0 / u
          -- pass 1: uniform sampling (all configs)
          let mut violAll := 0
          let mut worstAll : Int := 0
          let mut maxSum := 0
          -- pass 2: angle-window filter [2π/u, π - 2π/u] per (4.12)
          let mut violFilt := 0
          let mut worstFilt : Int := 0
          let mut maxSumF := 0
          let mut checked := 0
          let mut overF := 0
          -- pass 3: model-B (facing gaps) + upper proxy
          let mut violB := 0
          let mut worstB : Int := 0
          let mut maxSumB := 0
          let mut checkedB := 0
          let mut dumpedB := 0
          let mut overB := 0
          -- pass 4: model-A (triangle upper bound only — the provable
          -- GA consequence `A(Q) ≤ π - λ`, nothing else)
          let mut violA := 0
          let mut worstA : Int := 0
          let mut checkedA := 0
          let mut dumpedA := 0
          let mut overA := 0
          -- deletion audit accumulators: (d1fail, d1hullfail, d2fail,
          -- minSlack, maxGain, idMismatch) per bucket
          let mut acDel := (0, 0, 0, (0 : Int), 0, 0)
          let mut aDel := (0, 0, 0, (0 : Int), 0, 0)
          let mut acCert := emptyCertStats
          let mut aCert := emptyCertStats
          let mut clCert := emptyCertStats
          let mut gaCert := emptyCertStats
          let mut cdAC := 0
          let mut cdAM := 0
          let mut cdCl := 0
          let mut cdGa := 0
          let mut dumpedD2 := 0
          let mut acD1nf := 0   -- D1-fail AND non-flat (F > s)
          let mut aD1nf := 0
          let mut dumpedD1 := 0
          let cap := 2 ^ n + (if big then 2 ^ (n - 2) else 0)
          let mut st : UInt64 := 0x9E3779B97F4A7C15 +
            (n * 1000 + s * 10 + (if big then 1 else 0)).toUInt64
          for t in [:trials] do
            let (pts, st₁) := drawPts s st
            st := st₁
            let (v, w, sm) := audit n s δ big pts
            violAll := violAll + v
            if w > worstAll then worstAll := w
            if sm > maxSum then maxSum := sm
            let (f, sumFv, rhsSum, anyGE, anyHullGE, maxGain, _nR, _nHR,
              vinfos, em, be) := deletionAudit u pts
            let (acC, acF) := updCert vinfos f s em be acCert
            acCert := acC
            if acF > 0 ∧ cdAC < 5 then
              cdAC := cdAC + 1
              IO.println (dumpConfig u pts vinfos acF)
            let slack : Int := (sumFv : Int) - (s * f : Int)
            let d1f := if anyGE then 0 else 1
            let d1hf := if anyHullGE then 0 else 1
            let d2f := if sumFv < s * f then 1 else 0
            let idb := if rhsSum == sumFv then 0 else 1
            let (a1, a2, a3, a4, a5, a6) := acDel
            acDel := (a1 + d1f, a2 + d1hf, a3 + d2f, (if slack < a4 then slack else a4),
              max a5 maxGain, a6 + idb)
            if d2f > 0 && dumpedD2 < 4 then
              dumpedD2 := dumpedD2 + 1
              IO.println s!"  [allcfg D2fail] {violLevels n s δ big pts} slack={slack}"
            if ¬anyGE ∧ f > s then
              acD1nf := acD1nf + 1
              if dumpedD1 < 4 then
                dumpedD1 := dumpedD1 + 1
                IO.println s!"  [allcfg D1nf] {violLevels n s δ big pts}"
            let (mn, mx) := minMaxAngle pts
            if mn ≥ low ∧ mx ≤ lim then
              checked := checked + 1
              if v > 0 then violFilt := violFilt + v
              if w > worstFilt then worstFilt := w
              if sm > maxSumF then maxSumF := sm
              if sm > cap then overF := overF + 1
            -- model B: facing-gap lower bound + GA upper proxy
            if facingLegal u pts ∧ mx ≤ lim then
              checkedB := checkedB + 1
              if v > 0 then
                violB := violB + v
                if dumpedB < 5 then
                  dumpedB := dumpedB + 1
                  IO.println s!"  [modB viol] {violLevels n s δ big pts}"
              if w > worstB then worstB := w
              if sm > maxSumB then maxSumB := sm
              if sm > cap then overB := overB + 1
            -- model A: triangle upper bound only (provable from GA)
            if mx ≤ lim then
              checkedA := checkedA + 1
              if v > 0 then
                violA := violA + v
                if dumpedA < 5 then
                  dumpedA := dumpedA + 1
                  IO.println s!"  [modA viol] {violLevels n s δ big pts}"
              if w > worstA then worstA := w
              if sm > cap then overA := overA + 1
              let (aC, aF) := updCert vinfos f s em be aCert
              aCert := aC
              if aF > 0 ∧ cdAM < 5 then
                cdAM := cdAM + 1
                IO.println (dumpConfig u pts vinfos aF)
              let (a1, a2, a3, a4, a5, a6) := aDel
              aDel := (a1 + d1f, a2 + d1hf, a3 + d2f, (if slack < a4 then slack else a4),
                max a5 maxGain, a6 + idb)
              if ¬anyGE ∧ f > s then aD1nf := aD1nf + 1
          -- cluster pass (targets sharp profiles)
          let mut violCl := 0
          let mut worstCl : Int := 0
          let mut maxSumCl := 0
          let mut clDel := (0, 0, 0, (0 : Int), 0, 0)
          for _t in [:trials] do
            let (pts, st₁) := drawCluster s st
            st := st₁
            let (v, w, sm) := audit n s δ big pts
            violCl := violCl + v
            if w > worstCl then worstCl := w
            if sm > maxSumCl then maxSumCl := sm
            let (f, sumFv, _, anyGE, _, maxGain, _, _, vinfos, em, be) :=
              deletionAudit u pts
            let (clC, clF) := updCert vinfos f s em be clCert
            clCert := clC
            if clF > 0 ∧ cdCl < 5 then
              cdCl := cdCl + 1
              IO.println (dumpConfig u pts vinfos clF)
            let slack : Int := (sumFv : Int) - (s * f : Int)
            let (a1, _, a3, a4, a5, a6) := clDel
            clDel := (a1 + (if anyGE then 0 else 1), 0,
              a3 + (if sumFv < s * f then 1 else 0), (if slack < a4 then slack else a4),
              max a5 maxGain, a6)
          -- gon pass (structured legal configs for s ≥ 4)
          let mut okGon := 0
          let mut violGon := 0
          let mut worstGon : Int := 0
          let mut maxSumGon := 0
          let mut okGonA := 0
          let mut overGonA := 0
          let mut maxSumGonA := 0
          let mut gaDel := (0, 0, 0, (0 : Int), 0, 0)
          let mut gaD1nf := 0
          for _t in [:trials] do
            let (pts, st₁) := drawGon s st
            st := st₁
            let (mn, mx) := minMaxAngle pts
            if mn ≥ low ∧ mx ≤ lim then
              okGon := okGon + 1
              let (v, w, sm) := audit n s δ big pts
              if v > 0 then violGon := violGon + v
              if w > worstGon then worstGon := w
              if sm > maxSumGon then maxSumGon := sm
            if mx ≤ lim then
              okGonA := okGonA + 1
              let (_, _, sm) := audit n s δ big pts
              if sm > cap then overGonA := overGonA + 1
              if sm > maxSumGonA then maxSumGonA := sm
              let (f, sumFv, rhsSum, anyGE, anyHullGE, maxGain, _, _,
                vinfos, em, be) := deletionAudit u pts
              let (gaC, gaF) := updCert vinfos f s em be gaCert
              gaCert := gaC
              if gaF > 0 ∧ cdGa < 5 then
                cdGa := cdGa + 1
                IO.println (dumpConfig u pts vinfos gaF)
              let slack : Int := (sumFv : Int) - (s * f : Int)
              let (a1, a2, a3, a4, a5, a6) := gaDel
              gaDel := (a1 + (if anyGE then 0 else 1),
                a2 + (if anyHullGE then 0 else 1),
                a3 + (if sumFv < s * f then 1 else 0), (if slack < a4 then slack else a4),
                max a5 maxGain, a6 + (if rhsSum == sumFv then 0 else 1))
              if ¬anyGE ∧ f > s then gaD1nf := gaD1nf + 1
          IO.println s!"n={n} δ={δ} s={s} | allcfg viol={violAll} worst={worstAll} maxΣ={maxSum} | win ok={checked} viol={violFilt} over={overF} maxΣ={maxSumF} | modB ok={checkedB} viol={violB} over={overB} maxΣ={maxSumB} | modA ok={checkedA} viol={violA} over={overA} worst={worstA} | gon ok={okGon} viol={violGon} worst={worstGon} maxΣ={maxSumGon} | gonA ok={okGonA} over={overGonA} maxΣ={maxSumGonA} | cl viol={violCl} worst={worstCl} | cap {cap}"
          let (c1, c2, c3, c4, c5, c6) := acDel
          let (d1, d2, d3, d4, d5, d6) := aDel
          let (e1, e2, e3, e4, e5, e6) := gaDel
          let (g1, _, g3, g4, g5, _) := clDel
          IO.println s!"   del | allcfg D1f={c1} D1hf={c2} D2f={c3} sl={c4} g={c5} id={c6} nf={acD1nf} | modA D1f={d1} D1hf={d2} D2f={d3} sl={d4} g={d5} id={d6} nf={aD1nf} | gonA D1f={e1} D1hf={e2} D2f={e3} sl={e4} g={e5} id={e6} nf={gaD1nf} | cl D1f={g1} D2f={g3} sl={g4} g={g5}"
          IO.println s!"   cert modA | {showCert aCert}"
          IO.println s!"   cert gonA | {showCert gaCert}"
          IO.println s!"   cert allc | {showCert acCert}"
          IO.println s!"   cert clus | {showCert clCert}"
