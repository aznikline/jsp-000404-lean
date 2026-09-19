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

/-- One audit run: returns (violations, worst excess, sum 2^{kᵢ}). -/
def audit (n s : Nat) (δ : Float) (big : Bool) (pts : Array Pt) :
    Nat × Int × Nat := Id.run do
  let u := 2.0 * n.toFloat + 2.0 * δ
  let ks := profile u pts
  let mut viol := 0
  let mut worst : Int := 0
  let a := n + 2 - s      -- bottom staircase level
  for m in [a:n] do       -- m ∈ [a, n-1]
    let nm := tailCount ks m
    let cap := if big ∧ m = n - 1 then 2 else n - m
    if nm > cap then
      viol := viol + 1
      let ex : Int := (nm : Int) - (cap : Int)
      if ex > worst then worst := ex
  let sum := ks.foldl (fun acc k => acc + 2 ^ k) 0
  return (viol, worst, sum)

/-- Describe which tail levels fail for a config. -/
def violLevels (n s : Nat) (δ : Float) (big : Bool) (pts : Array Pt) :
    String := Id.run do
  let u := 2.0 * n.toFloat + 2.0 * δ
  let ks := profile u pts
  let a := n + 2 - s
  let mut out := ""
  for m in [a:n] do
    let nm := tailCount ks m
    let cap := if big ∧ m = n - 1 then 2 else n - m
    if nm > cap then
      out := out ++ s!" m={m}:N={nm}>cap={cap}"
  return s!"ks={ks.toList} sum={ks.foldl (fun acc k => acc + 2 ^ k) 0} |{out}"

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
  let trials := 4000
  for n in [3, 4, 5] do
    for (δ, big) in [(0.2, false), (0.7, true)] do
      for s in [3:n+2] do
        if s ≤ n + 1 then
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
          -- pass 3: model-B (facing gaps) + upper proxy
          let mut violB := 0
          let mut worstB : Int := 0
          let mut maxSumB := 0
          let mut checkedB := 0
          let mut dumpedB := 0
          let mut st : UInt64 := 0x9E3779B97F4A7C15 +
            (n * 1000 + s * 10 + (if big then 1 else 0)).toUInt64
          for t in [:trials] do
            let (pts, st₁) := drawPts s st
            st := st₁
            let (v, w, sm) := audit n s δ big pts
            violAll := violAll + v
            if w > worstAll then worstAll := w
            if sm > maxSum then maxSum := sm
            let (mn, mx) := minMaxAngle pts
            if mn ≥ low ∧ mx ≤ lim then
              checked := checked + 1
              if v > 0 then violFilt := violFilt + v
              if w > worstFilt then worstFilt := w
              if sm > maxSumF then maxSumF := sm
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
          -- cluster pass (targets sharp profiles)
          let mut violCl := 0
          let mut worstCl : Int := 0
          let mut maxSumCl := 0
          for _t in [:trials] do
            let (pts, st₁) := drawCluster s st
            st := st₁
            let (v, w, sm) := audit n s δ big pts
            violCl := violCl + v
            if w > worstCl then worstCl := w
            if sm > maxSumCl then maxSumCl := sm
          -- gon pass (structured legal configs for s ≥ 4)
          let mut okGon := 0
          let mut violGon := 0
          let mut worstGon : Int := 0
          let mut maxSumGon := 0
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
          let cap := 2 ^ n + (if big then 2 ^ (n - 2) else 0)
          IO.println s!"n={n} δ={δ} s={s} | allcfg viol={violAll} worst={worstAll} maxΣ={maxSum} | win ok={checked} viol={violFilt} worst={worstFilt} maxΣ={maxSumF} | modB ok={checkedB} viol={violB} worst={worstB} maxΣ={maxSumB} | gon ok={okGon} viol={violGon} worst={worstGon} maxΣ={maxSumGon} | cl viol={violCl} worst={worstCl} | cap {cap}"
