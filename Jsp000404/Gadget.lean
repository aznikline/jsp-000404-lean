import Jsp000404.ChainWitness
import Mathlib.Data.Fintype.Fin
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.BooleanAlgebra

/-!
# Gadget — the frozen local certificate object

A `Gadget` is the finite combinatorial certificate discovered by
`tools/link_graph.py`: signed fan equalities, signed triangle links,
angle-bound *charges* on positive leftover blocks, and *cap* bounds
covering negative leftover blocks.  `Valid` replays the checker's
per-vertex cover conditions; `gadget_ge` packages a valid gadget plus
a capacity hypothesis into the level bound `δ ≥ t`.

## Residual bookkeeping (mirrors the checker exactly)

For mode-A equalities written `LHS = RHS` we accumulate the residual
form `Σ coef·r + dco·δ + con = 0`, i.e. `P − U − c·δ = C` with

    c = -dco,   C = -con,   P = Σ coef⁺·r,   U = Σ coef⁻·r.

* fan at `v` with weight `w`:
  `w·(Σ_g r_{v,g} − δ) = w·(n − Σ_g q_{v,g})`
* link `σ·Δ{a,b,h}`: `σ·(∠a{b,h} + ∠b{a,h} + ∠h{a,b}) = σ·(n+δ)`
  where a *complementary* angle unfolds as `n + δ − arc` and a
  *direct* angle as `arc`, `arc = Σ_{g∈rng} (q_g + r_g)`;
* charge on complementary `∠v{a,b}`: `∠ ≤ π−λ` gives
  `Σ_arc r ≥ 1 − q_arc` (δ-free);
* caps: direct `∠v{a,b} ≤ π−λ` gives `Σ_arc r ≤ (n−1−q_arc) + δ`;
  complementary `∠v{a,b} ≥ 0` gives `Σ_arc r ≤ (n−q_arc) + δ`;
  and the trivial `r_g ≤ 1`.

A cap entry with multiplicity `m` supplies `m` units of coverage to
*every* gap in its range (`m·Σ_range r ≤ m·B + m·u·δ`); covering a
gap with coefficient `κ` requires total supplied multiplicity `≥ κ`.
-/

namespace Jsp404

open Finset

/-- Per-vertex static skeleton data: `pos u` the position of vertex
`u` in the cyclic fan order, `bits u` its direction bit, `q g` the
integer cell of gap `g`. -/
structure VertexData (s : ℕ) where
  pos : Fin s → Fin (s - 1)
  bits : Fin s → Bool
  q : Fin (s - 1) → ℤ

/-- A skeleton: per-vertex data for `s` vertices. -/
structure Skeleton (s : ℕ) where
  vtx : Fin s → VertexData s

namespace VertexData

variable {s : ℕ} (v : VertexData s)

/-- Gaps strictly between `a` and `b` in the cyclic order at `v`. -/
def arc (a b : Fin s) : Finset (Fin (s - 1)) :=
  Finset.Ico (v.pos a ⊓ v.pos b) (v.pos a ⊔ v.pos b)

/-- Integer content of the arc `a→b` at `v`. -/
def arcQ (a b : Fin s) : ℤ := ∑ g ∈ v.arc a b, v.q g

/-- Whether `∠v{a,b}` is complementary (`n+δ−arc`) rather than
direct (`arc`). -/
def comp (a b : Fin s) : Prop := v.bits a ≠ v.bits b

end VertexData

/-- The unfolded angle expression `∠x{a,b}` in λ-units. -/
def angleExpr {s : ℕ} (n : ℕ) (sk : Skeleton s)
    (r : Fin s → Fin (s - 1) → ℝ) (δ : ℝ) (x a b : Fin s) : ℝ :=
  if (sk.vtx x).bits a = (sk.vtx x).bits b then
    ∑ g ∈ (sk.vtx x).arc a b, (((sk.vtx x).q g : ℝ) + r x g)
  else (n : ℝ) + δ - ∑ g ∈ (sk.vtx x).arc a b, (((sk.vtx x).q g : ℝ) + r x g)

/-- The mode-A constraint bundle over a skeleton: hypotheses about
the real unknowns `r`, `δ` at the fixed exponent `n`. -/
structure ModeA {s : ℕ} (n : ℕ) (sk : Skeleton s)
    (r : Fin s → Fin (s - 1) → ℝ) (δ : ℝ) : Prop where
  r_nn : ∀ v g, 0 ≤ r v g
  r_le : ∀ v g, r v g ≤ 1
  fan : ∀ v, (∑ g, r v g) - δ = (n : ℝ) - ∑ g, (sk.vtx v).q g
  tri : ∀ a b h : Fin s, a ≠ b → a ≠ h → b ≠ h →
        angleExpr n sk r δ a b h + angleExpr n sk r δ b a h
          + angleExpr n sk r δ h a b = (n : ℝ) + δ
  ang_le : ∀ x a b : Fin s, a ≠ b →
        angleExpr n sk r δ x a b ≤ (n : ℝ) - 1 + δ
  ang_nn : ∀ x a b : Fin s, a ≠ b →
        0 ≤ angleExpr n sk r δ x a b

/-! ### Formal residual bookkeeping -/

/-- Formal linear combination of remainder variables, `δ` and a
constant: represents `Σ coef·r + dco·δ + con = 0`. -/
structure LinForm (s : ℕ) where
  coef : Fin s → Fin (s - 1) → ℤ
  dco : ℤ
  con : ℤ

namespace LinForm

variable {s : ℕ}

def eval (f : LinForm s) (r : Fin s → Fin (s - 1) → ℝ) (δ : ℝ) : ℝ :=
  (∑ v : Fin s, ∑ g : Fin (s - 1), (f.coef v g : ℝ) * r v g)
    + (f.dco : ℝ) * δ + (f.con : ℝ)

instance : Zero (LinForm s) := ⟨⟨fun _ _ => 0, 0, 0⟩⟩

instance : Add (LinForm s) :=
  ⟨fun f₁ f₂ =>
    ⟨fun v g => f₁.coef v g + f₂.coef v g,
     f₁.dco + f₂.dco, f₁.con + f₂.con⟩⟩

def smul (w : ℤ) (f : LinForm s) : LinForm s :=
  ⟨fun v g => w * f.coef v g, w * f.dco, w * f.con⟩

instance : SMul ℤ (LinForm s) := ⟨smul⟩

theorem coef_zero : (0 : LinForm s).coef = fun _ _ => 0 := rfl
theorem dco_zero : (0 : LinForm s).dco = 0 := rfl
theorem con_zero : (0 : LinForm s).con = 0 := rfl
theorem coef_add (f₁ f₂ : LinForm s) :
    (f₁ + f₂).coef = fun v g => f₁.coef v g + f₂.coef v g := rfl
theorem dco_add (f₁ f₂ : LinForm s) :
    (f₁ + f₂).dco = f₁.dco + f₂.dco := rfl
theorem con_add (f₁ f₂ : LinForm s) :
    (f₁ + f₂).con = f₁.con + f₂.con := rfl
theorem coef_smul (w : ℤ) (f : LinForm s) :
    (w • f).coef = fun v g => w * f.coef v g := rfl
theorem dco_smul (w : ℤ) (f : LinForm s) :
    (w • f).dco = w * f.dco := rfl
theorem con_smul (w : ℤ) (f : LinForm s) :
    (w • f).con = w * f.con := rfl

@[simp] theorem eval_zero (r δ) : eval (0 : LinForm s) r δ = 0 := by
  simp only [eval, coef_zero, dco_zero, con_zero, Int.cast_zero,
    zero_mul, add_zero, mul_zero, Finset.sum_const_zero]

theorem eval_add (f₁ f₂ : LinForm s) (r δ) :
    eval (f₁ + f₂) r δ = eval f₁ r δ + eval f₂ r δ := by
  have h1 : ∀ v g, (((f₁ + f₂).coef v g : ℤ) : ℝ) * r v g
      = (f₁.coef v g : ℝ) * r v g + (f₂.coef v g : ℝ) * r v g := by
    intro v g
    rw [coef_add]
    show ((f₁.coef v g + f₂.coef v g : ℤ) : ℝ) * r v g = _
    push_cast; ring
  have h2 : (((f₁ + f₂).dco : ℤ) : ℝ) = (f₁.dco : ℝ) + f₂.dco :=
    Int.cast_add _ _
  have h3 : (((f₁ + f₂).con : ℤ) : ℝ) = (f₁.con : ℝ) + f₂.con :=
    Int.cast_add _ _
  simp only [eval]
  rw [Finset.sum_congr rfl fun v _ =>
        Finset.sum_congr rfl fun g _ => h1 v g]
  rw [Finset.sum_congr rfl fun v _ => Finset.sum_add_distrib]
  rw [Finset.sum_add_distrib, h2, h3]
  ring

theorem eval_smul (w : ℤ) (f : LinForm s) (r δ) :
    eval (w • f) r δ = (w : ℝ) * eval f r δ := by
  have h1 : ∀ v g, (((w • f).coef v g : ℤ) : ℝ) * r v g
      = (w : ℝ) * ((f.coef v g : ℝ) * r v g) := by
    intro v g
    rw [coef_smul]
    show ((w * f.coef v g : ℤ) : ℝ) * r v g = _
    push_cast; ring
  have h2 : (((w • f).dco : ℤ) : ℝ) = (w : ℝ) * f.dco :=
    Int.cast_mul _ _
  have h3 : (((w • f).con : ℤ) : ℝ) = (w : ℝ) * f.con :=
    Int.cast_mul _ _
  simp only [eval]
  rw [Finset.sum_congr rfl fun v _ =>
        Finset.sum_congr rfl fun g _ => h1 v g]
  rw [Finset.sum_congr rfl fun v _ => (Finset.mul_sum ..).symm]
  rw [← Finset.mul_sum, h2, h3]
  ring

/-- Sum of a list of forms. -/
def formSum : List (LinForm s) → LinForm s
  | [] => 0
  | f :: fs => f + formSum fs

theorem eval_formSum (l : List (LinForm s)) (r δ) :
    eval (formSum l) r δ = (l.map (fun f => eval f r δ)).sum := by
  induction l with
  | nil => simp [formSum]
  | cons f fs ih => simp [formSum, eval_add, ih]

theorem list_sum_eq_zero {l : List ℝ}
    (h : ∀ x ∈ l, x = 0) : l.sum = 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp [List.sum_cons, h x (List.mem_cons_self ..),
        ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

end LinForm

/-- Residual form of the fan equality at `v`:
`Σ_g r_{v,g} − δ − (n − Σ_g q_{v,g}) = 0`. -/
def fanForm {s : ℕ} (n : ℕ) (sk : Skeleton s) (v : Fin s) :
    LinForm s where
  coef := fun w g => if w = v then 1 else 0
  dco := -1
  con := (∑ g, (sk.vtx v).q g) - n

/-- Residual contribution of the angle term `∠x{u,w}` inside a
triangle equality. -/
def angleTerm {s : ℕ} (n : ℕ) (sk : Skeleton s) (x u w : Fin s) :
    LinForm s :=
  if (sk.vtx x).bits u = (sk.vtx x).bits w then
    { coef := fun v g => if v = x ∧ g ∈ (sk.vtx x).arc u w then 1 else 0
      dco := 0
      con := (sk.vtx x).arcQ u w }
  else
    { coef := fun v g => if v = x ∧ g ∈ (sk.vtx x).arc u w then -1 else 0
      dco := 1
      con := (n : ℤ) - (sk.vtx x).arcQ u w }

/-- Residual form of the triangle equality `Δ{a,b,h}`:
`∠a{b,h} + ∠b{a,h} + ∠h{a,b} − δ − n = 0`. -/
def linkForm {s : ℕ} (n : ℕ) (sk : Skeleton s) (a b h : Fin s) :
    LinForm s :=
  angleTerm n sk a b h + angleTerm n sk b a h + angleTerm n sk h a b
    + ⟨fun _ _ => 0, -1, -(n : ℤ)⟩

/-- The coefficient sum of an indicator-weighted gap block. -/
theorem sum_coef_ite {s : ℕ} (x : Fin s) (arc : Finset (Fin (s - 1)))
    (k : ℤ) (r : Fin s → Fin (s - 1) → ℝ) :
    (∑ v : Fin s, ∑ g : Fin (s - 1),
        ((if v = x ∧ g ∈ arc then k else 0 : ℤ) : ℝ) * r v g)
      = (k : ℝ) * ∑ g ∈ arc, r x g := by
  rw [Finset.sum_eq_single x]
  · have h2 : ∀ g : Fin (s - 1),
        ((if x = x ∧ g ∈ arc then k else 0 : ℤ) : ℝ) * r x g
          = if g ∈ arc then (k : ℝ) * r x g else 0 := by
      intro g
      by_cases hg : g ∈ arc <;> simp [hg]
    rw [Finset.sum_congr rfl fun g _ => h2 g, ← Finset.sum_filter,
        Finset.mul_sum, Finset.filter_univ_mem]
  · intro v _ hv
    apply Finset.sum_eq_zero
    intro g _
    simp [hv]
  · simp

theorem fanForm_eval {s : ℕ} {n : ℕ} {sk : Skeleton s} {r δ}
    (hA : ModeA n sk r δ) (v : Fin s) :
    (fanForm n sk v).eval r δ = 0 := by
  have h := hA.fan v
  simp only [LinForm.eval, fanForm]
  rw [Finset.sum_eq_single v]
  · simp only [↓reduceIte, Int.cast_one, one_mul]
    push_cast at h ⊢
    linarith
  · intro w _ hw
    apply Finset.sum_eq_zero
    intro g _
    simp [hw]
  · simp

theorem angleTerm_eval {s : ℕ} {n : ℕ} {sk : Skeleton s} {r δ}
    (x u w : Fin s) :
    (angleTerm n sk x u w).eval r δ
      = angleExpr n sk r δ x u w := by
  unfold angleTerm angleExpr
  split_ifs with h
  · simp only [LinForm.eval, VertexData.arcQ, Int.cast_zero,
      zero_mul, add_zero]
    rw [sum_coef_ite, Finset.sum_add_distrib]
    push_cast
    ring
  · simp only [LinForm.eval, VertexData.arcQ, Int.cast_one,
      Int.cast_neg]
    rw [sum_coef_ite, Finset.sum_add_distrib]
    push_cast
    ring

theorem linkForm_eval {s : ℕ} {n : ℕ} {sk : Skeleton s} {r δ}
    (hA : ModeA n sk r δ) {a b h : Fin s}
    (hab : a ≠ b) (hah : a ≠ h) (hbh : b ≠ h) :
    (linkForm n sk a b h).eval r δ = 0 := by
  have h := hA.tri a b h hab hah hbh
  simp only [linkForm, LinForm.eval_add, angleTerm_eval]
  simp only [LinForm.eval]
  simp only [Int.cast_zero, Int.cast_neg, Int.cast_one,
    zero_mul, add_zero, Finset.sum_const_zero, mul_zero,
    Int.cast_natCast]
  linarith

/-! ### The gadget object -/

/-- Cap bound kind. `rle` uses `r_g ≤ 1`; `piLam` a direct angle
bound `Σ_arc r ≤ (n−1−q_arc)+δ`; `nn` a complementary `∠ ≥ 0`
giving `Σ_arc r ≤ (n−q_arc)+δ`. -/
inductive CapKind | rle | piLam | nn

/-- A cap bound entry: multiplicity `m` supplies `m` units of
coverage to every gap in `range`. -/
structure CapEntry (s : ℕ) where
  v : Fin s
  kind : CapKind
  a : Fin s
  b : Fin s
  gap : Fin (s - 1)
  m : ℤ

namespace CapEntry

variable {s : ℕ} (n : ℕ) (sk : Skeleton s) (e : CapEntry s)

/-- Gap range covered by this entry. -/
def range : Finset (Fin (s - 1)) :=
  match e.kind with
  | .rle => {e.gap}
  | .piLam => (sk.vtx e.v).arc e.a e.b
  | .nn => (sk.vtx e.v).arc e.a e.b

/-- Constant part of the bound: `Σ_range r ≤ B + u·δ`. -/
def B : ℤ :=
  match e.kind with
  | .rle => 1
  | .piLam => (n : ℤ) - 1 - (sk.vtx e.v).arcQ e.a e.b
  | .nn => (n : ℤ) - (sk.vtx e.v).arcQ e.a e.b

/-- δ-coefficient of the bound. -/
def u : ℤ :=
  match e.kind with
  | .rle => 0
  | _ => 1

/-- Local well-formedness of the entry. -/
def wf : Prop :=
  0 < e.m ∧ match e.kind with
  | .rle => True
  | .piLam => e.a ≠ e.b ∧ ¬ (sk.vtx e.v).comp e.a e.b
  | .nn => e.a ≠ e.b ∧ (sk.vtx e.v).comp e.a e.b

end CapEntry

/-- A gadget: the finite certificate data.  `fans v` is the fan
weight (±1 or 0); each link `(a,b,h,σ)` is `σ·Δ{a,b,h}`; each
charge `(v,a,b)` invokes the complementary-angle bound
`Σ_arc r ≥ 1 − q_arc` at `v`. -/
structure Gadget (s : ℕ) where
  fans : Fin s → ℤ
  links : List (Fin s × Fin s × Fin s × ℤ)
  charges : List (Fin s × Fin s × Fin s)
  caps : List (CapEntry s)

namespace Gadget

variable {s : ℕ} (n : ℕ) (sk : Skeleton s) (g : Gadget s)

/-- The combined residual form. -/
def form : LinForm s :=
  LinForm.formSum
    (((List.finRange s).map fun v => g.fans v • fanForm n sk v)
     ++ g.links.map fun l =>
        l.2.2.2 • linkForm n sk l.1 l.2.1 l.2.2.1)

/-- Residual coefficient on `r_{v,g}`. -/
def coef (v : Fin s) (gg : Fin (s - 1)) : ℤ := (g.form n sk).coef v gg

/-- Gain contributed by charge `(v,a,b)`:
`min_{g∈arc} coef · (1 − q_arc)`; zero for empty arcs. -/
def chargeGain (v a b : Fin s) : ℤ :=
  if h : ((sk.vtx v).arc a b).Nonempty then
    (((sk.vtx v).arc a b).image (g.coef n sk v)).min' (h.image _)
      * (1 - (sk.vtx v).arcQ a b)
  else 0

def K : ℤ := (g.charges.map fun e =>
    g.chargeGain n sk e.1 e.2.1 e.2.2).sum
def Bcap : ℤ := (g.caps.map fun e => e.m * e.B n sk).sum
def uu : ℤ := (g.caps.map fun e => e.m * e.u).sum
def cc : ℤ := -(g.form n sk).dco
def CC : ℤ := -(g.form n sk).con

/-- The gadget bound: `δ ≥ (K − Bcap − C)/(c + u)`.  Zero when the
denominator is nonpositive. -/
def bound : ℚ :=
  if (g.cc n sk : ℚ) + g.uu ≤ 0 then 0
  else ((g.K n sk - g.Bcap n sk - g.CC n sk : ℤ) : ℚ)
      / ((g.cc n sk : ℚ) + g.uu)

/-- Validity of a gadget over a skeleton — a faithful replay of the
checker's per-vertex cover conditions. -/
def Valid : Prop :=
    (∀ v, g.fans v = 1 ∨ g.fans v = -1 ∨ g.fans v = 0)
  ∧ (∀ l ∈ g.links,
        (l.2.2.2 = 1 ∨ l.2.2.2 = -1)
        ∧ l.1 ≠ l.2.1 ∧ l.1 ≠ l.2.2.1 ∧ l.2.1 ≠ l.2.2.1)
  ∧ (∀ e ∈ g.charges,
        let vx := sk.vtx e.1
        e.2.1 ≠ e.2.2
        ∧ vx.comp e.2.1 e.2.2
        ∧ (vx.arc e.2.1 e.2.2).Nonempty
        ∧ ∀ gg ∈ vx.arc e.2.1 e.2.2, 0 < g.coef n sk e.1 gg)
  ∧ g.charges.Pairwise (fun e e' =>
        e.1 ≠ e'.1 ∨
          Disjoint ((sk.vtx e.1).arc e.2.1 e.2.2)
            ((sk.vtx e'.1).arc e'.2.1 e'.2.2))
  ∧ (∀ e ∈ g.caps, e.wf sk)
  ∧ (∀ v gg, g.coef n sk v gg < 0 →
        -g.coef n sk v gg
          ≤ ((g.caps.filter fun e =>
                e.v = v ∧ gg ∈ e.range sk).map CapEntry.m).sum)
  ∧ 0 < g.cc n sk + g.uu

/-- The packaged witness: `P` collects positively-signed leftover
remainders, `U` the negative part, and the scalar fields replay the
checker computation. -/
noncomputable def witness (r : Fin s → Fin (s - 1) → ℝ) (δ : ℝ) :
    ResidualWitness where
  P := ∑ v : Fin s, ∑ gg : Fin (s - 1),
        (max (g.coef n sk v gg) 0 : ℝ) * r v gg
  U := ∑ v : Fin s, ∑ gg : Fin (s - 1),
        (max (-g.coef n sk v gg) 0 : ℝ) * r v gg
  C := (g.CC n sk : ℝ)
  K := (g.K n sk : ℝ)
  c := (g.cc n sk : ℝ)
  u := (g.uu : ℝ)
  B := (g.Bcap n sk : ℝ)
  δ := δ

/-- Each cap entry bounds its range: `Σ_range r ≤ B + u·δ`. -/
theorem cap_bound {r : Fin s → Fin (s - 1) → ℝ} {δ : ℝ}
    (hA : ModeA n sk r δ) (e : CapEntry s) (hw : e.wf sk) :
    (∑ gg ∈ e.range sk, r e.v gg)
      ≤ (e.B n sk : ℝ) + (e.u : ℝ) * δ := by
  obtain ⟨hm, hk⟩ := hw
  cases hkind : e.kind with
  | rle =>
      simp only [CapEntry.range, CapEntry.B, CapEntry.u, hkind,
        Finset.sum_singleton, Int.cast_one, Int.cast_zero,
        zero_mul, add_zero]
      exact hA.r_le _ _
  | piLam =>
      simp only [hkind] at hk
      obtain ⟨hab, hdir⟩ := hk
      have h := hA.ang_le e.v e.a e.b hab
      unfold angleExpr at h
      rw [if_pos (by simpa [VertexData.comp] using hdir)] at h
      simp only [CapEntry.range, CapEntry.B, CapEntry.u, hkind,
        VertexData.arcQ, Int.cast_one]
      rw [Finset.sum_add_distrib] at h
      push_cast
      linarith
  | nn =>
      simp only [hkind] at hk
      obtain ⟨hab, hcomp⟩ := hk
      have h := hA.ang_nn e.v e.a e.b hab
      unfold angleExpr at h
      rw [if_neg (by simpa [VertexData.comp] using hcomp)] at h
      simp only [CapEntry.range, CapEntry.B, CapEntry.u, hkind,
        VertexData.arcQ, Int.cast_one]
      rw [Finset.sum_add_distrib] at h
      push_cast
      linarith

/-- Each charge entry yields its lower bound:
`Σ_arc r ≥ 1 − q_arc` (from `∠ ≤ π−λ` on a complementary angle). -/
theorem charge_bound {r : Fin s → Fin (s - 1) → ℝ} {δ : ℝ}
    (hA : ModeA n sk r δ) {v a b : Fin s}
    (hab : a ≠ b) (hc : (sk.vtx v).comp a b) :
    (1 : ℝ) - (sk.vtx v).arcQ a b
      ≤ ∑ gg ∈ (sk.vtx v).arc a b, r v gg := by
  have h := hA.ang_le v a b hab
  unfold angleExpr at h
  rw [if_neg (by simpa [VertexData.comp] using hc)] at h
  simp only [VertexData.arcQ]
  rw [Finset.sum_add_distrib] at h
  push_cast
  linarith

/-- The gadget's residual identity: under mode-A, the formal
combination evaluates to zero. -/
theorem residual_eval {r : Fin s → Fin (s - 1) → ℝ} {δ : ℝ}
    (hA : ModeA n sk r δ)
    (hlinks : ∀ l ∈ g.links,
        l.1 ≠ l.2.1 ∧ l.1 ≠ l.2.2.1 ∧ l.2.1 ≠ l.2.2.1) :
    (g.form n sk).eval r δ = 0 := by
  unfold Gadget.form
  rw [LinForm.eval_formSum, List.map_append, List.sum_append]
  have hfan : (((List.finRange s).map fun v =>
          g.fans v • fanForm n sk v).map
        (fun f => f.eval r δ)).sum = 0 := by
    apply LinForm.list_sum_eq_zero
    intro x hx
    simp only [List.mem_map, List.mem_finRange, true_and] at hx
    obtain ⟨f, ⟨v, _, rfl⟩, rfl⟩ := hx
    show (g.fans v • fanForm n sk v).eval r δ = 0
    rw [LinForm.eval_smul, fanForm_eval hA v, mul_zero]
  have hlink : ((g.links.map fun l =>
          l.2.2.2 • linkForm n sk l.1 l.2.1 l.2.2.1).map
        (fun f => f.eval r δ)).sum = 0 := by
    apply LinForm.list_sum_eq_zero
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨f, ⟨l, hl, rfl⟩, rfl⟩ := hx
    show (l.2.2.2 • linkForm n sk l.1 l.2.1 l.2.2.1).eval r δ = 0
    rw [LinForm.eval_smul]
    obtain ⟨hab, hah, hbh⟩ := hlinks l hl
    rw [linkForm_eval hA hab hah hbh, mul_zero]
  rw [hfan, hlink, add_zero]

/-- `P − U` telescopes to the residual coefficient evaluation. -/
theorem pos_neg_eval {r : Fin s → Fin (s - 1) → ℝ} :
    (∑ v : Fin s, ∑ gg : Fin (s - 1),
        (max (g.coef n sk v gg) 0 : ℝ) * r v gg)
    - (∑ v : Fin s, ∑ gg : Fin (s - 1),
        (max (-g.coef n sk v gg) 0 : ℝ) * r v gg)
    = ∑ v : Fin s, ∑ gg : Fin (s - 1),
        (g.coef n sk v gg : ℝ) * r v gg := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun v _ => by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun gg _ => by
      by_cases h : 0 < g.coef n sk v gg
      · have h' : (0 : ℝ) ≤ (g.coef n sk v gg : ℝ) := by
          exact_mod_cast le_of_lt h
        rw [max_eq_left h',
            max_eq_right (by
              have : (-g.coef n sk v gg : ℝ) ≤ 0 := by
                exact_mod_cast neg_nonpos.mpr (le_of_lt h)
              exact this)]
        simp
      · have h' : (g.coef n sk v gg : ℝ) ≤ 0 := by
          exact_mod_cast le_of_not_gt h
        rw [max_eq_right h',
            max_eq_left (by
              have : (0 : ℝ) ≤ (-g.coef n sk v gg : ℝ) := by
                exact_mod_cast neg_nonneg.mpr (le_of_not_gt h)
              exact this)]
        simp

section ListHelpers

private theorem intCast_list_sum (l : List ℤ) :
    ((l.sum : ℤ) : ℝ) = (l.map fun x => (x : ℝ)).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [List.sum_cons, ih]

private theorem intCast_list_sum_map {α : Type*} (l : List α)
    (f : α → ℤ) :
    (((l.map f).sum : ℤ) : ℝ)
      = (l.map fun a => ((f a : ℤ) : ℝ)).sum := by
  induction l with
  | nil => simp
  | cons a as ih => simp [List.map_cons, List.sum_cons, ih]

private theorem list_sum_map_filter {α : Type*} (l : List α)
    (p : α → Prop) [DecidablePred p] (f : α → ℝ) :
    ((l.filter p).map f).sum
      = (l.map fun a => if p a then f a else 0).sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
      by_cases h : p a <;> simp [h, ih]

private theorem finset_sum_list_sum_comm {α β : Type*} (s : Finset α)
    (l : List β) (f : β → α → ℝ) :
    (∑ x ∈ s, (l.map fun e => f e x).sum)
      = (l.map fun e => ∑ x ∈ s, f e x).sum := by
  induction l with
  | nil => simp
  | cons e es ih =>
      simp [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]

private theorem list_sum_map_add {α : Type*} (l : List α)
    (f h : α → ℝ) :
    (l.map fun a => f a + h a).sum
      = (l.map f).sum + (l.map h).sum := by
  induction l with
  | nil => simp
  | cons a as ih => simp only [List.map_cons, List.sum_cons, ih]; ring

private theorem list_sum_map_mul {α : Type*} (l : List α)
    (f : α → ℝ) (c : ℝ) :
    (l.map fun a => f a * c).sum = (l.map f).sum * c := by
  induction l with
  | nil => simp
  | cons a as ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- Disjoint-arc packing: a list of pairwise-`R`-separated finsets
has its `f`-weight bounded by the total weight, when `R` implies
disjointness of the images and `f ≥ 0`. -/
private theorem list_sum_le_univ_of_pairwise_disjoint
    {ι α : Type*} [Fintype α] [DecidableEq α]
    {R : ι → ι → Prop} {S : ι → Finset α} (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    ∀ (l : List ι) (T : Finset α),
      l.Pairwise R → (∀ a ∈ l, S a ⊆ T) →
      (∀ a b, R a b → Disjoint (S a) (S b)) →
      (l.map fun i => ∑ x ∈ S i, f x).sum ≤ ∑ x ∈ T, f x := by
  intro l T hdj hsub hR
  induction l generalizing T with
  | nil =>
      simp only [List.map_nil, List.sum_nil]
      exact Finset.sum_nonneg fun x _ => hf x
  | cons a es ih =>
      obtain ⟨hd, hd2⟩ := List.pairwise_cons.mp hdj
      simp only [List.map_cons, List.sum_cons]
      have hsT : S a ⊆ T := hsub a List.mem_cons_self
      have key := ih (T \ S a) hd2
        (fun s' hs' => Finset.subset_sdiff.mpr
          ⟨hsub s' (List.mem_cons_of_mem _ hs'),
            (hR a s' (hd s' hs')).symm⟩)
      calc ∑ x ∈ S a, f x + (es.map fun i => ∑ x ∈ S i, f x).sum
          ≤ ∑ x ∈ S a, f x + ∑ x ∈ T \ S a, f x :=
            add_le_add_right key _
        _ = ∑ x ∈ T, f x := by
            rw [add_comm, Finset.sum_sdiff hsT]

end ListHelpers

/-- Charge total bound: `K ≤ P`. -/
theorem charge_total {r : Fin s → Fin (s - 1) → ℝ} {δ : ℝ}
    (hA : ModeA n sk r δ)
    (hch : ∀ e ∈ g.charges,
        e.2.1 ≠ e.2.2 ∧ (sk.vtx e.1).comp e.2.1 e.2.2
        ∧ ((sk.vtx e.1).arc e.2.1 e.2.2).Nonempty
        ∧ ∀ gg ∈ (sk.vtx e.1).arc e.2.1 e.2.2,
            0 < g.coef n sk e.1 gg)
    (hdj : g.charges.Pairwise (fun e e' =>
        e.1 ≠ e'.1 ∨
          Disjoint ((sk.vtx e.1).arc e.2.1 e.2.2)
            ((sk.vtx e'.1).arc e'.2.1 e'.2.2))) :
    (g.K n sk : ℝ)
      ≤ ∑ v : Fin s, ∑ gg : Fin (s - 1),
          (max (g.coef n sk v gg) 0 : ℝ) * r v gg := by
  -- per-charge bound: gain ≤ Σ_arc (max coef 0)·r
  have per : ∀ e ∈ g.charges,
      (g.chargeGain n sk e.1 e.2.1 e.2.2 : ℝ)
        ≤ ∑ gg ∈ (sk.vtx e.1).arc e.2.1 e.2.2,
            (max (g.coef n sk e.1 gg : ℝ) 0) * r e.1 gg := by
    intro e he
    obtain ⟨hab, hc, hne, hpos⟩ := hch e he
    have hmn_nn : (0:ℤ) ≤ (((sk.vtx e.1).arc e.2.1 e.2.2).image
        (g.coef n sk e.1)).min' (hne.image _) := by
      have hmem := Finset.min'_mem _ (hne.image (g.coef n sk e.1))
      rw [Finset.mem_image] at hmem
      obtain ⟨g0, hg0, hge⟩ := hmem
      rw [← hge]
      exact le_of_lt (hpos g0 hg0)
    have hmn_nn' : (0:ℝ) ≤ ((((sk.vtx e.1).arc e.2.1 e.2.2).image
        (g.coef n sk e.1)).min' (hne.image _) : ℤ) := by
      exact_mod_cast hmn_nn
    have hb := charge_bound n sk hA hab hc
    have hmul := mul_le_mul_of_nonneg_left hb hmn_nn'
    rw [Finset.mul_sum] at hmul
    have hle : ∀ gg ∈ (sk.vtx e.1).arc e.2.1 e.2.2,
        (((((sk.vtx e.1).arc e.2.1 e.2.2).image
            (g.coef n sk e.1)).min' (hne.image _) : ℤ) : ℝ)
            * r e.1 gg
          ≤ (max (g.coef n sk e.1 gg : ℝ) 0) * r e.1 gg := by
      intro gg hgg
      have hcpos := hpos gg hgg
      have hmnle : (((sk.vtx e.1).arc e.2.1 e.2.2).image
            (g.coef n sk e.1)).min' (hne.image _)
          ≤ g.coef n sk e.1 gg :=
        Finset.min'_le _ _ (Finset.mem_image.mpr ⟨gg, hgg, rfl⟩)
      rw [max_eq_left (show (0:ℝ) ≤ (g.coef n sk e.1 gg : ℝ) by
        exact_mod_cast le_of_lt hcpos)]
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast hmnle) (hA.r_nn _ _)
    have hcg : g.chargeGain n sk e.1 e.2.1 e.2.2
        = (((sk.vtx e.1).arc e.2.1 e.2.2).image
            (g.coef n sk e.1)).min' (hne.image _)
          * (1 - (sk.vtx e.1).arcQ e.2.1 e.2.2) :=
      dif_pos hne
    rw [hcg]
    push_cast
    exact le_trans hmul (Finset.sum_le_sum hle)
  -- cast K and bound pointwise
  have hK : (g.K n sk : ℝ)
      = (g.charges.map fun e =>
          (g.chargeGain n sk e.1 e.2.1 e.2.2 : ℝ)).sum := by
    simp only [K]
    rw [intCast_list_sum_map]
  -- packing: arcs embedded as (v, gap) pairs are pairwise disjoint
  have hdisj : g.charges.Pairwise (fun e e' =>
      Disjoint (((sk.vtx e.1).arc e.2.1 e.2.2).image (Prod.mk e.1))
        (((sk.vtx e'.1).arc e'.2.1 e'.2.2).image (Prod.mk e'.1))) :=
    hdj.imp fun {e e'} h => by
      rcases h with hv | hd
      · rw [Finset.disjoint_left]
        rintro x hx hx'
        rw [Finset.mem_image] at hx hx'
        obtain ⟨g1, _, h1⟩ := hx
        obtain ⟨g2, _, h2⟩ := hx'
        rw [← h1] at h2
        have hv' : e.1 = e'.1 := (Prod.ext_iff.mp h2).1.symm
        exact hv hv'
      · rw [Finset.disjoint_left]
        rintro x hx hx'
        rw [Finset.mem_image] at hx hx'
        obtain ⟨g1, hg1, h1⟩ := hx
        obtain ⟨g2, hg2, h2⟩ := hx'
        rw [← h1] at h2
        obtain ⟨hvv, hgg⟩ := Prod.ext_iff.mp h2
        have hgg' : g2 = g1 := hgg
        exact absurd (hgg' ▸ hg2)
          ((Finset.disjoint_left.mp hd) hg1)
  have hconv : (g.charges.map fun e =>
        ∑ gg ∈ (sk.vtx e.1).arc e.2.1 e.2.2,
          (max (g.coef n sk e.1 gg : ℝ) 0) * r e.1 gg).sum
      = (g.charges.map fun e =>
          ∑ x ∈ ((sk.vtx e.1).arc e.2.1 e.2.2).image (Prod.mk e.1),
            (max (g.coef n sk x.1 x.2 : ℝ) 0) * r x.1 x.2).sum := by
    congr 1
    apply List.map_congr_left
    intro e _
    rw [Finset.sum_image (by
      intro x _ y _ hxy
      exact (Prod.ext_iff.mp hxy).2)]
  have hmain :=
    list_sum_le_univ_of_pairwise_disjoint
      (f := fun p : Fin s × Fin (s - 1) =>
        (max (g.coef n sk p.1 p.2 : ℝ) 0) * r p.1 p.2)
      (hf := fun x =>
        mul_nonneg (le_max_right _ _) (hA.r_nn _ _))
      g.charges Finset.univ hdisj
      (fun _ _ => Finset.subset_univ _)
      (fun e e' h => h)
  have huniv : (∑ x : Fin s × Fin (s - 1),
        (max (g.coef n sk x.1 x.2 : ℝ) 0) * r x.1 x.2)
      = ∑ v : Fin s, ∑ gg : Fin (s - 1),
          (max (g.coef n sk v gg : ℝ) 0) * r v gg := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
  calc (g.K n sk : ℝ)
      = (g.charges.map fun e =>
          (g.chargeGain n sk e.1 e.2.1 e.2.2 : ℝ)).sum := hK
    _ ≤ (g.charges.map fun e =>
          ∑ gg ∈ (sk.vtx e.1).arc e.2.1 e.2.2,
            (max (g.coef n sk e.1 gg : ℝ) 0) * r e.1 gg).sum :=
        List.sum_le_sum fun e he => per e he
    _ = (g.charges.map fun e =>
          ∑ x ∈ ((sk.vtx e.1).arc e.2.1 e.2.2).image (Prod.mk e.1),
            (max (g.coef n sk x.1 x.2 : ℝ) 0) * r x.1 x.2).sum :=
        hconv
    _ ≤ ∑ x : Fin s × Fin (s - 1),
          (max (g.coef n sk x.1 x.2 : ℝ) 0) * r x.1 x.2 := hmain
    _ = ∑ v : Fin s, ∑ gg : Fin (s - 1),
          (max (g.coef n sk v gg : ℝ) 0) * r v gg := huniv

/-- Cap total bound: `U ≤ Bcap + u·δ`. -/
theorem cap_total {r : Fin s → Fin (s - 1) → ℝ} {δ : ℝ}
    (hA : ModeA n sk r δ)
    (hcaps : ∀ e ∈ g.caps, e.wf sk)
    (hcov : ∀ v gg, g.coef n sk v gg < 0 →
        -g.coef n sk v gg
          ≤ ((g.caps.filter fun e =>
                e.v = v ∧ gg ∈ e.range sk).map CapEntry.m).sum) :
    (∑ v : Fin s, ∑ gg : Fin (s - 1),
        (max (-g.coef n sk v gg) 0 : ℝ) * r v gg)
      ≤ (g.Bcap n sk : ℝ) + (g.uu : ℝ) * δ := by
  -- pointwise bound: the negative part is dominated by coverage
  have pt : ∀ (v : Fin s) (gg : Fin (s - 1)),
      (max (-(g.coef n sk v gg : ℝ)) 0) * r v gg
        ≤ (((g.caps.filter fun e =>
              e.v = v ∧ gg ∈ e.range sk).map CapEntry.m).sum : ℝ)
          * r v gg := by
    intro v gg
    by_cases hneg : g.coef n sk v gg < 0
    · have hc := hcov v gg hneg
      have hcast : (-(g.coef n sk v gg : ℝ))
          ≤ (((g.caps.filter fun e =>
                e.v = v ∧ gg ∈ e.range sk).map CapEntry.m).sum
              : ℝ) := by
        exact_mod_cast hc
      rw [max_eq_left (show (0:ℝ) ≤ -(g.coef n sk v gg : ℝ) by
        have : (0:ℤ) ≤ -g.coef n sk v gg := by omega
        exact_mod_cast this)]
      exact mul_le_mul_of_nonneg_right hcast (hA.r_nn _ _)
    · rw [max_eq_right (show (-(g.coef n sk v gg : ℝ)) ≤ 0 by
          have : -g.coef n sk v gg ≤ 0 := by omega
          exact_mod_cast this)]
      simp only [zero_mul]
      apply mul_nonneg _ (hA.r_nn _ _)
      have hc0 : (0:ℤ) ≤ ((g.caps.filter fun e =>
            e.v = v ∧ gg ∈ e.range sk).map CapEntry.m).sum :=
        List.sum_nonneg fun x hx => by
          simp only [List.mem_map, List.mem_filter] at hx
          obtain ⟨e, he, rfl⟩ := hx
          exact le_of_lt (hcaps e he.1).1
      exact_mod_cast hc0
  -- rewrite coverage as a full-list indicator sum and swap the
  -- finset/list double sum
  have coveq : ∀ (v : Fin s) (gg : Fin (s - 1)),
      (((g.caps.filter fun e =>
            e.v = v ∧ gg ∈ e.range sk).map CapEntry.m).sum : ℝ)
          * r v gg
        = (g.caps.map fun e =>
            if e.v = v ∧ gg ∈ e.range sk then (e.m : ℝ) * r v gg
            else 0).sum := by
    intro v gg
    rw [intCast_list_sum_map, list_sum_map_filter,
        ← list_sum_map_mul]
    simp only [ite_mul, zero_mul]
  have inner : ∀ e : CapEntry s,
      (∑ v : Fin s, ∑ gg : Fin (s - 1),
          if e.v = v ∧ gg ∈ e.range sk then (e.m : ℝ) * r v gg
          else 0)
        = (e.m : ℝ) * ∑ gg ∈ e.range sk, r e.v gg := by
    intro e
    rw [Finset.sum_eq_single e.v]
    · have h2 : ∀ gg : Fin (s - 1),
          (if e.v = e.v ∧ gg ∈ e.range sk then (e.m : ℝ) * r e.v gg
            else 0)
            = if gg ∈ e.range sk then (e.m : ℝ) * r e.v gg
              else 0 := by
        intro gg; by_cases hg : gg ∈ e.range sk <;> simp [hg]
      rw [Finset.sum_congr rfl fun gg _ => h2 gg,
          ← Finset.sum_filter, Finset.filter_univ_mem,
          Finset.mul_sum]
    · intro v _ hv
      apply Finset.sum_eq_zero
      intro gg _
      exact if_neg (fun h => hv h.1.symm)
    · simp
  have ebound : ∀ e ∈ g.caps,
      (e.m : ℝ) * ∑ gg ∈ e.range sk, r e.v gg
        ≤ (e.m : ℝ) * ((e.B n sk : ℝ) + (e.u : ℝ) * δ) :=
    fun e he => mul_le_mul_of_nonneg_left
      (cap_bound n sk hA e (hcaps e he))
      (by exact_mod_cast le_of_lt (hcaps e he).1)
  have distribute :
      (g.caps.map fun e =>
          (e.m : ℝ) * ((e.B n sk : ℝ) + (e.u : ℝ) * δ)).sum
        = (g.Bcap n sk : ℝ) + (g.uu : ℝ) * δ := by
    have h1 : ∀ e : CapEntry s,
        (e.m : ℝ) * ((e.B n sk : ℝ) + (e.u : ℝ) * δ)
          = (e.m : ℝ) * (e.B n sk : ℝ) + (e.m : ℝ) * (e.u : ℝ) * δ :=
      fun e => by ring
    rw [List.map_congr_left fun e _ => h1 e]
    rw [list_sum_map_add, list_sum_map_mul]
    have hB : (((g.caps.map fun e =>
            e.m * e.B n sk).sum : ℤ) : ℝ)
        = (g.caps.map fun e =>
            (e.m : ℝ) * (e.B n sk : ℝ)).sum := by
      rw [intCast_list_sum_map]
      exact congrArg List.sum
        (List.map_congr_left fun e _ =>
          Int.cast_mul e.m (e.B n sk))
    have hU : (((g.caps.map fun e => e.m * e.u).sum : ℤ) : ℝ)
        = (g.caps.map fun e =>
            (e.m : ℝ) * (e.u : ℝ)).sum := by
      rw [intCast_list_sum_map]
      exact congrArg List.sum
        (List.map_congr_left fun e _ =>
          Int.cast_mul e.m e.u)
    simp only [Bcap, uu]
    rw [hB, hU]
  calc (∑ v : Fin s, ∑ gg : Fin (s - 1),
          (max (-(g.coef n sk v gg : ℝ)) 0) * r v gg)
      ≤ ∑ v : Fin s, ∑ gg : Fin (s - 1),
          (((g.caps.filter fun e =>
              e.v = v ∧ gg ∈ e.range sk).map CapEntry.m).sum : ℝ)
            * r v gg :=
        Finset.sum_le_sum fun v _ =>
          Finset.sum_le_sum fun gg _ => pt v gg
    _ = ∑ v : Fin s, ∑ gg : Fin (s - 1),
          (g.caps.map fun e =>
            if e.v = v ∧ gg ∈ e.range sk then (e.m : ℝ) * r v gg
            else 0).sum := by
        exact Finset.sum_congr rfl fun v _ =>
          Finset.sum_congr rfl fun gg _ => coveq v gg
    _ = ∑ v : Fin s, (g.caps.map fun e =>
          ∑ gg : Fin (s - 1),
            if e.v = v ∧ gg ∈ e.range sk then (e.m : ℝ) * r v gg
            else 0).sum := by
        exact Finset.sum_congr rfl fun v _ =>
          finset_sum_list_sum_comm Finset.univ g.caps _
    _ = (g.caps.map fun e =>
          ∑ v : Fin s, ∑ gg : Fin (s - 1),
            if e.v = v ∧ gg ∈ e.range sk then (e.m : ℝ) * r v gg
            else 0).sum :=
        finset_sum_list_sum_comm Finset.univ g.caps _
    _ = (g.caps.map fun e =>
          (e.m : ℝ) * ∑ gg ∈ e.range sk, r e.v gg).sum := by
        congr 1
        exact List.map_congr_left fun e _ => inner e
    _ ≤ (g.caps.map fun e =>
          (e.m : ℝ) * ((e.B n sk : ℝ) + (e.u : ℝ) * δ)).sum :=
        List.sum_le_sum ebound
    _ = (g.Bcap n sk : ℝ) + (g.uu : ℝ) * δ := distribute

/-- The gadget's residual and bound conditions, packaged for
`debt_residual_ge`. -/
theorem gadget_fields {r : Fin s → Fin (s - 1) → ℝ} {δ : ℝ}
    (hA : ModeA n sk r δ) (hg : g.Valid n sk) :
    let w := g.witness n sk r δ
    w.P - w.U - w.c * w.δ = w.C
      ∧ w.K ≤ w.P
      ∧ w.U ≤ w.B + w.u * w.δ
      ∧ 0 < w.c + w.u := by
  obtain ⟨hfw, hlinks, hch, hdj, hcaps, hcov, hcu⟩ := hg
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h0 := g.residual_eval n sk hA (fun l hl => (hlinks l hl).2)
    simp only [LinForm.eval] at h0
    have hpn := g.pos_neg_eval n sk (r := r)
    simp only [Gadget.coef] at hpn
    rw [← hpn] at h0
    show (∑ v : Fin s, ∑ gg : Fin (s - 1),
          (max (g.coef n sk v gg : ℝ) 0) * r v gg)
        - (∑ v : Fin s, ∑ gg : Fin (s - 1),
          (max (-(g.coef n sk v gg : ℝ)) 0) * r v gg)
        - (g.cc n sk : ℝ) * δ = (g.CC n sk : ℝ)
    simp only [Gadget.cc, Gadget.CC, Gadget.coef, Int.cast_neg]
    linarith
  · exact g.charge_total n sk hA hch hdj
  · exact g.cap_total n sk hA hcaps hcov
  · show (0:ℝ) < (g.cc n sk : ℝ) + (g.uu : ℝ)
    have : (0:ℤ) < g.cc n sk + g.uu := hcu
    exact_mod_cast this

/-- Level theorem: a valid gadget whose capacity condition holds at
level `t` forces `δ ≥ t`. -/
theorem gadget_ge {r : Fin s → Fin (s - 1) → ℝ} {δ : ℝ} {t : ℝ}
    (hA : ModeA n sk r δ) (hg : g.Valid n sk)
    (ht : t * ((g.cc n sk : ℝ) + (g.uu : ℝ))
        ≤ (g.K n sk : ℝ) - (g.Bcap n sk : ℝ) - (g.CC n sk : ℝ)) :
    t ≤ δ := by
  have ⟨h1, h2, h3, h4⟩ := g.gadget_fields n sk hA hg
  exact debt_residual_ge h1 h2 h3 h4 ht

/-- Level 1: score ≥ 1 forces `δ ≥ 1/2`. -/
theorem gadget_ge_half {r : Fin s → Fin (s - 1) → ℝ} {δ : ℝ}
    (hA : ModeA n sk r δ) (hg : g.Valid n sk)
    (ht : (((g.cc n sk : ℝ) + (g.uu : ℝ)) / 2)
        ≤ (g.K n sk : ℝ) - (g.Bcap n sk : ℝ) - (g.CC n sk : ℝ)) :
    (1 : ℝ) / 2 ≤ δ := by
  apply g.gadget_ge n sk hA hg (t := 1 / 2)
  linarith

/-- Level 2: score ≥ 2 forces `δ ≥ 1`. -/
theorem gadget_ge_one {r : Fin s → Fin (s - 1) → ℝ} {δ : ℝ}
    (hA : ModeA n sk r δ) (hg : g.Valid n sk)
    (ht : ((g.cc n sk : ℝ) + (g.uu : ℝ))
        ≤ (g.K n sk : ℝ) - (g.Bcap n sk : ℝ) - (g.CC n sk : ℝ)) :
    (1 : ℝ) ≤ δ := by
  apply g.gadget_ge n sk hA hg (t := 1)
  linarith

end Gadget

end Jsp404
