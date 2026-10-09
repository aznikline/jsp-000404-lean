import Mathlib

/-!
Compact linear certificate checker (n=4 leaf closures).

Every model inequality is homogeneous in `lam`, so atoms are sparse
linear forms `Σ cᵢ·x_{vᵢ} ≤ / < 0` over `x : Fin n → ℝ`.

`pend` queues pending disjunctions (`Disj` = list of `Clause`);
`Cert.node children` resolves the head disjunction — `children[i]`
refutes under clause `i`.  A clause may unlock further flat or-facts
(`nb`/`sep`), queued front or back.
-/

namespace CertCheck

variable {n : ℕ}

structure Atom (n : ℕ) where
  terms : List (Rat × Fin n)
  strict : Bool := false

/-- Coefficient of variable `v` in `a` (duplicates summed). -/
def Atom.coeffAt {n} (a : Atom n) (v : Fin n) : Rat :=
  (a.terms.map fun (c, w) => if w = v then c else 0).sum

/-- Sum of the linear form at `x`. -/
def Atom.lhs {n} (a : Atom n) (x : Fin n → ℝ) : ℝ :=
  ∑ v : Fin n, (a.coeffAt v : ℝ) * x v

/-- `x` satisfies the atom. -/
def Atom.sem {n} (a : Atom n) (x : Fin n → ℝ) : Prop :=
  cond a.strict (a.lhs x < 0) (a.lhs x ≤ 0)

structure Clause (n : ℕ) where
  atoms : List (Atom n)
  front : List (List (Atom n)) := []
  back : List (List (Atom n)) := []

abbrev Disj (n : ℕ) := List (Clause n)

def lift {n} (o : List (Atom n)) : Disj n := o.map fun a => ⟨[a], [], []⟩

inductive Cert where
  | leaf : List Rat → Cert
  | node : List Cert → Cert

def coeffSumZero {n} (ctx : List (Atom n)) (w : List Rat) (v : Fin n) :
    Bool :=
  decide (((ctx.zip w).map fun (a, c) => c * a.coeffAt v).sum = 0)

def checkFarkas (ctx : List (Atom n)) (w : List Rat) : Bool :=
  decide (ctx.length = w.length) &&
    w.all (fun c => decide (0 ≤ c)) &&
    (List.finRange n).all (coeffSumZero ctx w) &&
    (ctx.zip w).any fun (a, c) => a.strict && decide (0 < c)

mutual
def check {n} (ctx : List (Atom n)) (pend : List (Disj n)) : Cert → Bool
  | .leaf w => checkFarkas ctx w
  | .node cs =>
      match pend with
      | [] => false
      | d :: rest => checkAll ctx rest d cs
def checkAll {n} (ctx : List (Atom n)) (rest : List (Disj n)) :
    List (Clause n) → List Cert → Bool
  | cl :: cls, c :: cs =>
      check (ctx ++ cl.atoms)
        (cl.front.map lift ++ rest ++ cl.back.map lift) c &&
      checkAll ctx rest cls cs
  | [], [] => true
  | _, _ => false
end

/-- Semantic content of a clause: atoms hold and every unlocked or holds. -/
def Clause.holds (c : Clause n) (x : Fin n → ℝ) : Prop :=
  (∀ a ∈ c.atoms, a.sem x) ∧
  (∀ o ∈ c.front, ∃ a ∈ o, a.sem x) ∧ ∀ o ∈ c.back, ∃ a ∈ o, a.sem x

/-- Semantic content of a pending disjunction: some clause holds. -/
def Disj.holds (d : Disj n) (x : Fin n → ℝ) : Prop :=
  ∃ c ∈ d, c.holds x

theorem lift_holds {x : Fin n → ℝ} {o : List (Atom n)}
    (h : ∃ a ∈ o, a.sem x) : Disj.holds (lift o) x := by
  obtain ⟨a, ha, hs⟩ := h
  exact ⟨⟨[a], [], []⟩, List.mem_map_of_mem ha,
    ⟨fun b hb => by
        rcases List.mem_singleton.mp hb with rfl; exact hs,
     fun o' ho' => by simp at ho', fun o' ho' => by simp at ho'⟩⟩

/-- Push the cast of a total coefficient into the sparse terms. -/
theorem coeffAt_cast {n} (a : Atom n) (v : Fin n) :
    (a.coeffAt v : ℝ) =
      (a.terms.map fun (c, w) => if w = v then (c : ℝ) else 0).sum := by
  unfold Atom.coeffAt
  induction a.terms with
  | nil => simp
  | cons q tl ih =>
    obtain ⟨c', w'⟩ := q
    simp only [List.map_cons, List.sum_cons, Rat.cast_add]
    rw [ih]
    split_ifs <;> simp

/-- Cast of a weighted coefficient sum distributes to per-element casts. -/
theorem cast_mapsum {n} {v : Fin n} (l : List (Atom n × Rat)) :
    (↑((l.map fun (a, c) => c * a.coeffAt v).sum) : ℝ) =
      ((l.map fun (a, c) => (c : ℝ) * (a.coeffAt v : ℝ)).sum) := by
  induction l with
  | nil => simp
  | cons q tl ih =>
    obtain ⟨a, c⟩ := q
    simp only [List.map_cons, List.sum_cons]

/-- Sparse-term lhs equals the Fin-sum of total coefficients. -/
theorem term_lhs_eq {n} (terms : List (Rat × Fin n)) (x : Fin n → ℝ) :
    (terms.map fun (c, v) => (c : ℝ) * x v).sum =
      ∑ v : Fin n,
        ((terms.map fun (c, w) => if w = v then (c : ℝ) else 0).sum)
          * x v := by
  induction terms with
  | nil => simp
  | cons q tl ih =>
    obtain ⟨c, v⟩ := q
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    -- ⊢ ↑c*x v + Σ_i S_i·x_i = Σ_i ((ite + S_i))·x_i
    have e : ∀ i : Fin n,
        ((if v = i then (c : ℝ) else 0) +
            (tl.map fun (c', w) => if w = i then (c' : ℝ) else 0).sum)
          * x i =
        (if v = i then (c : ℝ) * x i else 0) +
          (tl.map fun (c', w) => if w = i then (c' : ℝ) else 0).sum
            * x i := by
      intro i
      by_cases hvi : v = i <;> simp [hvi, add_mul]
    rw [Finset.sum_congr rfl fun i _ => e i, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_ite_eq]
    simp

/-- Evaluation form of `lhs`: literal sparse sum (used by the oracle
    bridge in generated leaves). -/
theorem lhs_eval {n} (a : Atom n) (x : Fin n → ℝ) :
    a.lhs x = (a.terms.map fun (c, v) => (c : ℝ) * x v).sum := by
  unfold Atom.lhs
  rw [Finset.sum_congr rfl fun v _ => congrArg (· * x v) (coeffAt_cast a v)]
  exact (term_lhs_eq a.terms x).symm

/-- `Σ wⱼ·lhsⱼ ≤ 0` over `(atom, weight)` pairs when all weights are
    nonnegative and every atom holds. -/
theorem weighted_le {x : Fin n → ℝ} (l : List (Atom n × Rat))
    (hp : ∀ p ∈ l, p.1.sem x ∧ (0 : Rat) ≤ p.2) :
    ((l.map fun (a, c) => (c : ℝ) * a.lhs x).sum : ℝ) ≤ 0 := by
  induction l with
  | nil => simp
  | cons p t ih =>
    obtain ⟨a, c⟩ := p
    rw [List.map_cons, List.sum_cons]
    have ha : a.sem x := (hp (a, c) List.mem_cons_self).1
    have hc : (0 : Rat) ≤ c := (hp (a, c) List.mem_cons_self).2
    have hd0 : a.lhs x ≤ 0 := by
      cases hs : a.strict with
      | true =>
        have h : a.lhs x < 0 := by
          simpa [Atom.sem, hs, Bool.cond_true] using ha
        linarith
      | false =>
        have h : a.lhs x ≤ 0 := by
          simpa [Atom.sem, hs, Bool.cond_false] using ha
        exact h
    have hd : (c : ℝ) * a.lhs x ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by exact_mod_cast hc) hd0
    have ihx := ih fun p hp' => hp p (List.mem_cons_of_mem _ hp')
    linarith [hd, ihx]

/-- Strict version: positive weight on a strict atom gives `< 0`. -/
theorem weighted_lt {x : Fin n → ℝ} (l : List (Atom n × Rat))
    (hp : ∀ p ∈ l, p.1.sem x ∧ (0 : Rat) ≤ p.2)
    (hstr : ∃ p ∈ l, p.1.strict = true ∧ (0 : Rat) < p.2) :
    ((l.map fun (a, c) => (c : ℝ) * a.lhs x).sum : ℝ) < 0 := by
  obtain ⟨⟨a, c⟩, hm, hastr, hc⟩ := hstr
  obtain ⟨l₁, l₂, rfl⟩ := List.mem_iff_append.mp hm
  rw [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
  have ha : a.sem x := (hp (a, c) (by simp)).1
  have hd0 : a.lhs x < 0 := by
    have hastr2 : a.strict = true := hastr
    have h : a.lhs x < 0 := by
      unfold Atom.sem at ha
      rw [hastr2] at ha
      simpa using ha
    exact h
  have hmid : (c : ℝ) * a.lhs x < 0 :=
    mul_neg_of_pos_of_neg (by exact_mod_cast hc) hd0
  have hS1 := weighted_le l₁ fun p hp' => hp p (by
    rw [List.mem_append]; exact Or.inl hp')
  have hS2 := weighted_le l₂ fun p hp' => hp p (by
    rw [List.mem_append]; exact Or.inr (List.mem_cons_of_mem _ hp'))
  linarith [hS1, hmid, hS2]

/-- Weighted lhs sum collapses to the Fin-sum of per-variable totals. -/
theorem weighted_lhs_eq {x : Fin n → ℝ} (l : List (Atom n × Rat)) :
    ((l.map fun (a, c) => (c : ℝ) * a.lhs x).sum : ℝ) =
      ∑ v : Fin n,
        (↑((l.map fun (a, c) => c * a.coeffAt v).sum) : ℝ) * x v := by
  induction l with
  | nil => simp
  | cons p t ih =>
    obtain ⟨a, c⟩ := p
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    unfold Atom.lhs
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring

theorem farkas_sound {x : Fin n → ℝ} (ctx : List (Atom n)) (w : List Rat) :
    checkFarkas ctx w = true → (∀ a ∈ ctx, a.sem x) → False := by
  intro h hc
  simp only [checkFarkas, coeffSumZero, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true, List.any_eq_true] at h
  obtain ⟨⟨⟨hlen, hpos⟩, hz⟩, hstr⟩ := h
  have hs : ∀ p ∈ ctx.zip w, p.1.sem x ∧ (0 : Rat) ≤ p.2 := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    rw [List.getElem_zip]
    have h1 : i < ctx.length := by
      rw [List.length_zip] at hi
      omega
    have h2 : i < w.length := by
      rw [List.length_zip] at hi
      omega
    exact ⟨hc _ (List.getElem_mem h1), hpos _ (List.getElem_mem h2)⟩
  obtain ⟨⟨a0, c0⟩, hm0, hastr0, hcpos0⟩ := hstr
  have hlt : ((ctx.zip w).map fun (a, c) => (c : ℝ) * a.lhs x).sum
      < 0 := weighted_lt _ hs ⟨⟨a0, c0⟩, hm0, hastr0, hcpos0⟩
  rw [weighted_lhs_eq] at hlt
  have hz' : ∀ v : Fin n,
      ((ctx.zip w).map fun (a, c) => c * a.coeffAt v).sum = 0 :=
    fun v => hz v (List.mem_finRange v)
  have hz'' : ∀ v : Fin n,
      ((ctx.zip w).map fun (a, c) => (c : ℝ) * (a.coeffAt v : ℝ)).sum
        = 0 := by
    intro v
    have h0 := congrArg (fun r : Rat => (r : ℝ)) (hz' v)
    simp only [Rat.cast_zero] at h0
    push_cast at h0
    rw [List.map_map] at h0
    have hf : (Rat.cast ∘ fun x => x.2 * x.1.coeffAt v :
        Atom n × Rat → ℝ) =
        fun x => (x.2 : ℝ) * (x.1.coeffAt v : ℝ) := by
      funext ⟨a, c⟩
      simp [Rat.cast_mul]
    rw [hf] at h0
    exact h0
  have : (∑ v : Fin n,
      ((ctx.zip w).map fun (a, c) => (c : ℝ) * (a.coeffAt v : ℝ)).sum
        * x v) = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    rw [hz'' v]
    simp
  rw [this] at hlt
  simp at hlt

theorem check_sound {x : Fin n → ℝ} (cert : Cert) :
    ∀ (ctx : List (Atom n)) (pend : List (Disj n)),
      check ctx pend cert = true →
      (∀ a ∈ ctx, a.sem x) →
      (∀ d ∈ pend, d.holds x) → False := by
  refine Cert.rec (motive_2 := fun cs =>
      ∀ (ctx : List (Atom n)) (rest : List (Disj n))
        (cls : List (Clause n)),
        checkAll ctx rest cls cs = true →
        (∀ a ∈ ctx, a.sem x) →
        (∀ d ∈ rest, d.holds x) →
        (∃ c ∈ cls, c.holds x) → False) ?_ ?_ ?_ ?_ cert
  · -- leaf
    intro w ctx pend h hc _
    exact farkas_sound ctx w h hc
  · -- node
    intro cs ih ctx pend h hc hp
    cases pend with
    | nil => simp [check] at h
    | cons d rest =>
      have hd : d.holds x := hp d List.mem_cons_self
      have hrest : ∀ d' ∈ rest, d'.holds x :=
        fun d' hd' => hp d' (List.mem_cons_of_mem _ hd')
      exact ih ctx rest d h hc hrest hd
  · -- nil (motive_2 []): checkAll _ _ cls [] = true, oracle ∃ c∈cls
    intro ctx rest cls h _ _ hor
    cases cls with
    | nil =>
      obtain ⟨c, hcm, _⟩ := hor
      simp at hcm
    | cons cl cls' => simp [checkAll] at h
  · -- cons (motive_2 (c' :: cs'))
    intro c' cs' ihc ihcs ctx rest cls h hc hrest hor
    cases cls with
    | nil => simp [checkAll] at h
    | cons cl cls' =>
      simp only [checkAll, Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      obtain ⟨c, hcm, hcl⟩ := hor
      rcases List.mem_cons.mp hcm with heq | hm
      · -- the head clause is the true one: refute via child c'
        have hcl' : Clause.holds cl x := heq ▸ hcl
        refine ihc _ _ h1 ?_ ?_
        · intro a ha
          rcases List.mem_append.mp ha with hm' | hm'
          · exact hc a hm'
          · exact hcl'.1 a hm'
        · intro d' hd'
          rcases List.mem_append.mp hd' with hm' | hm'
          · rcases List.mem_append.mp hm' with hf | hb
            · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hf
              exact lift_holds (hcl'.2.1 o ho)
            · exact hrest _ hb
          · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hm'
            exact lift_holds (hcl'.2.2 o ho)
      · -- the true clause is among the tail: recurse on cs'
        exact ihcs ctx rest cls' h2 hc hrest ⟨c, hm, hcl⟩

end CertCheck

/-! ## End-to-end pilot: pair_A (0,0), terminal 0

Real extracted core `N0 N4 hc23 hphi ht01 ht0b ht34 ht4b u1e0` decoded to
sparse atoms over `x = [lam, delta, t0..t4, d01..d34]` (17 vars),
`p = 4·lam + delta` eliminated.  Weights solved by the z3 dual
(`tools/pilot/pairA_00_term0_weights.json`); `decide` is the
kernel-checked replay — the solver only discovered the data. -/

namespace Pilot

open CertCheck

/-- Variable order: lam delta t0 t1 t2 t3 t4 d01 d02 d03 d04 d12 d13 d14 d23 d24 d34 -/
def ctx : List (Atom 17) :=
  [ ⟨([(1, 1), (-1, 0)] : List (Rat × Fin 17)), true⟩    -- hphi: delta - lam < 0
  , ⟨[(-1, 2)], false⟩                                   -- ht0b: -t0 ≤ 0
  , ⟨[(1, 6), (-1, 1)], false⟩                           -- ht4b: t4 - delta ≤ 0
  , ⟨[(1, 2), (-1, 3)], true⟩                            -- ht01: t0 - t1 < 0
  , ⟨[(1, 5), (-1, 6)], true⟩                            -- ht34: t3 - t4 < 0
  , ⟨[(1, 4), (1, 0), (-1, 14)], false⟩                  -- hc23a: t2+lam-d23 ≤ 0
  , ⟨[(1, 14), (-3, 0), (-1, 1), (-1, 5)], false⟩        -- hc23b: d23-3lam-delta-t3 ≤ 0
  , ⟨[(1, 3), (3, 0), (-1, 7)], false⟩                   -- u1e0: t1+3lam-d01 ≤ 0
  , ⟨[(1, 7), (1, 0), (-1, 11)], false⟩                  -- N0a: d01+lam-d12 ≤ 0
  , ⟨[(1, 7), (-1, 8)], true⟩                            -- N0b: d01-d02 < 0
  , ⟨[(1, 8), (-1, 11)], true⟩                           -- N0c: d02-d12 < 0
  , ⟨[(1, 11), (1, 0), (-1, 14)], false⟩                 -- N4a: d12+lam-d23 ≤ 0
  , ⟨[(1, 11), (-1, 12)], true⟩                          -- N4b: d12-d13 < 0
  , ⟨[(1, 12), (-1, 14)], true⟩                          -- N4c: d13-d23 < 0
  ]

def w : List Rat := [1/2, 1/4, 1/4, 1/4, 1/4, 0, 1/4, 1/4, 1/4, 0, 0, 1/4, 0, 0]

/-- Kernel-checked: the Farkas certificate verifies. -/
theorem leaf_ok : checkFarkas ctx w = true := by decide +kernel

/-- Negative control: flipping a weight's sign must reject. -/
theorem leaf_bad_neg : checkFarkas ctx
    [-1/2, 1/4, 1/4, 1/4, 1/4, 0, 1/4, 1/4, 1/4, 0, 0, 1/4, 0, 0] =
    false := by decide +kernel

/-- Negative control: all-zero weights must reject — the strict-positivity
    witness is what fails (lengths and cancellation still hold). -/
theorem leaf_bad_zero : checkFarkas ctx (List.replicate 14 0) =
    false := by decide +kernel

/-- Negative control: corrupting one coefficient (-3 → -2 on lam in hc23b)
    breaks cancellation and must reject. -/
theorem leaf_bad_coeff : checkFarkas
    (ctx.set 6 ⟨[(1, 14), (-2, 0), (-1, 1), (-1, 5)], false⟩)
    w = false := by decide +kernel

end Pilot
