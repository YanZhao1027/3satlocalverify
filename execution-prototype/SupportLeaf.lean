import MomentsSAT

namespace Prototype
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse

/-- Active variables that occur in any literal, including negated literals. -/
def activeVars {n : Nat} (F : CNF (Fin n)) : Finset (Fin n) :=
  F.biUnion fun C => C.image Literal.variable

/-- Assign all absent variables to false for one representative in each fiber. -/
def extendActive {n : Nat} (F : CNF (Fin n))
    (a : {v : Fin n // v ∈ activeVars F} → Bool) : Assignment (Fin n) :=
  fun v => if h : v ∈ activeVars F then a ⟨v, h⟩ else false

/-- Count representatives of assignments over the support and add free-variable factor. -/
def countActive {n : Nat} (F : CNF (Fin n)) : Nat :=
  let S := activeVars F
  let short : Nat := (Finset.univ.filter fun a : {v : Fin n // v ∈ S} → Bool =>
    F.eval (extendActive F a) = true).card
  short * 2 ^ (n - S.card)


abbrev Active {n : Nat} (F : CNF (Fin n)) := {v : Fin n // v ∈ activeVars F}
abbrev Inactive {n : Nat} (F : CNF (Fin n)) := {v : Fin n // v ∉ activeVars F}

/-- A canonical split of an ambient assignment into active and inactive coordinates. -/
def splitAssign {n : Nat} (F : CNF (Fin n)) :
    Assignment (Fin n) ≃ ((Active F → Bool) × (Inactive F → Bool)) where
  toFun := fun a => (fun v => a v.val, fun v => a v.val)
  invFun := fun p v =>
    if h : v ∈ activeVars F then p.1 ⟨v,h⟩ else p.2 ⟨v,h⟩
  left_inv := by
    intro a
    funext v
    by_cases h : v ∈ activeVars F <;> simp [h]
  right_inv := by
    intro p
    rcases p with ⟨a,b⟩
    apply Prod.ext
    · funext v
      simp [v.property]
    · funext v
      simp [v.property]

/-- Every literal's variable is listed in activeVars. -/
private theorem literal_active {n : Nat} (F : CNF (Fin n))
    (C : Clause (Fin n)) (hc : C ∈ F) (l : Literal (Fin n)) (hl : l ∈ C) :
    l.variable ∈ activeVars F := by
  apply Finset.mem_biUnion.mpr
  exact ⟨C,hc,Finset.mem_image.mpr ⟨l,hl,rfl⟩⟩

/-- Values of variables not used by F never affect F.eval. -/
theorem eval_agree_active {n : Nat} (F : CNF (Fin n))
    (a b : Assignment (Fin n))
    (h : ∀ v ∈ activeVars F, a v = b v) : F.eval a = F.eval b := by
  have forward (a b : Assignment (Fin n))
      (hab : ∀ v ∈ activeVars F, a v = b v)
      (ha : F.eval a = true) : F.eval b = true := by
    apply (CNF.eval_eq_true b F).mpr
    intro C hc
    obtain ⟨l,hl,ht⟩ := (Clause.eval_eq_true a C).mp
      ((CNF.eval_eq_true a F).mp ha C hc)
    apply (Clause.eval_eq_true b C).mpr
    refine ⟨l,hl,?_⟩
    have hs := hab l.variable (literal_active F C hc l hl)
    simpa only [Literal.eval, hs] using ht
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact forward a b h
  · exact forward b a (fun v hv => (h v hv).symm)

private theorem eval_split {n : Nat} (F : CNF (Fin n))
    (a : Active F → Bool) (b : Inactive F → Bool) :
    F.eval ((splitAssign F).symm (a,b)) = F.eval (extendActive F a) := by
  apply eval_agree_active
  intro v hv
  simp [splitAssign, extendActive, hv]

private theorem inactive_card {n : Nat} (F : CNF (Fin n)) :
    Fintype.card (Inactive F) = n - (activeVars F).card := by
  rw [Fintype.card_subtype_compl (p := fun v : Fin n => v ∈ activeVars F)]
  simp [Fintype.card_subtype]

/-- Proof that support-only enumeration preserves the exact ambient #SAT count. -/
theorem countActive_correct {n : Nat} (F : CNF (Fin n)) :
    countActive F = SAT.count F := by
  have hcount : SAT.count F =
      ∑ a : Assignment (Fin n), if F.eval a = true then (1 : Nat) else 0 := by
    change (Finset.univ.filter fun a : Assignment (Fin n) => F.eval a = true).card = _
    rw [Finset.card_filter]
  have hsplit :
      (∑ a : Assignment (Fin n), if F.eval a = true then (1 : Nat) else 0) =
      ∑ p : (Active F → Bool) × (Inactive F → Bool),
        if F.eval ((splitAssign F).symm p) = true then (1 : Nat) else 0 := by
    apply Fintype.sum_equiv (splitAssign F)
    intro a
    simp
  rw [hcount, hsplit]
  rw [Fintype.sum_prod_type]
  simp_rw [eval_split]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  rw [Fintype.card_fun, Fintype.card_bool, inactive_card]
  simp [countActive, activeVars, Nat.mul_comm]
  rfl


/-- The number of partial assignments examined is exactly 2^support-size. -/
theorem active_candidates_card {n : Nat} (F : CNF (Fin n)) :
    Fintype.card (Active F → Bool) = 2 ^ (activeVars F).card := by
  rw [Fintype.card_fun, Fintype.card_bool]
  simp [Active, Fintype.card_subtype]

/-- The source sparse DFS transition, replacing its expensive ambient
    count leaf with our support-compressed exact finite counter. -/
def sparseActiveStep {n : Nat} (M : Nat) (s : SparseCountProgram.State n) :
    SparseCountProgram.State n :=
  match s.pending with
  | [] => s
  | node :: rest =>
    match SparsePriority.select node.formula M with
    | none => ⟨rest, s.total + countActive node.formula⟩
    | some (c, H) =>
      ⟨⟨DisjointBranch.childA node.formula c H, node.depth + 1⟩ ::
        ⟨DisjointBranch.childB node.formula c H, node.depth + 1⟩ :: rest, s.total⟩

/-- Checked substitution preserves every intermediate state of the source DFS. -/
theorem sparseActiveStep_eq_source {n : Nat} (M : Nat)
    (s : SparseCountProgram.State n) :
    sparseActiveStep M s = SparseCountProgram.step M s := by
  rcases s with ⟨pending, total⟩
  cases pending with
  | nil => rfl
  | cons node rest =>
      cases hselect : SparsePriority.select node.formula M with
      | none => simp [sparseActiveStep, SparseCountProgram.step, hselect,
                      countActive_correct]
      | some p => simp [sparseActiveStep, SparseCountProgram.step, hselect]

def sparseActiveRun {n : Nat} (M : Nat) :
    Nat → SparseCountProgram.State n → SparseCountProgram.State n
  | 0, s => s
  | t + 1, s => sparseActiveStep M (sparseActiveRun M t s)

theorem sparseActiveRun_eq_source {n : Nat} (M t : Nat)
    (s : SparseCountProgram.State n) :
    sparseActiveRun M t s = SparseCountProgram.run M t s := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [sparseActiveRun, SparseCountProgram.run]
      rw [ih, sparseActiveStep_eq_source]

/-- A terminating run computes the ambient #SAT count, free variables included. -/
theorem sparseActiveRun_exact {n : Nat} (M t : Nat)
    (F : CNF (Fin n))
    (hfinished : (sparseActiveRun M t (SparseCountProgram.initial F)).pending = []) :
    (sparseActiveRun M t (SparseCountProgram.initial F)).total = SAT.count F := by
  rw [sparseActiveRun_eq_source] at *
  exact SparseCountProgram.total_eq_count_of_finished M t F hfinished


/-- Support compression never enumerates more assignments than the ambient
    n-dimensional cube; strict savings when the formula has free variables. -/
theorem active_candidates_le_ambient {n : Nat} (F : CNF (Fin n)) :
    Fintype.card (Active F → Bool) ≤ 2 ^ n := by
  rw [active_candidates_card]
  exact Nat.pow_le_pow_right (by decide)
    ((Finset.card_le_univ (activeVars F)).trans_eq (by simp))

end Prototype
