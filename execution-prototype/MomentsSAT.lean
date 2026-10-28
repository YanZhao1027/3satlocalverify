import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAlgorithm
import OAI.Algorithms.SubexponentialSAT.SqrtLog.WalshExistence

namespace Prototype
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse

/-- Explicit deterministic order on clauses, using OpenAI's canonical codes. -/
def orderedClauses {n : Nat} (F : CNF (Fin n)) : List (Clause (Fin n)) :=
  let r := fun C D : Clause (Fin n) => Encoding.clauseNumbers C ≤ Encoding.clauseNumbers D
  letI : IsTrans _ r := ⟨fun _ _ _ => le_trans⟩
  letI : Std.Total r := ⟨fun _ _ => le_total _ _⟩
  letI : Std.Antisymm r :=
    ⟨fun _ _ h h' => Encoding.clauseNumbers_injective (le_antisymm h h')⟩
  F.sort r

/-- Explicitly enumerate all finite Boolean assignments using upstream tuple enumerator. -/
def assignments (n : Nat) : List (Assignment (Fin n)) :=
  WalshExistence.tuples [false, true] n

/-- A concrete computational instance of the upstream head moments engine.
    All arithmetic is exact Nat, and costs each scalar/add/mul/project operation 1. -/
def natOps {n : Nat} : MomentsAlgorithm.Ops Nat (Assignment (Fin n)) Nat where
  zero := 0
  one := 1
  add := fun a b => (a+b,1)
  mul := fun a b => (a*b,1)
  scale := fun r a => (r*a,1)
  project := fun _ a => (a,1)

/-- Each clause is a one-term head: 1 iff the assignment satisfies it. -/
def clauseHeads {n : Nat} (F : CNF (Fin n)) (a : Assignment (Fin n)) :
    List (List (Nat × Nat)) :=
  (orderedClauses F).map fun C => [(1, (C.eval a).toNat)]

/-- Exact counting using the actual source MomentsAlgorithm.run for product and sum.
    WARNING: the assignment list enumerates all 2^n assignments. -/
def countMoments {n : Nat} (F : CNF (Fin n)) : Nat :=
  (MomentsAlgorithm.run (natOps (n := n)) (clauseHeads F) (assignments n)).1

/-- Actual exact arithmetic cost charged by the source's arithmetic-operation model. -/
def momentsCost {n : Nat} (F : CNF (Fin n)) : Nat :=
  (MomentsAlgorithm.run (natOps (n := n)) (clauseHeads F) (assignments n)).2


private theorem head_eval {n : Nat} (v : Nat) :
    (MomentsAlgorithm.head (natOps (n := n)) [(1, v)]).1 = v := by
  simp [natOps, MomentsAlgorithm.head]

private theorem heads_eval {n : Nat} (a : Assignment (Fin n))
    (cs : List (Clause (Fin n))) :
    (MomentsAlgorithm.heads (natOps (n := n))
      (cs.map fun C => [(1, (C.eval a).toNat)])).1 =
    (cs.map fun C => (C.eval a).toNat).prod := by
  induction cs with
  | nil => rfl
  | cons C cs ih =>
      simp only [MomentsAlgorithm.heads, List.map_cons, List.prod_cons]
      change (MomentsAlgorithm.head (natOps (n := n)) [(1, (C.eval a).toNat)]).1 *
        (MomentsAlgorithm.heads (natOps (n := n))
          (cs.map fun C => [(1, (C.eval a).toNat)])).1 =
        (C.eval a).toNat * (cs.map fun C => (C.eval a).toNat).prod
      rw [head_eval, ih]

private theorem listProdBool {α : Type*} (f : α → Bool) (cs : List α) :
    (cs.map fun x => (f x).toNat).prod =
    (decide (∀ x ∈ cs, f x = true)).toNat := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
      cases h : f c <;> simp [h, ih]

private theorem heads_eq_eval {n : Nat} (F : CNF (Fin n))
    (a : Assignment (Fin n)) :
    (MomentsAlgorithm.heads (natOps (n := n)) (clauseHeads F a)).1 =
      (F.eval a).toNat := by
  rw [clauseHeads, heads_eval, listProdBool]
  simp [CNF.eval, orderedClauses]

private theorem moments_run_values {n : Nat} (F : CNF (Fin n))
    (as : List (Assignment (Fin n))) :
    (MomentsAlgorithm.run (natOps (n := n)) (clauseHeads F) as).1 =
    (as.map fun a => (F.eval a).toNat).sum := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      simp only [MomentsAlgorithm.run, List.map_cons, List.sum_cons]
      change (MomentsAlgorithm.heads (natOps (n := n)) (clauseHeads F a)).1 +
        (MomentsAlgorithm.run (natOps (n := n)) (clauseHeads F) as).1 =
        (F.eval a).toNat + (as.map fun a => (F.eval a).toNat).sum
      rw [heads_eq_eval, ih]


/-- Source tuple enumerator never repeats a Boolean assignment. -/
theorem assignments_nodup (n : Nat) : (assignments n).Nodup := by
  induction n with
  | zero => simp [assignments, WalshExistence.tuples]
  | succ n ih =>
      simp only [assignments, WalshExistence.tuples, List.flatMap_cons,
        List.flatMap_nil, List.append_nil] at *
      have hinj (b : Bool) : Function.Injective
          (fun x : Fin n → Bool => Fin.cons (α := fun _ : Fin (n + 1) => Bool) b x) := by
        intro x y h
        exact (Fin.cons_inj.mp h).2
      have hfalse := ih.map (hinj false)
      have htrue := ih.map (hinj true)
      apply hfalse.append htrue
      intro a ha hb
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
      obtain ⟨y, _, hy⟩ := List.mem_map.mp hb
      have contra : false = true := (Fin.cons_inj.mp hy.symm).1
      contradiction

/-- The upstream finite enumerator covers all Boolean assignments. -/
theorem assignments_mem {n : Nat} (a : Assignment (Fin n)) : a ∈ assignments n := by
  unfold assignments
  apply WalshExistence.mem_tuples
  intro b
  cases b <;> simp

private theorem assignments_toFinset (n : Nat) :
    (assignments n).toFinset = (Finset.univ : Finset (Assignment (Fin n))) := by
  classical
  ext a
  simp [assignments_mem]

/-- Executable MomentsAlgorithm-derived counting equals the official SAT.count
    for *every* finite CNF, not only tested instances. -/
theorem countMoments_correct {n : Nat} (F : CNF (Fin n)) :
    countMoments F = SAT.count F := by
  unfold countMoments
  rw [moments_run_values]
  rw [← List.sum_toFinset (fun a => (F.eval a).toNat) (assignments_nodup n)]
  rw [assignments_toFinset]
  simp only [SAT.count, SAT.satisfyingAssignments, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro a ha
  cases h : F.eval a <;> simp


/-- Same physical pending/total state as the upstream sparse DFS, but each leaf
    is evaluated by the executable original MomentsAlgorithm.run, not SAT.count. -/
def sparseMomentsStep {n : Nat} (M : Nat) (s : SparseCountProgram.State n) :
    SparseCountProgram.State n :=
  match s.pending with
  | [] => s
  | node :: rest =>
    match SparsePriority.select node.formula M with
    | none => ⟨rest, s.total + countMoments node.formula⟩
    | some (c, H) =>
      ⟨⟨DisjointBranch.childA node.formula c H, node.depth + 1⟩ ::
        ⟨DisjointBranch.childB node.formula c H, node.depth + 1⟩ :: rest, s.total⟩

/-- New leaf engine is *extensionally exactly* the original Lean DFS transition. -/
theorem sparseMomentsStep_eq_source {n : Nat} (M : Nat) (s : SparseCountProgram.State n) :
    sparseMomentsStep M s = SparseCountProgram.step M s := by
  rcases s with ⟨pending, total⟩
  cases pending with
  | nil => rfl
  | cons node rest =>
      cases hselect : SparsePriority.select node.formula M with
      | none => simp [sparseMomentsStep, SparseCountProgram.step, hselect,
                      countMoments_correct]
      | some p => simp [sparseMomentsStep, SparseCountProgram.step, hselect]

/-- Finite iteration of the actual OpenAI sparse DFS with the executable moments leaf. -/
def sparseMomentsRun {n : Nat} (M : Nat) : Nat → SparseCountProgram.State n → SparseCountProgram.State n
  | 0, s => s
  | t + 1, s => sparseMomentsStep M (sparseMomentsRun M t s)

/-- The entire reconnected algorithm is identical to the upstream DFS semantics. -/
theorem sparseMomentsRun_eq_source {n : Nat} (M t : Nat)
    (s : SparseCountProgram.State n) :
    sparseMomentsRun M t s = SparseCountProgram.run M t s := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [sparseMomentsRun, SparseCountProgram.run]
      rw [ih, sparseMomentsStep_eq_source]

/-- A completed operational run computes the exact satisfying assignment count. -/
theorem sparseMomentsRun_exact {n : Nat} (M t : Nat) (F : CNF (Fin n))
    (hfinished : (sparseMomentsRun M t (SparseCountProgram.initial F)).pending = []) :
    (sparseMomentsRun M t (SparseCountProgram.initial F)).total = SAT.count F := by
  rw [sparseMomentsRun_eq_source] at *
  exact SparseCountProgram.total_eq_count_of_finished M t F hfinished


/-- Exactly three charged Nat operations per clause in the heads arithmetic. -/
private theorem heads_cost {n : Nat} (a : Assignment (Fin n))
    (cs : List (Clause (Fin n))) :
    (MomentsAlgorithm.heads (natOps (n := n))
      (cs.map fun C => [(1, (C.eval a).toNat)])).2 = 3 * cs.length := by
  induction cs with
  | nil => rfl
  | cons C cs ih =>
      simp only [List.map_cons, List.length_cons, MomentsAlgorithm.heads]
      change 2 + (MomentsAlgorithm.heads (natOps (n := n))
        (cs.map fun C => [(1, (C.eval a).toNat)])).2 + 1 =
        3 * (cs.length + 1)
      rw [ih]
      omega

private theorem orderedClauses_length {n : Nat} (F : CNF (Fin n)) :
    (orderedClauses F).length = F.card := by
  simp [orderedClauses]

private theorem run_cost {n : Nat} (F : CNF (Fin n))
    (as : List (Assignment (Fin n))) :
    (MomentsAlgorithm.run (natOps (n := n)) (clauseHeads F) as).2 =
      as.length * (3 * F.card + 2) := by
  induction as with
  | nil => simp [MomentsAlgorithm.run]
  | cons a as ih =>
      simp only [MomentsAlgorithm.run, List.length_cons]
      change (MomentsAlgorithm.heads (natOps (n := n)) (clauseHeads F a)).2 + 1 +
        (MomentsAlgorithm.run (natOps (n := n)) (clauseHeads F) as).2 + 1 =
        (as.length + 1) * (3 * F.card + 2)
      rw [ih]
      rw [show (MomentsAlgorithm.heads (natOps (n := n)) (clauseHeads F a)).2 =
         3 * F.card by
        unfold clauseHeads
        rw [heads_cost, orderedClauses_length]]
      ring

private theorem assignments_length (n : Nat) : (assignments n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [assignments, WalshExistence.tuples, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.length_append,
        List.length_map] at *
      rw [pow_succ]
      omega

/-- This bridge's charged arithmetic work is explicitly exponential.
    It does NOT satisfy the paper's subexponential leaf bound. -/
theorem momentsCost_exact {n : Nat} (F : CNF (Fin n)) :
    momentsCost F = (2 ^ n) * (3 * F.card + 2) := by
  unfold momentsCost
  rw [run_cost, assignments_length]

end Prototype
