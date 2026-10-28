import CRTKernel

namespace PaperKernel
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SAT

/-- An assignment violates zero clauses exactly when it satisfies the CNF. -/
theorem zeroViolations_iff {n : Nat} (cs : List (Clause (Fin n)))
    (a : Assignment (Fin n)) :
    countViolations cs a = 0 ↔ CNF.eval a (cs.toFinset : CNF (Fin n)) = true := by
  unfold countViolations
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  constructor
  · intro h
    apply (CNF.eval_eq_true a (cs.toFinset)).mpr
    intro C hC
    have hm : C ∈ cs := by simpa using hC
    have hh := h C hm
    cases hv : C.eval a <;> simp [hv] at hh ⊢
  · intro h
    intro C hC
    have he := (CNF.eval_eq_true a (cs.toFinset)).mp h C (by simpa using hC)
    simp [he]

/-- The constant coefficient of the violation polynomial is precisely #SAT.
    This is a generic theorem, not merely the successful concrete examples. -/
theorem coefficient_zero_correct {n : Nat} (cs : List (Clause (Fin n))) :
    coefficient cs 0 = SAT.count (cs.toFinset : CNF (Fin n)) := by
  let F : CNF (Fin n) := cs.toFinset
  have hset : (Prototype.assignments n).toFinset =
      (Finset.univ : Finset (Assignment (Fin n))) := by
    ext a
    simp [Prototype.assignments_mem]
  have hnodup : ((Prototype.assignments n).filter
      (fun a => decide (countViolations cs a = 0))).Nodup :=
    (Prototype.assignments_nodup n).filter _
  unfold coefficient
  calc
    ((Prototype.assignments n).filter
      (fun a => decide (countViolations cs a = 0))).length =
      (((Prototype.assignments n).filter
        (fun a => decide (countViolations cs a = 0))).toFinset).card :=
        (List.toFinset_card_of_nodup hnodup).symm
    _ = (Finset.univ.filter fun a : Assignment (Fin n) => F.eval a = true).card := by
      rw [List.toFinset_filter, hset]
      congr 1
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa only [decide_eq_true_eq, F] using zeroViolations_iff cs a
    _ = SAT.count F := by rfl

end PaperKernel
