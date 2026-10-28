import VerifiedReconstruction
import CRTBridgeProof

namespace VerifiedReconstruction
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SAT
open Polynomial

/-- For every modulus and CNF, the violation polynomial has degree bounded by
    the number of clauses, with no assumption about connectedness or width. -/
theorem violation_degree_le {n m : Nat} (F : CNF (Fin n)) :
    (GeneralVEWeighted.violationPoly (p := m) F).natDegree ≤ F.card := by
  unfold GeneralVEWeighted.violationPoly
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro a _
  let k := PaperKernel.countViolations (Prototype.orderedClauses F) a
  calc
    ((Polynomial.X : Polynomial (ZMod m)) ^ k).natDegree ≤
        k * (Polynomial.X : Polynomial (ZMod m)).natDegree :=
          Polynomial.natDegree_pow_le
    _ ≤ k * 1 := Nat.mul_le_mul_left k Polynomial.natDegree_X_le
    _ = k := by omega
    _ ≤ (Prototype.orderedClauses F).length := by
         exact List.length_filter_le (fun C => !(C.eval a)) (Prototype.orderedClauses F)
    _ = F.card := by simp [Prototype.orderedClauses]

end VerifiedReconstruction
