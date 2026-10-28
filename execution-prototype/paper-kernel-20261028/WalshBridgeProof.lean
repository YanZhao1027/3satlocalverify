import CRTBridgeProof

namespace PaperKernel
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog

private theorem characterInt_zero {n : Nat} (a : Assignment (Fin n)) :
    WalshExistence.characterInt (0 : Cayley.Cube n) (asCube a) = 1 := by
  simp [WalshExistence.characterInt]

private theorem foldl_bool_sum {n : Nat} (F : CNF (Fin n))
    (xs : List (Assignment (Fin n))) (acc : Int) :
    xs.foldl (fun sum a => sum + if F.eval a then (1:Int) else 0) acc =
      acc + (xs.map (fun a => if F.eval a then (1:Int) else 0)).sum := by
  induction xs generalizing acc with
  | nil => simp
  | cons a xs ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih]
      ring

/-- For any CNF, the zero Walsh frequency of its satisfying-indicator
    function equals the ambient exact model count. -/
theorem walsh_zero_eq_count {n : Nat} (F : CNF (Fin n)) :
    walshCoefficient F 0 = (SAT.count F : Int) := by
  unfold walshCoefficient
  simp_rw [characterInt_zero]
  rw [foldl_bool_sum]
  simp only [zero_add]
  rw [← List.sum_toFinset (fun a => if F.eval a then (1:Int) else 0)
        (Prototype.assignments_nodup n)]
  have hset : (Prototype.assignments n).toFinset =
      (Finset.univ : Finset (Assignment (Fin n))) := by
    ext a
    simp [Prototype.assignments_mem]
  rw [hset]
  have hcount : SAT.count F =
      ∑ a : Assignment (Fin n), if F.eval a = true then (1 : Nat) else 0 := by
    change (Finset.univ.filter fun a : Assignment (Fin n) => F.eval a = true).card = _
    rw [Finset.card_filter]
  exact_mod_cast hcount.symm

end PaperKernel
