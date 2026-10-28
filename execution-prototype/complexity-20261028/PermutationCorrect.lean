import MemoComplexity
import GeneralVEExact

/-! Any proposed elimination order can be used for *exact* #SAT counting
    once it is checked to be a permutation of the full variable list.
    No heuristic algorithm needs to be trusted to preserve semantic correctness. -/
namespace GeneralVE

variable {n : Nat} {R : Type*} [CommSemiring R]

/-- Each Boolean variable marginalization commutes with every other one;
    repeated variables commute too, though the scheduling theorem uses a
    permutation without duplicates. -/
theorem marginal_comm (x y : Fin n) (f : Assignment n → R) :
    marginal x (marginal y f) = marginal y (marginal x f) := by
  funext a
  by_cases hxy : x = y
  · subst y
    rfl
  · simp only [marginal]
    simp_rw [Function.update_comm hxy]
    ring

/-- This is the mathematical reason a heuristic variable ordering is safe:
    it does not affect the value of the exact partition function. -/
theorem marginalMany_perm {xs ys : List (Fin n)} (h : xs.Perm ys)
    (f : Assignment n → R) : marginalMany xs f = marginalMany ys f := by
  unfold marginalMany
  apply List.Perm.foldl_eq' h
  intro x _ y _ g
  exact (marginal_comm x y g).symm

end GeneralVE

namespace GeneralVESAT
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SAT

/-- The memoized source implementation with an externally supplied, explicitly
    certified full elimination order. The order can be computed by an untrusted
    min-fill heuristic, since its permutation proof is checked by Lean. -/
def exactCountWithOrder {n : Nat} (F : CNF (Fin n))
    (xs : List (Fin n)) : Nat :=
  GeneralVE.product (GeneralVE.runMemo xs (factors F)) (fun _ => false)

/-- Arbitrary-order exactness: a stronger, general theorem than the fixed
    ‘finRange’ order used in the first implementation. -/
theorem exactCountWithOrder_correct {n : Nat} (F : CNF (Fin n))
    (xs : List (Fin n)) (hperm : xs.Perm (List.finRange n)) :
    exactCountWithOrder F xs = SAT.count F := by
  unfold exactCountWithOrder
  rw [GeneralVE.runMemo_correct]
  rw [GeneralVE.marginalMany_perm hperm]
  rw [← GeneralVE.run_correct]
  exact exactCount_correct F

end GeneralVESAT
