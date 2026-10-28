import GeneralVESAT
import MarginalComplete

namespace GeneralVESAT
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SAT

/-- A complete, general theorem for any CNF over Fin n, with no constraints
    on width, treewidth, connectivity, satisfiability or elimination order.

    The executable bucket algorithm uses a fixed full variable order here;
    GeneralVE.run_correct already proves its semantics for *every* schedule.
    The result is exactly SAT.count, including all ambient free variables. -/
theorem exact_count {n : Nat} (F : CNF (Fin n))
    (a : Assignment (Fin n)) :
    GeneralVE.product (runFactors F) a = SAT.count F := by
  rw [runFactors_correct, GeneralVE.marginalMany_finRange]
  change (∑ b : Assignment (Fin n), (F.eval b).toNat) =
    (Finset.univ.filter fun b : Assignment (Fin n) => F.eval b = true).card
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro b _
  cases h : F.eval b <;> simp [h]

/-- The final answer is independent of the chosen base assignment. -/
def exactCount {n : Nat} (F : CNF (Fin n)) : Nat :=
  GeneralVE.product (runFactors F) (fun _ => false)

theorem exactCount_correct {n : Nat} (F : CNF (Fin n)) :
    exactCount F = SAT.count F :=
  exact_count F (fun _ => false)

end GeneralVESAT
