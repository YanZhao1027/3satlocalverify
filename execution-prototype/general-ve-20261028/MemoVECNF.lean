import MemoVE
import GeneralVEExact
import DualJetProof

namespace MemoVECNF
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SAT

variable {n : Nat} {R : Type*} [CommSemiring R]

/-- Table-backed #SAT counter, preserving GeneralVEExact.exactCount semantics. -/
def exactMemo (F : CNF (Fin n)) : Nat :=
  GeneralVE.product (GeneralVE.runMemo (List.finRange n)
    (GeneralVESAT.factors F)) (fun _ => false)

theorem exactMemo_correct (F : CNF (Fin n)) :
    exactMemo F = SAT.count F := by
  unfold exactMemo
  rw [GeneralVE.runMemo_correct, GeneralVE.marginalMany_finRange]
  have heq : GeneralVE.product (GeneralVESAT.factors F) =
      (fun a => (F.eval a).toNat) := by
    funext a
    exact GeneralVESAT.product_factors_eq_eval F a
  rw [heq]
  have hcount : SAT.count F =
      ∑ a : Assignment (Fin n), (F.eval a).toNat := by
    change (Finset.univ.filter fun a : Assignment (Fin n) => F.eval a = true).card = _
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro a _
    cases h : F.eval a <;> simp [h]
  exact hcount.symm

/-- Same source weighted-count semantics with one explicitly materialized
    table at each newly eliminated bucket, instead of repeated closures. -/
def weightedMemo (F : CNF (Fin n)) (x : R) : R :=
  GeneralVE.product (GeneralVE.runMemo (List.finRange n)
    (GeneralVEWeighted.factors F x)) (fun _ => false)

theorem weightedMemo_eq_source (F : CNF (Fin n)) (x : R) :
    weightedMemo F x = GeneralVEWeighted.weightedTotal F x := by
  unfold weightedMemo GeneralVEWeighted.weightedTotal
  rw [GeneralVE.runMemo_correct, GeneralVE.run_correct]

private def dualNode {p : Nat} (x : ZMod p) : DualNumber (ZMod p) := ⟨x,1⟩

/-- A cached, completely Lean first-order Hermite jet generator. -/
def memoDualJet (F : CNF (Fin n)) {p : Nat} (x : ZMod p) :
    DualNumber (ZMod p) :=
  weightedMemo (R := DualNumber (ZMod p)) F (dualNode x)

theorem memoDualJet_eq_source (F : CNF (Fin n)) {p : Nat} (x : ZMod p) :
    memoDualJet F x = GeneralVEWeighted.dualJet F x := by
  simpa only [memoDualJet, GeneralVEWeighted.dualJet, dualNode] using
    (weightedMemo_eq_source (R := DualNumber (ZMod p)) F (dualNode x))

/-- Caching preserves both universally verified Hermite coordinates. -/
theorem memoDualJet_value_correct (F : CNF (Fin n)) {p : Nat} (x : ZMod p) :
    (memoDualJet F x).fst = Polynomial.eval x (GeneralVEWeighted.violationPoly F) := by
  rw [memoDualJet_eq_source]
  exact GeneralVEWeighted.dualJet_value_correct F x

theorem memoDualJet_derivative_correct (F : CNF (Fin n)) {p : Nat} (x : ZMod p) :
    (memoDualJet F x).snd =
      Polynomial.eval x (Polynomial.derivative (GeneralVEWeighted.violationPoly F)) := by
  rw [memoDualJet_eq_source]
  exact GeneralVEWeighted.dualJet_derivative_correct F x

end MemoVECNF
