import GeneralVEExact
import Mathlib.Algebra.DualNumber

namespace GeneralVEWeighted
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SAT

variable {n : Nat} {R : Type*} [CommSemiring R]

/-- One clause contributes 1 if satisfied, and X if violated.
    Here X can be any element of a commutative semiring (e.g. dual numbers). -/
def clauseFactor (C : Clause (Fin n)) (x : R) : GeneralVE.Factor n R where
  scope := C.image Literal.variable
  value := fun a => if C.eval a then 1 else x
  locality := by
    intro a b h
    have forward (a b : Assignment (Fin n))
        (hab : ∀ v ∈ C.image Literal.variable, a v = b v)
        (ha : C.eval a = true) : C.eval b = true := by
      obtain ⟨l,hl,ht⟩ := (Clause.eval_eq_true a C).mp ha
      apply (Clause.eval_eq_true b C).mpr
      refine ⟨l,hl,?_⟩
      have hv : a l.variable = b l.variable :=
        hab l.variable (Finset.mem_image.mpr ⟨l,hl,rfl⟩)
      simpa only [Literal.eval, hv] using ht
    have eq : C.eval a = C.eval b := by
      apply Bool.eq_iff_iff.mpr
      constructor
      · exact forward a b h
      · exact forward b a (fun v hv => (h v hv).symm)
    rw [eq]

def factors (F : CNF (Fin n)) (x : R) :
    List (GeneralVE.Factor n R) :=
  (Prototype.orderedClauses F).map (fun C => clauseFactor C x)

/-- The generic sum-product bucket eliminator for the violation polynomial
    evaluated at x, without ever enumerating all 2^n assignments in a loop. -/
def weightedTotal (F : CNF (Fin n)) (x : R) : R :=
  GeneralVE.product (GeneralVE.run (List.finRange n) (factors F x))
    (fun _ => false)

/-- Full arbitrary-CNF correctness: weightedTotal returns the exact partition
    function, i.e. the sum of X^(number of violated clauses) over all assignments.
    This holds for every possible R, so also for first-order Hermite jets. -/
theorem weightedTotal_correct (F : CNF (Fin n)) (x : R) :
    weightedTotal F x =
      ∑ a : Assignment (Fin n),
        ((Prototype.orderedClauses F).map fun C => if C.eval a then (1:R) else x).prod := by
  unfold weightedTotal
  rw [GeneralVE.run_correct, GeneralVE.marginalMany_finRange]
  apply Fintype.sum_congr
  intro a
  unfold GeneralVE.product factors
  simp only [List.map_map, Function.comp_def]
  rfl

/-- Exact first-order Hermite jet (value, first derivative) in dual numbers,
    computed by the SAME general verified bucket eliminator. -/
def dualJet (F : CNF (Fin n)) {p : Nat} (x : ZMod p) : DualNumber (ZMod p) :=
  weightedTotal F ⟨x,1⟩

theorem dualJet_correct (F : CNF (Fin n)) {p : Nat} (x : ZMod p) :
    dualJet F x =
      ∑ a : Assignment (Fin n),
        ((Prototype.orderedClauses F).map fun C =>
          if C.eval a then (1 : DualNumber (ZMod p)) else (⟨x,1⟩ : DualNumber (ZMod p))).prod :=
  by
    simpa only [dualJet] using
      (weightedTotal_correct (R := DualNumber (ZMod p)) F
        (⟨x,1⟩ : DualNumber (ZMod p)))

end GeneralVEWeighted
