import GeneralVEWeighted
import CRTKernel

namespace GeneralVEWeighted
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SAT
open Polynomial

variable {n : Nat} {R : Type*} [CommSemiring R]

/-- Product of a list of satisfied=1, violated=x clause weights is exactly
    x raised to the number of violated clauses, for any commutative semiring. -/
private theorem product_pow_violations (cs : List (Clause (Fin n)))
    (a : Assignment (Fin n)) (x : R) :
    (cs.map (fun C => if C.eval a then (1 : R) else x)).prod =
    x ^ PaperKernel.countViolations cs a := by
  induction cs with
  | nil => simp [PaperKernel.countViolations]
  | cons C cs ih =>
      by_cases h : C.eval a = true
      · have hcount : PaperKernel.countViolations (C :: cs) a =
            PaperKernel.countViolations cs a := by
          simp [PaperKernel.countViolations, h]
        simp only [List.map_cons, List.prod_cons]
        rw [if_pos h, one_mul, ih, hcount]
      · have hf : C.eval a = false := by
          cases hv : C.eval a <;> simp_all
        have hcount : PaperKernel.countViolations (C :: cs) a =
            PaperKernel.countViolations cs a + 1 := by
          simp [PaperKernel.countViolations, hf]
        simp only [List.map_cons, List.prod_cons]
        rw [if_neg h, ih, hcount, pow_succ]
        ring

/-- Fully verified weighted count = evaluation of the violation generating
    polynomial at x. The numerical code is the verified sparse bucket VE. -/
theorem weightedTotal_as_pow (F : CNF (Fin n)) (x : R) :
    weightedTotal F x =
    ∑ a : Assignment (Fin n),
      x ^ PaperKernel.countViolations (Prototype.orderedClauses F) a := by
  rw [weightedTotal_correct]
  apply Fintype.sum_congr
  intro a
  exact product_pow_violations (Prototype.orderedClauses F) a x

/-- Mathematical violation polynomial. The computational algorithm avoids
    constructing this enormous sum and instead evaluates its jets directly. -/
noncomputable def violationPoly {p : Nat} (F : CNF (Fin n)) : Polynomial (ZMod p) :=
  ∑ a : Assignment (Fin n),
    (Polynomial.X : Polynomial (ZMod p)) ^
      PaperKernel.countViolations (Prototype.orderedClauses F) a

/-- Enforce the dual-number multiplication, not the ordinary coordinatewise
    product-ring instance on the underlying pair representation. -/
private def dualNode {p : Nat} (x : ZMod p) : DualNumber (ZMod p) :=
  ⟨x,1⟩

private theorem dualJet_as_pow (F : CNF (Fin n)) {p : Nat} (x : ZMod p) :
    dualJet F x =
      ∑ a : Assignment (Fin n),
        (dualNode x) ^
          PaperKernel.countViolations (Prototype.orderedClauses F) a := by
  change weightedTotal F (dualNode x) = _
  exact weightedTotal_as_pow (R := DualNumber (ZMod p)) F (dualNode x)

/-- For EVERY CNF and every modular node x, the first component of the
    computed dual-number result is the true violation polynomial's value. -/
theorem dualJet_value_correct (F : CNF (Fin n)) {p : Nat} (x : ZMod p) :
    (dualJet F x).fst = Polynomial.eval x (violationPoly F) := by
  rw [dualJet_as_pow]
  rw [TrivSqZeroExt.fst_sum]
  unfold violationPoly
  rw [Polynomial.eval_finset_sum]
  apply Fintype.sum_congr
  intro a
  simp only [TrivSqZeroExt.fst_pow, Polynomial.eval_X_pow]
  rfl

/-- For EVERY CNF and every modular node x, the second dual-number component
    is the DERIVATIVE of the true violation polynomial, without computing the
    exponential-size histogram. Thus the pair is a certified Hermite jet. -/
theorem dualJet_derivative_correct (F : CNF (Fin n)) {p : Nat} (x : ZMod p) :
    (dualJet F x).snd = Polynomial.eval x (Polynomial.derivative (violationPoly F)) := by
  rw [dualJet_as_pow]
  rw [TrivSqZeroExt.snd_sum]
  unfold violationPoly
  rw [Polynomial.derivative_sum, Polynomial.eval_finset_sum]
  apply Fintype.sum_congr
  intro a
  simp only [TrivSqZeroExt.snd_pow, Polynomial.derivative_X_pow,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X_pow]
  simp only [Nat.pred_eq_sub_one, nsmul_eq_mul, smul_eq_mul]
  simp [dualNode]

end GeneralVEWeighted
