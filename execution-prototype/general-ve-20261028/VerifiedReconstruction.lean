import MemoVECNF
import OAI.Algorithms.SubexponentialSAT.SqrtLog.Reconstruction

namespace VerifiedReconstruction
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open Polynomial

/-- A minimal faithful representation of ordinary ring operations in ZMod m.
    OpenAI's reconstruction theorem requires such an explicit represented ring,
    not merely its executable RingProgram. -/
def representedOps (m : Nat) :
    SubexpSymbolicCost.RepresentedRing (ZMod m) (ZMod m) where
  decode := id
  zeroRun := (0,1)
  oneRun := (1,1)
  addRun := fun a b => (a+b,1)
  mulRun := fun a b => (a*b,1)
  negRun := fun a => (-a,1)
  zero_correct := rfl
  one_correct := rfl
  add_correct := by intros; rfl
  mul_correct := by intros; rfl
  neg_correct := by intros; rfl

/-- A mathematically verified jet evaluator. The two coordinates are the
    original (memoized) generalized CNF variable-elimination computations. -/
def verifiedJets {n m Q : Nat} (F : CNF (Fin n))
    (nodes : Fin Q → ZMod m) : Fin Q → List (ZMod m) :=
  fun i =>
    let d := MemoVECNF.memoDualJet F (nodes i)
    [d.fst,d.snd]

/-- The missing bridge between our generic CNF VE proof and the original
    OpenAI Reconstruction.HasJets interface. Both order-two Taylor coefficients
    are certified for every CNF, at every node, over every modular ring. -/
theorem verified_hasJets {n m Q : Nat} (F : CNF (Fin n))
    (nodes : Fin Q → ZMod m) :
    Reconstruction.HasJets (representedOps m) nodes 2 (verifiedJets F nodes)
      (GeneralVEWeighted.violationPoly F) := by
  apply Reconstruction.hasJets_of_coefficients
  intro i k hk
  have h : k = 0 ∨ k = 1 := by omega
  rcases h with rfl | rfl
  · simp only [PolynomialAlgorithm.coeff_denote, PolynomialAlgorithm.coeff,
      representedOps, verifiedJets]
    rw [← Polynomial.taylor_apply, Polynomial.taylor_coeff_zero]
    exact MemoVECNF.memoDualJet_value_correct F (nodes i)
  · simp only [PolynomialAlgorithm.coeff_denote, PolynomialAlgorithm.coeff,
      representedOps, verifiedJets]
    rw [← Polynomial.taylor_apply, Polynomial.taylor_coeff_one]
    exact MemoVECNF.memoDualJet_derivative_correct F (nodes i)

end VerifiedReconstruction
