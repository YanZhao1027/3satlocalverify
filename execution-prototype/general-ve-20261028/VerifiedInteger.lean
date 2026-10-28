import VerifiedComplete
import CRTBridgeProof

namespace VerifiedReconstruction
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open Polynomial

/-- The constant term of the arbitrary-CNF violation polynomial is the
    *modular image* of the exact satisfying-assignment count. -/
theorem violation_at_zero_count {n m : Nat} (F : CNF (Fin n)) :
    (GeneralVEWeighted.violationPoly (p := m) F).eval 0 =
      (SAT.count F : ZMod m) := by
  have hv (a : Assignment (Fin n)) :
      PaperKernel.countViolations (Prototype.orderedClauses F) a = 0 ↔
      F.eval a = true := by
    simpa [Prototype.orderedClauses] using
      (PaperKernel.zeroViolations_iff (Prototype.orderedClauses F) a)
  have heval (a : Assignment (Fin n)) :
      (0 : ZMod m) ^ PaperKernel.countViolations (Prototype.orderedClauses F) a =
        if F.eval a = true then 1 else 0 := by
    by_cases h : F.eval a = true
    · have hk := (hv a).mpr h
      simp [hk,h]
    · have hk : PaperKernel.countViolations (Prototype.orderedClauses F) a ≠ 0 :=
        fun hh => h ((hv a).mp hh)
      cases hcount : PaperKernel.countViolations (Prototype.orderedClauses F) a with
      | zero => contradiction
      | succ k => simp [hcount, h]
  unfold GeneralVEWeighted.violationPoly
  rw [Polynomial.eval_finset_sum]
  simp_rw [Polynomial.eval_X_pow, heval]
  have hnat : SAT.count F =
      ∑ a : Assignment (Fin n), if F.eval a = true then (1 : Nat) else 0 := by
    change (Finset.univ.filter fun a : Assignment (Fin n) => F.eval a = true).card = _
    rw [Finset.card_filter]
  calc
    (∑ a : Assignment (Fin n), if F.eval a = true then (1 : ZMod m) else 0) =
      ((∑ a : Assignment (Fin n), if F.eval a = true then (1 : Nat) else 0) : ZMod m) := by
        simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    _ = (SAT.count F : ZMod m) := by rw [hnat]; simp

/-- The original model count has at most 2^n models. -/
theorem sat_count_le_cube {n : Nat} (F : CNF (Fin n)) :
    SAT.count F ≤ 2 ^ n := by
  change (Finset.univ.filter fun a : Assignment (Fin n) => F.eval a = true).card ≤ _
  exact (Finset.card_le_univ _).trans_eq (by simp [Fintype.card_fun])

/-- For a modulus larger than the entire Boolean cube, the modular image
    uniquely determines the exact integer #SAT count. -/
theorem val_modular_count {n m : Nat} (F : CNF (Fin n))
    (hm : 2 ^ n < m) :
    (SAT.count F : ZMod m).val = SAT.count F := by
  rw [ZMod.val_natCast]
  exact Nat.mod_eq_of_lt ((sat_count_le_cube F).trans_lt hm)

/-- FINAL conditional end-to-end theorem: the actual original OpenAI
    Reconstruction.run, using our *verified* memoized VE-produced Hermite jets,
    recovers the full integer #SAT count, provided the explicitly listed
    algebraic CRT hypotheses and a sufficient residue modulus hold. -/
theorem integer_count_from_verified_CRT
    {n m Q : Nat} [NeZero Q] (F : CNF (Fin n))
    (nodes : Fin Q → ZMod m)
    {E : Type*} [Field E] [Fintype E]
    (rho : ZMod m →+* E) (residueSize : Nat)
    (hcard : Fintype.card E = residueSize)
    (pi : ZMod m) (precision : Nat) (hnil : pi ^ precision = 0)
    (hker : ∀ x, rho x = 0 → pi ∣ x)
    (hnodes : Function.Injective (fun i => rho (nodes i)))
    (hdegree : F.card < Q * 2) (hmod : 2 ^ n < m) :
    ((Reconstruction.run (representedOps m).program nodes residueSize precision 2
      (verifiedJets F nodes)).1.headD 0).val = SAT.count F := by
  rw [reconstructed_head_correct F nodes rho residueSize hcard pi
      precision hnil hker hnodes hdegree]
  rw [violation_at_zero_count]
  exact val_modular_count F hmod

end VerifiedReconstruction
