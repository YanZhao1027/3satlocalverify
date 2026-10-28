import VerifiedInteger

namespace VerifiedReconstruction
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog

private instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- Actual residue homomorphism Z/(7^2) -> F_7. -/
def residue49 : ZMod 49 →+* ZMod 7 :=
  ZMod.castHom (by norm_num : 7 ∣ 49) (ZMod 7)

theorem residue49_ker (x : ZMod 49) (h : residue49 x = 0) :
    (7 : ZMod 49) ∣ x := by
  have hv : (x.val : ZMod 7) = 0 := by
    simpa [residue49, ZMod.castHom_apply] using h
  have hd : 7 ∣ x.val := (ZMod.natCast_eq_zero_iff x.val 7).mp hv
  obtain ⟨k,hk⟩ := hd
  refine ⟨(k : ZMod 49), ?_⟩
  calc
    x = (x.val : ZMod 49) := (ZMod.natCast_zmod_val x).symm
    _ = (7 : ZMod 49) * (k : ZMod 49) := by
      rw [hk]
      push_cast
      rfl

theorem residue49_nodes (Q : Nat) (hQ : Q ≤ 7) :
    Function.Injective (fun i : Fin Q => residue49 (i.val : ZMod 49)) := by
  intro i j h
  have hv := congrArg ZMod.val h
  simp only [residue49, map_natCast, ZMod.val_natCast] at hv
  have hi : i.val < 7 := lt_of_lt_of_le i.isLt hQ
  have hj : j.val < 7 := lt_of_lt_of_le j.isLt hQ
  simp only [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hv
  exact Fin.ext hv

theorem residue49_nilpotent : (7 : ZMod 49) ^ 2 = 0 := by decide

/-- A concrete paper-style theorem for modulus 49 and a first-derivative jet.
    No residue assumptions remain: they are all proved above. -/
theorem concrete49_count {n Q : Nat} [NeZero Q]
    (F : CNF (Fin n)) (hdegree : F.card < Q * 2)
    (hQ : Q ≤ 7) (hmod : 2 ^ n < 49) :
    ((Reconstruction.run (representedOps 49).program
      (fun i : Fin Q => (i.val : ZMod 49)) 7 2 2
      (verifiedJets F (fun i : Fin Q => (i.val : ZMod 49)))).1.headD 0).val =
      SAT.count F := by
  exact integer_count_from_verified_CRT F
    (fun i : Fin Q => (i.val : ZMod 49))
    residue49 7 (by exact ZMod.card 7) (7 : ZMod 49) 2
    residue49_nilpotent residue49_ker
    (residue49_nodes Q hQ) hdegree hmod

end VerifiedReconstruction
