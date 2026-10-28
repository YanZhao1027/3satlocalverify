import VerifiedInteger

namespace VerifiedReconstruction
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog

private instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- Actual residue homomorphism Z/(7^2) -> F_7. -/
def residue2401 : ZMod 2401 →+* ZMod 7 :=
  ZMod.castHom (by norm_num : 7 ∣ 2401) (ZMod 7)

theorem residue2401_ker (x : ZMod 2401) (h : residue2401 x = 0) :
    (7 : ZMod 2401) ∣ x := by
  have hv : (x.val : ZMod 7) = 0 := by
    simpa [residue2401, ZMod.castHom_apply] using h
  have hd : 7 ∣ x.val := (ZMod.natCast_eq_zero_iff x.val 7).mp hv
  obtain ⟨k,hk⟩ := hd
  refine ⟨(k : ZMod 2401), ?_⟩
  calc
    x = (x.val : ZMod 2401) := (ZMod.natCast_zmod_val x).symm
    _ = (7 : ZMod 2401) * (k : ZMod 2401) := by
      rw [hk]
      push_cast
      rfl

theorem residue2401_nodes (Q : Nat) (hQ : Q ≤ 7) :
    Function.Injective (fun i : Fin Q => residue2401 (i.val : ZMod 2401)) := by
  intro i j h
  have hv := congrArg ZMod.val h
  simp only [residue2401, map_natCast, ZMod.val_natCast] at hv
  have hi : i.val < 7 := lt_of_lt_of_le i.isLt hQ
  have hj : j.val < 7 := lt_of_lt_of_le j.isLt hQ
  simp only [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hv
  exact Fin.ext hv

theorem residue2401_nilpotent : (7 : ZMod 2401) ^ 4 = 0 := by decide

/-- A concrete paper-style theorem for modulus 2401 and a first-derivative jet.
    No residue assumptions remain: they are all proved above. -/
theorem concrete2401_count {n Q : Nat} [NeZero Q]
    (F : CNF (Fin n)) (hdegree : F.card < Q * 2)
    (hQ : Q ≤ 7) (hmod : 2 ^ n < 2401) :
    ((Reconstruction.run (representedOps 2401).program
      (fun i : Fin Q => (i.val : ZMod 2401)) 7 4 2
      (verifiedJets F (fun i : Fin Q => (i.val : ZMod 2401)))).1.headD 0).val =
      SAT.count F := by
  exact integer_count_from_verified_CRT F
    (fun i : Fin Q => (i.val : ZMod 2401))
    residue2401 7 (by exact ZMod.card 7) (7 : ZMod 2401) 4
    residue2401_nilpotent residue2401_ker
    (residue2401_nodes Q hQ) hdegree hmod

end VerifiedReconstruction

