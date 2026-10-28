import ReconstructionDegree

namespace VerifiedReconstruction
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open Polynomial

/-- CONDITIONAL final correctness of the actual OpenAI reconstruction program,
    using our real, verified memoized arbitrary-CNF Hermite jets. All the
    mathematical residue assumptions are explicit, as in OpenAI's own theorem.
    The only constraint on input CNF is F.card < 2*Q (a polynomial degree bound).
    No assumptions of bounded treewidth, connectivity, SAT status, etc. -/
theorem reconstruct_violation_polynomial
    {n m Q : Nat} [NeZero Q] (F : CNF (Fin n))
    (nodes : Fin Q → ZMod m)
    {E : Type*} [Field E] [Fintype E]
    (rho : ZMod m →+* E) (residueSize : Nat)
    (hcard : Fintype.card E = residueSize)
    (pi : ZMod m) (precision : Nat) (hnil : pi ^ precision = 0)
    (hker : ∀ x, rho x = 0 → pi ∣ x)
    (hnodes : Function.Injective (fun i => rho (nodes i)))
    (hdegree : F.card < Q * 2) :
    PolynomialAlgorithm.denote
      ((Reconstruction.run (representedOps m).program nodes residueSize precision 2
        (verifiedJets F nodes)).1.map (representedOps m).decode) =
      GeneralVEWeighted.violationPoly F := by
  apply Reconstruction.run_correct (representedOps m) nodes rho residueSize
    hcard pi precision hnil hker hnodes 2 (by omega)
    (verifiedJets F nodes) (GeneralVEWeighted.violationPoly F)
  · exact (violation_degree_le F).trans_lt hdegree
  · exact verified_hasJets F nodes
  · intro i
    simp [verifiedJets]

/-- The first reconstructed coefficient is the value at zero of the actual
    violation-count polynomial of the input CNF. -/
theorem reconstructed_head_correct
    {n m Q : Nat} [NeZero Q] (F : CNF (Fin n))
    (nodes : Fin Q → ZMod m)
    {E : Type*} [Field E] [Fintype E]
    (rho : ZMod m →+* E) (residueSize : Nat)
    (hcard : Fintype.card E = residueSize)
    (pi : ZMod m) (precision : Nat) (hnil : pi ^ precision = 0)
    (hker : ∀ x, rho x = 0 → pi ∣ x)
    (hnodes : Function.Injective (fun i => rho (nodes i)))
    (hdegree : F.card < Q * 2) :
    (Reconstruction.run (representedOps m).program nodes residueSize precision 2
      (verifiedJets F nodes)).1.headD 0 =
    (GeneralVEWeighted.violationPoly F).eval 0 := by
  have h := Reconstruction.run_head_eq_eval_zero (representedOps m)
    nodes residueSize precision 2 (verifiedJets F nodes)
    (GeneralVEWeighted.violationPoly F)
    (reconstruct_violation_polynomial F nodes rho residueSize hcard pi
      precision hnil hker hnodes hdegree)
  simpa only [representedOps, id_eq] using h

end VerifiedReconstruction
