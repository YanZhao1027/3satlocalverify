import GeneralVE
import MomentsSAT

namespace GeneralVESAT
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SAT

/-- Formally certified support-local factor for a single arbitrary SAT clause. -/
def clauseFactor {n : Nat} (C : Clause (Fin n)) : GeneralVE.Factor n Nat where
  scope := C.image Literal.variable
  value := fun a => (C.eval a).toNat
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

/-- The initial bucket factors faithfully encode the original CNF. -/
def factors {n : Nat} (F : CNF (Fin n)) :
    List (GeneralVE.Factor n Nat) := (Prototype.orderedClauses F).map clauseFactor

private theorem product_bool_list {n : Nat} (cs : List (Clause (Fin n)))
    (a : Assignment (Fin n)) :
    (cs.map fun C => (C.eval a).toNat).prod =
      (decide (∀ C ∈ cs, C.eval a = true)).toNat := by
  induction cs with
  | nil => simp
  | cons C cs ih =>
      simp only [List.map_cons, List.prod_cons, List.forall_mem_cons]
      rw [ih]
      cases h : C.eval a <;> simp [h]

/-- The product of arbitrary CNF clause factors equals the truth indicator.
    This is a general theorem for all finite CNFs, including empty clauses,
    contradictions, free variables and all fixed widths k. -/
theorem product_factors_eq_eval {n : Nat} (F : CNF (Fin n))
    (a : Assignment (Fin n)) :
    GeneralVE.product (factors F) a = (F.eval a).toNat := by
  unfold GeneralVE.product factors
  simp only [List.map_map, Function.comp_def]
  change ((Prototype.orderedClauses F).map (fun C => (C.eval a).toNat)).prod =
    (F.eval a).toNat
  rw [product_bool_list]
  simp [CNF.eval, Prototype.orderedClauses]

/-- The fully generic verified bucket algorithm on actual SAT clauses. -/
def runFactors {n : Nat} (F : CNF (Fin n)) :
    List (GeneralVE.Factor n Nat) :=
  GeneralVE.run (List.finRange n) (factors F)

/-- The bucket result equals successive exact marginalization of the
    SAT truth indicator. This holds for every CNF, not just low-treewidth. -/
theorem runFactors_correct {n : Nat} (F : CNF (Fin n))
    (a : Assignment (Fin n)) :
    GeneralVE.product (runFactors F) a =
      GeneralVE.marginalMany (List.finRange n) (fun b => (F.eval b).toNat) a := by
  rw [runFactors, GeneralVE.run_correct]
  have heq : GeneralVE.product (factors F) = (fun b => (F.eval b).toNat) := by
    funext b
    exact product_factors_eq_eval F b
  rw [heq]

end GeneralVESAT
