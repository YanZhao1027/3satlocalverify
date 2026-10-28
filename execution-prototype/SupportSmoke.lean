import SupportLeaf

private def sparseClause : OAI.Algorithms.SubexponentialSAT.SAT.Clause (Fin 40) :=
  ([⟨(3 : Fin 40), true⟩, ⟨(19 : Fin 40), false⟩] :
    List (OAI.Algorithms.SubexponentialSAT.SAT.Literal (Fin 40))).toFinset
private def sparseFormula : OAI.Algorithms.SubexponentialSAT.SAT.CNF (Fin 40) :=
  {sparseClause}
#eval Prototype.activeVars sparseFormula |>.card
#eval Prototype.countActive sparseFormula
#eval Prototype.countActive (∅ : OAI.Algorithms.SubexponentialSAT.SAT.CNF (Fin 40))
