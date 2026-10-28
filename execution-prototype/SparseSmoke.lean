import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse

private def literal (v : Fin 3) (positive : Bool) : Literal (Fin 3) := ⟨v, positive⟩
private def clause (lits : List (Literal (Fin 3))) : Clause (Fin 3) := lits.toFinset
private def sampleCNF : CNF (Fin 3) :=
  ([clause [literal 0 true, literal 1 true],
    clause [literal 0 true, literal 2 true],
    clause [literal 0 true, literal 1 false],
    clause [literal 0 false, literal 2 true]] : List (Clause (Fin 3))).toFinset

#eval SAT.count sampleCNF
#eval (SparsePriority.select sampleCNF 2).isSome
#eval (SparseCountProgram.run 2 16 (SparseCountProgram.initial sampleCNF)).pending.length
#eval (SparseCountProgram.run 2 16 (SparseCountProgram.initial sampleCNF)).total
#eval (SparseCountProgram.run 2 16 (SparseCountProgram.initial sampleCNF)).total == SAT.count sampleCNF
