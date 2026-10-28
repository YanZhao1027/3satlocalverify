import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse

namespace SparsePrototype

structure RawInput where
  nvars : Nat
  declaredClauses : Nat
  clauses : List (List Int)

structure Stats where
  steps : Nat := 0
  branches : Nat := 0
  leaves : Nat := 0
  maxPending : Nat := 0
  deriving Repr

def words (line : String) : List String :=
  ((line.replace "\t" " ").splitOn " ").filter (· != "")

def readDimacs (s : String) : Except String RawInput := do
  let mut hdr : Option (Nat × Nat) := none
  let mut clauses : Array (List Int) := #[]
  let mut current : List Int := []
  for line in s.splitOn "\n" do
    let clean := line.trimAscii.toString
    if clean.isEmpty || clean.startsWith "c" || clean.startsWith "%" then
      continue
    let tokens := words clean
    if clean.startsWith "p " then
      match tokens with
      | ["p", "cnf", ns, ms] =>
        if hdr.isSome then throw "duplicate p cnf header"
        match ns.toNat?, ms.toNat? with
        | some n, some m => hdr := some (n, m)
        | _, _ => throw "non-numeric DIMACS header"
      | _ => throw "expected: p cnf <nvars> <clauses>"
    else
      if hdr.isNone then throw "DIMACS clauses appeared before p cnf header"
      for w in tokens do
        match w.toInt? with
        | none => throw s!"invalid integer token: {w}"
        | some v =>
          if v == 0 then
            clauses := clauses.push current.reverse
            current := []
          else
            current := v :: current
  if !current.isEmpty then throw "unterminated clause (missing 0)"
  match hdr with
  | none => throw "missing p cnf header"
  | some (n, declared) =>
    if declared != clauses.size then throw s!"header declares {declared} clauses but found {clauses.size}"
    pure ⟨n, declared, clauses.toList⟩

def encodeFormula (n : Nat) (clauses : List (List Int)) :
    Except String (CNF (Fin n)) := do
  let mut out : List (Clause (Fin n)) := []
  for c in clauses do
    let mut literals : List (Literal (Fin n)) := []
    for v in c do
      let abs := v.natAbs
      if abs == 0 then throw "zero is only a clause terminator"
      if h : abs - 1 < n then
        literals := ⟨⟨abs - 1, h⟩, decide (v > 0)⟩ :: literals
      else
        throw s!"literal {v} outside declared variable range 1..{n}"
    out := literals.toFinset :: out
  pure out.toFinset


end SparsePrototype
