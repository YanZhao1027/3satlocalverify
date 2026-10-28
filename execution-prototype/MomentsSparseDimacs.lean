import MomentsSAT

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
  momentsOps : Nat := 0
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

-- Certified refinement of OpenAI SparseCountProgram.step.
-- Its leaf calls the original MomentsAlgorithm.run, with a proved exponential cost.
def solve {n : Nat} (threshold budget : Nat) (F : CNF (Fin n)) :
    Except String (Nat × Stats) := Id.run do
  let mut state := SparseCountProgram.initial F
  let mut stats : Stats := {maxPending := state.pending.length}
  for _ in [:budget] do
    match state.pending with
    | [] => break
    | node :: _ =>
      let branch := (SparsePriority.select node.formula threshold).isSome
      let charged := if branch then 0 else (2 ^ n) * (3 * node.formula.card + 2)
      state := Prototype.sparseMomentsStep threshold state
      stats := ⟨stats.steps + 1, stats.branches + (if branch then 1 else 0),
        stats.leaves + (if branch then 0 else 1),
        max stats.maxPending state.pending.length, stats.momentsOps + charged⟩
  if !state.pending.isEmpty then
    return .error s!"fuel exhausted after {budget} transitions; {state.pending.length} pending"
  return .ok (state.total, stats)

def runOne (path : String) : IO Bool := do
  let s ← IO.FS.readFile path
  match readDimacs s with
  | .error message =>
    IO.eprintln s!"ERROR {path}: {message}"
    pure false
  | .ok raw =>
    if raw.nvars > 12 then
      IO.eprintln s!"ERROR {path}: n={raw.nvars} exceeds safety cap 12 (exhaustive Moments leaves)"
      return false
    match encodeFormula raw.nvars raw.clauses with
    | .error message =>
      IO.eprintln s!"ERROR {path}: {message}"
      pure false
    | .ok cnf =>
      let start ← IO.monoMsNow
      let output := solve 2 100000 cnf
      match output with
      | .error message =>
        IO.eprintln s!"ERROR {path}: {message}"
        pure false
      | .ok (answer, stats) =>
        let elapsed := (← IO.monoMsNow) - start
        let check := SAT.count cnf
        let ok := answer == check
        IO.println s!"MOMENTS_FILE {path} n={raw.nvars} m={raw.declaredClauses} count={answer} reference={check} steps={stats.steps} branches={stats.branches} leaves={stats.leaves} maxPending={stats.maxPending} ops={stats.momentsOps} ms={elapsed} result={if ok then "PASS" else "FAIL"}"
        pure ok

end SparsePrototype

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    IO.eprintln "usage: lean --run SparseDimacs.lean file1.cnf [file2.cnf ...]"
    pure 2
  | files =>
    let mut ok := true
    for path in files do
      if !(← SparsePrototype.runOne path) then ok := false
    pure (if ok then 0 else 1)
