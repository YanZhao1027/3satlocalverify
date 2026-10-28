import MemoVECNF
import DimacsCore
import HermiteKernel

/-! Runnable completely-Lean SAT -> verified bucket first-jets -> ORIGINAL
    OpenAI Reconstruction.run over ZMod(q^mu) with Hermite order 2.
    The parser is a separate tested but not kernel-verified IO adapter.
    The general sampling theorems are in DualJetProof.lean. -/
namespace GeneralVEDualCLI
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog

/-- Cheap pure scope-only preview of the widest bucket, avoiding any expensive
    factor evaluations. Blocks risky high-treewidth instances before runMemo. -/
private def peakScopeWidth {n : Nat} (F : SAT.CNF (Fin n)) : Nat := Id.run do
  let mut scopes : List (Finset (Fin n)) :=
    (Prototype.orderedClauses F).map (fun C => C.image SAT.Literal.variable)
  let mut peak := 0
  for x in List.finRange n do
    let selected := scopes.filter (fun s => decide (x ∈ s))
    let untouched := scopes.filter (fun s => decide (x ∉ s))
    let joined := selected.foldl (fun acc s => acc ∪ s) (∅ : Finset (Fin n))
    peak := max peak joined.card
    scopes := joined.erase x :: untouched
  return peak
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog

private def runOne (prime precision : Nat) (path : String) : IO Bool := do
  let src ← IO.FS.readFile path
  match SparsePrototype.readDimacs src with
  | .error e =>
    IO.eprintln s!"ERROR {path}: {e}"
    return false
  | .ok parsed =>
    if parsed.nvars > 64 || parsed.declaredClauses > 64 then
      IO.eprintln s!"ERROR {path}: demo cap n<=64,m<=64"
      return false
    match SparsePrototype.encodeFormula parsed.nvars parsed.clauses with
    | .error e =>
      IO.eprintln s!"ERROR {path}: {e}"
      return false
    | .ok F =>
      let peak := peakScopeWidth F
      if peak > 18 then
        IO.eprintln s!"ERROR {path}: predicted bucket width={peak} exceeds safe cap 18"
        return false
      let q := (parsed.declaredClauses+2)/2
      let modulus := prime ^ precision
      if !(decide (Nat.Prime prime)) || prime < q ||
          precision = 0 || modulus ≤ 2 ^ parsed.nvars then
        IO.eprintln s!"ERROR {path}: require prime p>=Q={q}, positive precision and p^precision>2^n"
        return false
      let started ← IO.monoMsNow
      let jets : Fin q → List (ZMod modulus) := fun i =>
        let d := MemoVECNF.memoDualJet F (i.val : ZMod modulus)
        [d.fst, d.snd]
      let reconstructed := Reconstruction.run (PaperKernel.ops modulus)
        (fun i : Fin q => (i.val : ZMod modulus)) prime precision 2 jets
      let coeffs := (reconstructed.1.take (parsed.declaredClauses+1)).map ZMod.val
      let answer : Nat := (reconstructed.1.headD 0).val
      let valCheck := PaperKernel.evalPolynomial modulus coeffs (q : ZMod modulus)
      let independentEval := (MemoVECNF.memoDualJet F (q : ZMod modulus)).fst
      let oracleRun := parsed.nvars ≤ 12
      let oracle := if oracleRun then SAT.count F else answer
      let ok := answer == oracle && valCheck == independentEval &&
        coeffs.length == parsed.declaredClauses+1
      IO.println s!"DUAL_FILE {path} n={parsed.nvars} m={parsed.declaredClauses} peakWidth={peak} prime={prime} precision={precision} nodes={q} count={answer} coeffs={coeffs} scalarCallbacks={reconstructed.2} extraValue={valCheck.val} oracle={if oracleRun then toString oracle else "SKIPPED"} result={if ok then "PASS" else "FAIL"}"
      let finished ← IO.monoMsNow
      IO.println s!"DUAL_TIME {path} ms={finished-started}"
      return ok
end GeneralVEDualCLI

def main (args : List String) : IO UInt32 := do
  match args with
  | p :: m :: files =>
      if files.isEmpty then
        IO.eprintln "Usage: lean --run GeneralVEDualDimacs.lean prime precision formula.cnf ..."
        return 2
      let some prime := p.toNat? | return 2
      let some precision := m.toNat? | return 2
      let mut success := true
      for file in files do
        if !(← GeneralVEDualCLI.runOne prime precision file) then success := false
      return if success then 0 else 1
  | _ =>
      IO.eprintln "Usage: lean --run GeneralVEDualDimacs.lean prime precision formula.cnf ..."
      return 2
