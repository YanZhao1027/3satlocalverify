import HermiteKernel

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SAT

namespace PaperKernel.HermiteCLI

def runOne (path : String) : IO Bool := do
  let src ← IO.FS.readFile path
  match SparsePrototype.readDimacs src with
  | .error message =>
    IO.eprintln s!"ERROR {path}: {message}"
    return false
  | .ok input =>
    if input.nvars > 9 || input.declaredClauses > 5 then
      IO.eprintln s!"ERROR {path}: only n<=9 and m<=5 permitted"
      return false
    match SparsePrototype.encodeFormula input.nvars input.clauses with
    | .error message =>
      IO.eprintln s!"ERROR {path}: {message}"
      return false
    | .ok F =>
      let hist := polynomialCoefficients (Prototype.orderedClauses F)
      let oracle := SAT.count F
      IO.println s!"HIST {path} n={input.nvars} m={input.declaredClauses} count={oracle} histogram={hist}"
      let mut allPassed := true
      for D in [1,2,3] do
        let Q := 6 / D
        let started ← IO.monoMsNow
        let a := reconstructHermite 7 hist Q D
        let b := reconstructHermite 11 hist Q D
        let c := reconstructHermite 13 hist Q D
        let aa := (a.1.take 6).map ZMod.val
        let bb := (b.1.take 6).map ZMod.val
        let cc := (c.1.take 6).map ZMod.val
        let exact : Nat := ((a.1.headD 0).val*715 +
                           (b.1.headD 0).val*364 +
                           (c.1.headD 0).val*924) % 1001
        let passed := aa == hist.map (· % 7) &&
                      bb == hist.map (· % 11) &&
                      cc == hist.map (· % 13) &&
                      exact == oracle && exact == hist.headD 0
        IO.println s!"HERMITE_FILE {path} order={D} nodes={Q} count={exact} costs={[a.2,b.2,c.2]} result={if passed then "PASS" else "FAIL"}"
        let ended ← IO.monoMsNow
        IO.println s!"HERMITE_TIMING {path} order={D} ms={ended-started}"
        if !passed then allPassed := false
      return allPassed

end PaperKernel.HermiteCLI

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "Usage: lean --run HermiteDimacs.lean file1.cnf [...] (n<=9,m<=5)"
    return 2
  let mut pass := true
  for path in args do
    if !(← PaperKernel.HermiteCLI.runOne path) then pass := false
  return if pass then 0 else 1
