import PrimePowerKernel

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SAT

namespace PaperKernel.PrimePowerCLI

def runOne (path : String) : IO Bool := do
  let src ← IO.FS.readFile path
  match SparsePrototype.readDimacs src with
  | .error msg =>
    IO.eprintln s!"ERROR {path}: {msg}"
    return false
  | .ok inp =>
    if inp.nvars > 11 || inp.declaredClauses > 5 then
      IO.eprintln s!"ERROR {path}: limits n<=11,m<=5 (prime-power demonstration)"
      return false
    match SparsePrototype.encodeFormula inp.nvars inp.clauses with
    | .error msg =>
      IO.eprintln s!"ERROR {path}: {msg}"
      return false
    | .ok F =>
      let hist := polynomialCoefficients (Prototype.orderedClauses F)
      let oracle := SAT.count F
      IO.println s!"HISTP {path} n={inp.nvars} m={inp.declaredClauses} count={oracle} histogram={hist}"
      let mut allOK := true
      for D in [1,2,3] do
        let Q := 6 / D
        let t0 ← IO.monoMsNow
        let a := reconstructPrimePower hist Q D
        let b := reconstructHermite 11 hist Q D
        let c := reconstructHermite 13 hist Q D
        let aa := (a.1.take 6).map ZMod.val
        let bb := (b.1.take 6).map ZMod.val
        let cc := (c.1.take 6).map ZMod.val
        let result := recover49_11_13 ((a.1.headD 0).val)
          ((b.1.headD 0).val) ((c.1.headD 0).val)
        let pass := aa == hist.map (· % 49) && bb == hist.map (· % 11) &&
                    cc == hist.map (· % 13) && result == oracle && result == hist.headD 0
        IO.println s!"PRIME_FILE {path} order={D} nodes={Q} count={result} costs={[a.2,b.2,c.2]} result={if pass then "PASS" else "FAIL"}"
        let t1 ← IO.monoMsNow
        IO.println s!"PRIME_TIMING {path} order={D} ms={t1-t0}"
        if !pass then allOK := false
      return allOK

end PaperKernel.PrimePowerCLI

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "Usage: lean --run PrimePowerDimacs.lean file.cnf ... (n<=11,m<=5)"
    return 2
  let mut allOK := true
  for path in args do
    if !(← PaperKernel.PrimePowerCLI.runOne path) then allOK := false
  return if allOK then 0 else 1
