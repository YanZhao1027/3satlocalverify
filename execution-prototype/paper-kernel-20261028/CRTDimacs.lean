import CRTKernel

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SAT

namespace PaperKernel.CLI

def runOne (path : String) : IO Bool := do
  let src ← IO.FS.readFile path
  match SparsePrototype.readDimacs src with
  | .error message =>
    IO.eprintln s!"ERROR {path}: {message}"
    return false
  | .ok input =>
    if input.nvars > 9 || input.declaredClauses > 5 then
      IO.eprintln s!"ERROR {path}: maximum n=9 and m=5 for small, exhaustive experimental CRT"
      return false
    match SparsePrototype.encodeFormula input.nvars input.clauses with
    | .error message =>
      IO.eprintln s!"ERROR {path}: {message}"
      return false
    | .ok F =>
      let beforeOracle ← IO.monoMsNow
      let exactOracle := SAT.count F
      IO.println s!"ORACLE {path} count={exactOracle}"
      let afterOracle ← IO.monoMsNow
      let cs := Prototype.orderedClauses F
      let hist := polynomialCoefficients cs
      let r7 := reconstruct 7 hist
      let r11 := reconstruct 11 hist
      let r13 := reconstruct 13 hist
      let residue7 := (r7.1.take 6).map ZMod.val
      let residue11 := (r11.1.take 6).map ZMod.val
      let residue13 := (r13.1.take 6).map ZMod.val
      let answer : Nat := ((r7.1.headD 0).val*715 + (r11.1.headD 0).val*364 +
                           (r13.1.headD 0).val*924) % 1001
      let w0 := walshCoefficient F 0
      let wUnits := (List.finRange input.nvars).map (fun i => walshCoefficient F (unitMask i))
      let coeffCheck := residue7 == hist.map (· % 7) &&
                        residue11 == hist.map (· % 11) &&
                        residue13 == hist.map (· % 13)
      let passed := coeffCheck && answer == exactOracle &&
                    hist.headD 0 == answer && w0 == (answer : Int)
      IO.println s!"CRT_FILE {path} n={input.nvars} m={input.declaredClauses} count={answer} hist={hist} mod7={residue7} mod11={residue11} mod13={residue13} costs={[r7.2,r11.2,r13.2]} walsh0={w0} walshUnits={wUnits} result={if passed then "PASS" else "FAIL"}"
      let afterCRT ← IO.monoMsNow
      IO.println s!"TIMING {path} oracle_ms={afterOracle-beforeOracle} crt_and_walsh_ms={afterCRT-afterOracle}"
      return passed

end PaperKernel.CLI

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "Usage: lean --run CRTDimacs.lean file1.cnf [file2.cnf ...] (n<=9,m<=5)"
    return 2
  let mut passed := true
  for path in args do
    if !(← PaperKernel.CLI.runOne path) then passed := false
  return if passed then 0 else 1
