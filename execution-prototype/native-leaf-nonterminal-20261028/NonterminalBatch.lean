import LinearizedPrefixRunner

/-! Actual original terminal-classifier and leaf-loader stages on FOUR
nonterminal small CNFs. None of the reported oracle counts are computed by
the prefix: the accepted output is the correctly loaded physical leaf bank.
The subsequent noncomputable high-query computation is deliberately NOT run.
-/
namespace IndependentNonterminal
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse

set_option maxRecDepth 19000

/-- x0 and not x1, 2 assignments over three variables. -/
def F2 : RawCNF 3 := [[⟨0,true⟩],[⟨1,false⟩]]
/-- x0 and not x0, no satisfying assignments. -/
def F3 : RawCNF 3 := [[⟨0,true⟩],[⟨0,false⟩]]
/-- Two genuine nonunit 2-clauses. -/
def F4 : RawCNF 3 := [[⟨0,true⟩,⟨1,true⟩],[⟨0,false⟩,⟨2,true⟩]]

def checkOne (name : String) (G : RawCNF 3) : String := Id.run do
  let a := IndependentNativeExec.readyPhysicalState 3 2 2
    (NativeTerminal.clauseRecords G)
  let (c,s) := runCompactFrom (a.withPC (some program.entry)) 6000
  let countOracle := SAT.count (ExecCNF.formulaSet G)
  let copied :=
    c.stackData[1104]! == a.stacks 265 &&
    c.stackData[1105]! == a.stacks 267 &&
    c.stackData[1106]! == a.stacks 264
  return s!"case={name};clauses={G.length};oracleCount={countOracle};halted={s.halted};guard0={c.regs[0]!};guard7={c.regs[7]!};copied={copied};sourceSteps={s.executed};peakTotalBits={s.peakTotalBits};peakSingleStackBits={s.peakSingleStackBits};codeLookups={s.codeCacheMisses}"

#eval checkOne "unit_positive" F
#eval checkOne "two_units" F2
#eval checkOne "contradiction" F3
#eval checkOne "two_binary_clauses" F4

end IndependentNonterminal
