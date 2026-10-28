import LinearizedCompiler

/-! Independent compact ARRAY implementation of upstream BitProgram.execInstr
    for executable prefix probing. It uses EXACT original `program.code` for
    each visited program-counter label, memoized by label; it does not precompute
    the original high-query suffix or inject a #SAT result.

    While arrays accelerate simulation, this is not itself a formal compiler
    refinement certificate yet: source step consistency must be checked
    separately before attributing a result to the original program. -/
namespace IndependentNonterminal
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.BitProgram

abbrev L := StructuredCalls.size commonPrefix + 1
abbrev Instructions := Instr 80 1220 L

structure CompactCfg where
  pc : Option (Fin L)
  regs : Array Bool
  stackData : Array (List Bool)
  deriving Inhabited

def compactOf (c : Cfg 80 1220 L) : CompactCfg :=
  { pc := c.pc, regs := Array.ofFn c.regs, stackData := Array.ofFn c.stacks }

def executeCompact (instr : Instructions) (c : CompactCfg) : CompactCfg :=
  match instr with
  | .halt => {c with pc := none}
  | .goto next => {c with pc := some next}
  | .set dst value next =>
    {c with pc := some next, regs := c.regs.set! dst.val value}
  | .copy dst src next =>
    {c with pc := some next, regs := c.regs.set! dst.val (c.regs[src.val]!)}
  | .bnot dst src next =>
    {c with pc := some next, regs := c.regs.set! dst.val (!(c.regs[src.val]!))}
  | .band dst x y next =>
    {c with pc := some next, regs := c.regs.set! dst.val ((c.regs[x.val]!) && (c.regs[y.val]!))}
  | .bor dst x y next =>
    {c with pc := some next, regs := c.regs.set! dst.val ((c.regs[x.val]!) || (c.regs[y.val]!))}
  | .bxor dst x y next =>
    {c with pc := some next, regs := c.regs.set! dst.val ((c.regs[x.val]!) ^^ (c.regs[y.val]!))}
  | .branch test yes no =>
    {c with pc := some (if c.regs[test.val]! then yes else no)}
  | .push stack src next =>
    {c with pc := some next, stackData := c.stackData.set! stack.val ((c.regs[src.val]!) :: (c.stackData[stack.val]!))}
  | .peek stack value present next =>
    let top := (c.stackData[stack.val]!).head?
    let newReg := (c.regs.set! value.val (top.getD false)).set! present.val top.isSome
    {c with pc := some next, regs := newReg}
  | .pop stack value present next =>
    let top := (c.stackData[stack.val]!).head?
    let newReg := (c.regs.set! value.val (top.getD false)).set! present.val top.isSome
    {pc := some next, regs := newReg, stackData := c.stackData.set! stack.val (c.stackData[stack.val]!).tail}

structure RunStats where
  executed : Nat := 0
  codeCacheMisses : Nat := 0
  peakTotalBits : Nat := 0
  peakSingleStackBits : Nat := 0
  halted : Bool := false
  deriving Repr

/-- Instrument per-step source opcodes from the dense array linearization,
subject to the separate per-label differential check against program.code. -/
def runCompactFrom
    (initial : Cfg 80 1220 L) (fuel : Nat) : CompactCfg × RunStats := Id.run do
  let mut c := compactOf initial
  let initialTotal := c.stackData.foldl (fun total s => total + s.length) 0
  let initialMax := c.stackData.foldl (fun m s => max m s.length) 0
  let mut stats : RunStats := {peakTotalBits := initialTotal, peakSingleStackBits := initialMax}
  let mut cache : Std.HashMap Nat Instructions := {}
  let mut total := initialTotal
  for _ in [:fuel] do
    let some p := c.pc | break
    let instr ← match cache[p.val]? with
      | some instr => pure instr
      | none => do
        let instr := (fastArray[p.val]?).getD .halt
        cache := cache.insert p.val instr
        stats := {stats with codeCacheMisses := stats.codeCacheMisses + 1}
        pure instr
    let old := c
    c := executeCompact instr c
    stats := {stats with executed := stats.executed + 1}
    match instr with
    | .push stack _ _ =>
      total := total + 1
      stats := {stats with peakSingleStackBits := max stats.peakSingleStackBits ((old.stackData[stack.val]!).length + 1)}
    | .pop stack _ _ _ =>
      if !(old.stackData[stack.val]!).isEmpty then total := total - 1
    | _ => pure ()
    stats := {stats with peakTotalBits := max stats.peakTotalBits total}
  return (c, {stats with halted := c.pc.isNone})

def runCompact (fuel : Nat) : CompactCfg × RunStats :=
  runCompactFrom (physical.withPC (some program.entry)) fuel

def summary (fuel : Nat) : String := Id.run do
  let (c, s) := runCompact fuel
  let actualTotal := c.stackData.foldl (fun tot stack => tot + stack.length) 0
  return s!"fuel={fuel};steps={s.executed};halted={s.halted};cache_misses={s.codeCacheMisses};guard0={c.regs[0]!};guard7={c.regs[7]!};copiedBody={c.stackData[1104]! == physical.stacks 265};copiedN={c.stackData[1105]! == physical.stacks 267};copiedOccurrence={c.stackData[1106]! == physical.stacks 264};scratchEmpty={(c.stackData[1219]!).isEmpty};resultWord={(c.stackData[263]!).length};peakTotal={s.peakTotalBits};peakSingle={s.peakSingleStackBits};finalTotal={actualTotal}"

end IndependentNonterminal
