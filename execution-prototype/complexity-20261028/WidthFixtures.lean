import MemoComplexity

/-! Honest support-only stress cases. Every scope has exactly three variables,
    all variables occur, and the hypergraph is connected. We do not materialize
    any of the exponential tables; we evaluate their exact lengths only. -/
namespace WidthFixtures
open GeneralVE.Complexity

private def v (n i : Nat) [NeZero n] : Fin n := Fin.ofNat n i

/-- n-2 consecutive 3-clause scopes. Connectivity has path width two. -/
def chainScopes (n : Nat) [NeZero n] : List (Finset (Fin n)) :=
  (List.range (n-2)).map (fun i => ([v n i, v n (i+1), v n (i+2)] : List (Fin n)).toFinset)

/-- n-2 connected 3-clause scopes all involving vertex zero; eliminating
    zero FIRST creates a joint factor across all n variables. -/
def hubScopes (n : Nat) [NeZero n] : List (Finset (Fin n)) :=
  (List.range (n-2)).map (fun i => ([v n 0, v n (i+1), v n (i+2)] : List (Fin n)).toFinset)

def chainWidth (n : Nat) [NeZero n] := maxWidth (List.finRange n) (chainScopes n)
def hubWidth (n : Nat) [NeZero n] := maxWidth (List.finRange n) (hubScopes n)
def hubRows (n : Nat) [NeZero n] := totalRows (List.finRange n) (hubScopes n)
def chainRows (n : Nat) [NeZero n] := totalRows (List.finRange n) (chainScopes n)

#eval [(chainWidth 16), (hubWidth 16), (chainRows 16), (hubRows 16)]
#eval [(chainWidth 32), (hubWidth 32), (chainRows 32), (hubRows 32)]
#eval [(chainWidth 64), (hubWidth 64), (chainRows 64), (hubRows 64)]

/-- The static width computations for an actual 16-variable pair of 3-CNFs
    are decidable in the trusted kernel (without native_decide). -/
theorem chain8_width : chainWidth 8 = 3 := by decide
theorem hub8_width : hubWidth 8 = 8 := by decide

end WidthFixtures
