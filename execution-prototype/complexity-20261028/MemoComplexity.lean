import MemoVE

/-! A non-asymptotic work/memory model for the ACTUAL source-level memoized
    variable eliminator. We count materialized factor rows only, not runtime
    bit operations, table lookups, or ring arithmetic. All claims are exact
    combinatorial counts or explicit upper bounds. -/
namespace GeneralVE.Complexity

variable {n : Nat} {R : Type*} [CommSemiring R]

/-- Every recursive call of sampleSupport doubles its number of rows. -/
theorem sampleSupport_length (xs : List (Fin n)) :
    (sampleSupport xs).length = 2 ^ xs.length := by
  induction xs with
  | nil => simp [sampleSupport]
  | cons x xs ih =>
      simp [sampleSupport, ih, pow_succ, Nat.mul_comm]

/-- Exact number of source-level rows materialized by memo for each factor. -/
theorem makeTable_length (f : Factor n R) :
    (makeTable f).length = 2 ^ f.scope.card := by
  simp [makeTable, sampleSupport_length]

/-- Scope-only version of the source bucket. This can be profiled cheaply
    without evaluating an expensive factor. -/
def bucketScopes (x : Fin n) :
    List (Finset (Fin n)) → List (Finset (Fin n)) × Finset (Fin n)
  | [] => ([], ∅)
  | s :: ss =>
      let other := bucketScopes x ss
      if x ∈ s then (other.1, s ∪ other.2)
      else (s :: other.1, other.2)

/-- The table after eliminating x is indexed by the surviving bucket scope. -/
def eliminateScopes (x : Fin n)
    (ss : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  (bucketScopes x ss).2.erase x :: (bucketScopes x ss).1

def bucketWidth (x : Fin n) (ss : List (Finset (Fin n))) : Nat :=
  (bucketScopes x ss).2.card

def rowsAfterElimination (x : Fin n) (ss : List (Finset (Fin n))) : Nat :=
  2 ^ ((bucketScopes x ss).2.erase x).card

/-- The width trace follows exactly the static transformation of the bucket
    scope, one entry per elimination step. -/
def widths : List (Fin n) → List (Finset (Fin n)) → List Nat
  | [], _ => []
  | x :: xs, ss => bucketWidth x ss :: widths xs (eliminateScopes x ss)

/-- The table row sizes trace follows the actual tables materialized by memo. -/
def tableRows : List (Fin n) → List (Finset (Fin n)) → List Nat
  | [], _ => []
  | x :: xs, ss => rowsAfterElimination x ss ::
      tableRows xs (eliminateScopes x ss)

def maxWidth (xs : List (Fin n)) (ss : List (Finset (Fin n))) : Nat :=
  (widths xs ss).foldl max 0

def totalRows (xs : List (Fin n)) (ss : List (Finset (Fin n))) : Nat :=
  (tableRows xs ss).sum

theorem scope_bucket_matches (x : Fin n) (fs : List (Factor n R)) :
    ((bucket x fs).1.map Factor.scope, (bucket x fs).2.scope) =
    bucketScopes x (fs.map Factor.scope) := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      have hf := congrArg Prod.fst ih
      have hs := congrArg Prod.snd ih
      by_cases hx : x ∈ f.scope
      · simp only [bucket, bucketScopes, List.map_cons, if_pos hx]
        apply Prod.ext
        · exact hf
        · exact congrArg (fun s => f.scope ∪ s) hs
      · simp only [bucket, bucketScopes, List.map_cons, if_neg hx]
        apply Prod.ext
        · exact congrArg (List.cons f.scope) hf
        · exact hs

theorem scope_eliminateMemo_matches (x : Fin n) (fs : List (Factor n R)) :
    (eliminateMemo x fs).map Factor.scope =
    eliminateScopes x (fs.map Factor.scope) := by
  simp only [eliminateMemo, eliminateScopes, List.map_cons]
  have h := scope_bucket_matches x fs
  cases hh : bucket x fs with
  | mk untouched joined =>
      simp only [hh] at h ⊢
      have hf := congrArg Prod.fst h
      have hs := congrArg Prod.snd h
      simp only [Prod.fst, Prod.snd] at hf hs
      change joined.scope.erase x :: List.map Factor.scope untouched =
        (bucketScopes x (List.map Factor.scope fs)).2.erase x ::
          (bucketScopes x (List.map Factor.scope fs)).1
      rw [hf, hs]

theorem source_materialized_rows (x : Fin n) (fs : List (Factor n R)) :
    (makeTable (Factor.sumOut (bucket x fs).2 x)).length =
      rowsAfterElimination x (fs.map Factor.scope) := by
  rw [makeTable_length]
  change 2 ^ (((bucket x fs).2.scope.erase x).card) =
    2 ^ (((bucketScopes x (fs.map Factor.scope)).2.erase x).card)
  exact congrArg (fun s : Finset (Fin n) => 2 ^ ((s.erase x).card))
    (congrArg Prod.snd (scope_bucket_matches x fs))

/-- Removing a key cannot increase scope width. -/
theorem rows_le_bucket (x : Fin n) (ss : List (Finset (Fin n))) :
    rowsAfterElimination x ss ≤ 2 ^ bucketWidth x ss := by
  apply Nat.pow_le_pow_right (by omega)
  exact Finset.card_le_card (Finset.erase_subset x _)

/-- One certified table is made per eliminated variable. -/
theorem tableRows_length (xs : List (Fin n)) (ss : List (Finset (Fin n))) :
    (tableRows xs ss).length = xs.length := by
  induction xs generalizing ss with
  | nil => rfl
  | cons x xs ih =>
      simp only [tableRows, List.length_cons]
      rw [ih]

theorem widths_length (xs : List (Fin n)) (ss : List (Finset (Fin n))) :
    (widths xs ss).length = xs.length := by
  induction xs generalizing ss with
  | nil => rfl
  | cons x xs ih =>
      simp only [widths, List.length_cons]
      rw [ih]

/-- The sum of actual memo-table rows is at most sum of the powers of the
    corresponding pre-elimination bucket widths (no lookup cost included). -/
theorem totalRows_le_sum_widths (xs : List (Fin n))
    (ss : List (Finset (Fin n))) :
    totalRows xs ss ≤ ((widths xs ss).map (fun w => 2 ^ w)).sum := by
  induction xs generalizing ss with
  | nil => rfl
  | cons x xs ih =>
      change rowsAfterElimination x ss + totalRows xs (eliminateScopes x ss) ≤
        2 ^ bucketWidth x ss +
          ((widths xs (eliminateScopes x ss)).map fun w => 2 ^ w).sum
      exact Nat.add_le_add (rows_le_bucket x ss) (ih (eliminateScopes x ss))

/-- If every intermediate bucket has size at most w, the algorithm's
    (materialized) table-row budget is at most number of steps times 2^w.
    This is a bound on row creation, NOT a full bit-time bound. -/
theorem totalRows_le_of_width_bound (xs : List (Fin n))
    (ss : List (Finset (Fin n))) (w : Nat)
    (hw : ∀ v ∈ widths xs ss, v ≤ w) :
    totalRows xs ss ≤ xs.length * 2 ^ w := by
  induction xs generalizing ss with
  | nil => simp [totalRows, tableRows]
  | cons x xs ih =>
      have hhead : bucketWidth x ss ≤ w := by
        exact hw _ (by simp [widths])
      have htail : ∀ v ∈ widths xs (eliminateScopes x ss), v ≤ w := by
        intro v hv
        exact hw v (by simp [widths, hv])
      change rowsAfterElimination x ss + totalRows xs (eliminateScopes x ss) ≤
        (xs.length + 1) * 2 ^ w
      calc
        rowsAfterElimination x ss + totalRows xs (eliminateScopes x ss) ≤
            2 ^ w + xs.length * 2 ^ w :=
          Nat.add_le_add ((rows_le_bucket x ss).trans
            (Nat.pow_le_pow_right (by omega) hhead))
            (ih (eliminateScopes x ss) htail)
        _ = (xs.length + 1) * 2 ^ w := by ring

/-- Every intermediate factor scope is a subset of the n-variable universe.
    Therefore a generic full n-variable schedule has an n*2^n row envelope;
    this bound is not subexponential and never claims to be. -/
theorem totalRows_le_ambient (xs : List (Fin n))
    (ss : List (Finset (Fin n))) :
    totalRows xs ss ≤ xs.length * 2 ^ n := by
  apply totalRows_le_of_width_bound xs ss n
  intro v hv
  induction xs generalizing ss with
  | nil => simp [widths] at hv
  | cons x xs ih =>
      simp only [widths, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact (Finset.card_le_univ _).trans_eq (by simp)
      · exact ih (eliminateScopes x ss) hv

/-- In particular the full list of variables materializes at most n*2^n
    factor-table rows, regardless of the CNF and elimination schedule. -/
theorem totalRows_full_le (ss : List (Finset (Fin n))) :
    totalRows (List.finRange n) ss ≤ n * 2 ^ n := by
  simpa using totalRows_le_ambient (List.finRange n) ss

/-- This recursive source-cost observer records the precise table lengths
    created in each call of eliminateMemo. It does not run actual table lookup. -/
def sourceTableRows : List (Fin n) → List (Factor n R) → List Nat
  | [], _ => []
  | x :: xs, fs =>
      (makeTable (Factor.sumOut (bucket x fs).2 x)).length ::
        sourceTableRows xs (eliminateMemo x fs)

/-- The STATIC scope transformation exactly matches the factor-support list
    produced by running actual memoized elimination, for every schedule. -/
theorem run_scopes_match (xs : List (Fin n))
    (fs : List (Factor n R)) :
    (runMemo xs fs).map Factor.scope =
      xs.foldl (fun ss x => eliminateScopes x ss) (fs.map Factor.scope) := by
  induction xs generalizing fs with
  | nil => rfl
  | cons x xs ih =>
      change (runMemo xs (eliminateMemo x fs)).map Factor.scope =
        xs.foldl (fun ss y => eliminateScopes y ss)
          (eliminateScopes x (fs.map Factor.scope))
      rw [ih, scope_eliminateMemo_matches]

/-- The static widths exactly predict the number of rows of every
    dynamically materialized factor table, not merely the first table. -/
theorem sourceTableRows_eq_static (xs : List (Fin n))
    (fs : List (Factor n R)) :
    sourceTableRows xs fs = tableRows xs (fs.map Factor.scope) := by
  induction xs generalizing fs with
  | nil => rfl
  | cons x xs ih =>
      change (makeTable (Factor.sumOut (bucket x fs).2 x)).length ::
        sourceTableRows xs (eliminateMemo x fs) =
        rowsAfterElimination x (fs.map Factor.scope) ::
          tableRows xs (eliminateScopes x (fs.map Factor.scope))
      rw [source_materialized_rows, ih, scope_eliminateMemo_matches]

/-- FINISHED RESOURCE CERTIFICATE: on any source list of independent local
    factors and any order whose actual intermediate bucket widths are ≤w,
    total materialized TABLE ROWS are ≤ (#steps) * 2^w.
    IMPORTANT: no claim about machine instructions, memory bit cost, table
    lookup runtime, or uniform upper bound on the width w is made here. -/
theorem source_table_rows_le (xs : List (Fin n))
    (fs : List (Factor n R)) (w : Nat)
    (hw : ∀ v ∈ widths xs (fs.map Factor.scope), v ≤ w) :
    (sourceTableRows xs fs).sum ≤ xs.length * 2 ^ w := by
  rw [sourceTableRows_eq_static]
  exact totalRows_le_of_width_bound xs (fs.map Factor.scope) w hw

end GeneralVE.Complexity
