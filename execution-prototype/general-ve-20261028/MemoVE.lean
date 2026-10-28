import GeneralVE

/-! A semantically transparent, table-backed optimization for general bucket
    variable elimination: enumerate only support assignments, materialize the
    expensive factor values once, and use a local support-key lookup. -/
namespace GeneralVE

variable {n : Nat} {R : Type*} [CommSemiring R]

/-- Generate truth assignments to the variables in one *local support* only.
    The unlisted variables receive a fixed false base value. -/
def sampleSupport : List (Fin n) → List (Assignment n)
  | [] => [fun _ => false]
  | v :: vs =>
    (sampleSupport vs).flatMap fun a =>
      [Function.update a v false, Function.update a v true]

/-- Look up a cached row by equality on the support rather than entire n-space. -/
def tableLookup (s : Finset (Fin n)) :
    List (Assignment n × R) → Assignment n → Option R
  | [], _ => none
  | (b,v)::tail,a =>
    if ∀ j ∈ s, b j = a j then some v else tableLookup s tail a

/-- The sample list is at most 2^(support size). No global cube is enumerated. -/
def makeTable (f : Factor n R) : List (Assignment n × R) :=
  (sampleSupport (f.scope.sort (· ≤ ·))).map fun a => (a,f.value a)

/-- Source-level caching: `table` is evaluated *before* the returned closure
    is constructed, so all lookups reuse an existing table of factor values. -/
def cachedFn (f : Factor n R) : Assignment n → R :=
  let table := makeTable f
  fun a =>
    match tableLookup f.scope table a with
    | some v => v
    | none => f.value a

private theorem lookup_sound (f : Factor n R)
    (samples : List (Assignment n)) (a : Assignment n)
    (v : R) (h : tableLookup f.scope
      (samples.map fun b => (b,f.value b)) a = some v) :
    v = f.value a := by
  induction samples with
  | nil => simp [tableLookup] at h
  | cons b bs ih =>
      by_cases heq : ∀ j ∈ f.scope, b j = a j
      · simp only [List.map_cons, tableLookup, if_pos heq] at h
        cases Option.some.inj h
        exact f.locality b a heq
      · simp only [List.map_cons, tableLookup, if_neg heq] at h
        exact ih h

/-- Crucial certification: the cache NEVER changes a factor's mathematical
    value, even if a lookup misses. This theorem does not assume anything
    about how sampleSupport enumerates local vectors. -/
theorem cachedFn_eq (f : Factor n R) (a : Assignment n) :
    cachedFn f a = f.value a := by
  unfold cachedFn
  cases h : tableLookup f.scope (makeTable f) a with
  | none => rfl
  | some v =>
      exact lookup_sound f (sampleSupport (f.scope.sort (· ≤ ·))) a v (by
        simpa only [makeTable] using h)

/-- Turn a pure factor into an explicit factor object with a captured table.
    The computed `rows` is allocated outside the lookup closure. -/
def memo (f : Factor n R) : Factor n R :=
  let rows := makeTable f
  let cached : Assignment n → R := fun a =>
    match tableLookup f.scope rows a with
    | some v => v
    | none => f.value a
  have hc : ∀ a, cached a = f.value a := by
    intro a
    change cachedFn f a = f.value a
    exact cachedFn_eq f a
  { scope := f.scope
    value := cached
    locality := by
      intro a b hab
      rw [hc a, hc b]
      exact f.locality a b hab }

theorem memo_value_eq (f : Factor n R) (a : Assignment n) :
    (memo f).value a = f.value a := by
  change cachedFn f a = f.value a
  exact cachedFn_eq f a

/-- The memoized bucket transition has exactly the original mathematical
    semantics; only the physical representation of the output factor changes. -/
def eliminateMemo (x : Fin n) (fs : List (Factor n R)) :
    List (Factor n R) :=
  let (untouched, joined) := bucket x fs
  memo (Factor.sumOut joined x) :: untouched

theorem eliminateMemo_correct (x : Fin n) (fs : List (Factor n R))
    (a : Assignment n) :
    product (eliminateMemo x fs) a = marginal x (product fs) a := by
  have hsource := eliminate_correct x fs a
  unfold eliminateMemo eliminate at *
  simp only [product, List.map_cons, List.prod_cons, memo_value_eq] at *
  exact hsource

def runMemo (xs : List (Fin n)) (fs : List (Factor n R)) :
    List (Factor n R) := xs.foldl (fun acc x => eliminateMemo x acc) fs

theorem runMemo_correct (xs : List (Fin n)) (fs : List (Factor n R))
    (a : Assignment n) :
    product (runMemo xs fs) a = marginalMany xs (product fs) a := by
  induction xs generalizing fs with
  | nil => rfl
  | cons x xs ih =>
      change product (runMemo xs (eliminateMemo x fs)) a =
        marginalMany xs (marginal x (product fs)) a
      rw [ih]
      have h : product (eliminateMemo x fs) = marginal x (product fs) := by
        funext b
        exact eliminateMemo_correct x fs b
      rw [h]

end GeneralVE
