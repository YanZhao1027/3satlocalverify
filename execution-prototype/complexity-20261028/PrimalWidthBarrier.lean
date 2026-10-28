import MemoComplexity

/-! A general structural lower bound on bucket VE table size. Even if each
    INITIAL factor involves only three variables, pairwise shared factors can
    force the first bucket to contain all n variables, for EVERY first choice.
    This does not prove inherent SAT hardness: algebraic cancellations or more
    sophisticated algorithms could avoid explicitly materializing this table. -/
namespace GeneralVE.Complexity

variable {n : Nat}

/-- Exactly characterizes which variables occur in the joined bucket. -/
theorem mem_bucketScopes_iff (ss : List (Finset (Fin n)))
    (x y : Fin n) :
    y ∈ (bucketScopes x ss).2 ↔
      ∃ s ∈ ss, x ∈ s ∧ y ∈ s := by
  induction ss with
  | nil => simp [bucketScopes]
  | cons s ss ih =>
      by_cases hx : x ∈ s
      · simpa [bucketScopes, hx, ih, Finset.mem_union]
      · simpa [bucketScopes, hx, ih]

/-- For any list of supports in which *each pair* of variables shares some
    factor, every possible first elimination bucket has width n. -/
theorem complete_pair_cover_forces_width
    (ss : List (Finset (Fin n)))
    (hpair : ∀ x y : Fin n, ∃ s ∈ ss, x ∈ s ∧ y ∈ s)
    (x : Fin n) :
    bucketWidth x ss = n := by
  have hall : (bucketScopes x ss).2 = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro y
    exact (mem_bucketScopes_iff ss x y).mpr (hpair x y)
  simp [bucketWidth, hall]

/-- Thus the first cache alone has 2^(n-1) entries, independent of the
    elimination order, for a complete pair-coverage factor support family. -/
theorem complete_pair_cover_forces_rows
    (ss : List (Finset (Fin n)))
    (hpair : ∀ x y : Fin n, ∃ s ∈ ss, x ∈ s ∧ y ∈ s)
    (x : Fin n) :
    rowsAfterElimination x ss = 2 ^ (n - 1) := by
  have hall : (bucketScopes x ss).2 = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro y
    exact (mem_bucketScopes_iff ss x y).mpr (hpair x y)
  simp [rowsAfterElimination, hall, Finset.card_erase_of_mem]

end GeneralVE.Complexity
