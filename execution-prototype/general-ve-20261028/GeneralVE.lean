import Mathlib

/-! General bucket variable elimination over arbitrary Fin n Boolean factors.
    Factors explicitly carry a local support proof. The algorithm contracts
    only factors containing the eliminated variable. -/
namespace GeneralVE

variable {n : Nat} {R : Type*} [CommSemiring R]
abbrev Assignment (n : Nat) := Fin n → Bool

structure Factor (n : Nat) (R : Type*) [CommSemiring R] where
  scope : Finset (Fin n)
  value : Assignment n → R
  locality : ∀ a b : Assignment n,
    (∀ v ∈ scope, a v = b v) → value a = value b

namespace Factor

/-- A constant one factor, independent of all variables. -/
def one : Factor n R where
  scope := ∅
  value := fun _ => 1
  locality := by intros; rfl

/-- Combine two factors without destroying local support bookkeeping. -/
def mul (f g : Factor n R) : Factor n R where
  scope := f.scope ∪ g.scope
  value := fun a => f.value a * g.value a
  locality := by
    intro a b h
    congr 1
    · apply f.locality
      intro v hv
      exact h v (Finset.mem_union.mpr (Or.inl hv))
    · apply g.locality
      intro v hv
      exact h v (Finset.mem_union.mpr (Or.inr hv))

/-- Eliminate variable x from a joined factor: sum over its two Boolean values.
    The new factor's true support is the original support with x erased. -/
def sumOut (f : Factor n R) (x : Fin n) : Factor n R where
  scope := f.scope.erase x
  value := fun a => f.value (Function.update a x false) +
    f.value (Function.update a x true)
  locality := by
    intro a b h
    have heq (choice : Bool) :
        f.value (Function.update a x choice) =
        f.value (Function.update b x choice) := by
      apply f.locality
      intro v hv
      by_cases vx : v = x
      · subst v
        simp
      · simp [Function.update, vx]
        exact h v (Finset.mem_erase.mpr ⟨vx, hv⟩)
    rw [heq false, heq true]

end Factor

/-- Product of a list of factors (the original partition-function integrand). -/
def product (fs : List (Factor n R)) (a : Assignment n) : R :=
  (fs.map fun f => f.value a).prod

/-- The bucket accumulator holds untouched factors and a single joined factor
    carrying the scopes that mention x; this maintains sparse scopes. -/
def bucket (x : Fin n) : List (Factor n R) →
    List (Factor n R) × Factor n R
  | [] => ([], Factor.one)
  | f :: fs =>
    let rest := bucket x fs
    if x ∈ f.scope then
      (rest.1, Factor.mul f rest.2)
    else
      (f :: rest.1, rest.2)

/-- Standard variable elimination: sum out x from its bucket only. -/
def eliminate (x : Fin n) (fs : List (Factor n R)) : List (Factor n R) :=
  let (untouched, collected) := bucket x fs
  Factor.sumOut collected x :: untouched

/-- Eliminate in any prescribed order, leaving one constant factor per bucket. -/
def run (xs : List (Fin n)) (fs : List (Factor n R)) : List (Factor n R) :=
  xs.foldl (fun curr x => eliminate x curr) fs

/-- The obvious one-variable marginalization operator. -/
def marginal (x : Fin n) (f : Assignment n → R) : Assignment n → R :=
  fun a => f (Function.update a x false) +
    f (Function.update a x true)

private theorem bucket_product (x : Fin n)
    (fs : List (Factor n R)) (a : Assignment n) :
    product fs a = product (bucket x fs).1 a * (bucket x fs).2.value a := by
  induction fs with
  | nil => simp [bucket, product, Factor.one]
  | cons f fs ih =>
    simp only [bucket]
    split
    · simp only [product, List.map_cons, List.prod_cons, Factor.mul]
      have hi : (List.map (fun f => f.value a) fs).prod =
          (List.map (fun f => f.value a) (bucket x fs).1).prod *
          (bucket x fs).2.value a := ih
      rw [hi]
      ring
    · simp only [product, List.map_cons, List.prod_cons]
      have hi : (List.map (fun f => f.value a) fs).prod =
          (List.map (fun f => f.value a) (bucket x fs).1).prod *
          (bucket x fs).2.value a := ih
      rw [hi]
      ring

private theorem bucket_untouched (x : Fin n)
    (fs : List (Factor n R)) (f : Factor n R)
    (hf : f ∈ (bucket x fs).1) : x ∉ f.scope := by
  induction fs with
  | nil => simp [bucket] at hf
  | cons g gs ih =>
    simp only [bucket] at hf
    split at hf
    · exact ih hf
    · simp only [List.mem_cons] at hf
      rcases hf with rfl | hf
      · assumption
      · exact ih hf

private theorem bucket_stable (x : Fin n) (fs : List (Factor n R))
    (a : Assignment n) (b : Bool) :
    product (bucket x fs).1 (Function.update a x b) =
      product (bucket x fs).1 a := by
  unfold product
  apply congrArg List.prod
  apply List.map_congr_left
  intro f hf
  apply f.locality
  intro v hv
  have hne : v ≠ x := by
    intro h
    subst v
    exact (bucket_untouched x fs f hf) hv
  simp [Function.update, hne]

/-- Main soundness theorem for generic bucket elimination, pointwise in all
    non-eliminated coordinates: all untouched factors remain outside the sum. -/
theorem eliminate_correct (x : Fin n) (fs : List (Factor n R))
    (a : Assignment n) :
    product (eliminate x fs) a = marginal x (product fs) a := by
  simp only [eliminate, marginal]
  generalize hb : bucket x fs = p
  rcases p with ⟨remaining, collected⟩
  have h1 := bucket_product (R := R) x fs (Function.update a x false)
  have h2 := bucket_product (R := R) x fs (Function.update a x true)
  have hs1 := bucket_stable (R := R) x fs a false
  have hs2 := bucket_stable (R := R) x fs a true
  rw [hb] at h1 h2 hs1 hs2
  simp only at h1 h2 hs1 hs2
  rw [h1,h2,hs1,hs2]
  simp only [product, List.map_cons, List.prod_cons, Factor.sumOut]
  ring


/-- Successive variable marginalization is defined independently of the bucket
    implementation. It remains meaningful for any commutative semiring. -/
def marginalMany (xs : List (Fin n)) (f : Assignment n → R) : Assignment n → R :=
  xs.foldl (fun g x => marginal x g) f

/-- A general, proven contract for a sequence of bucket eliminations:
    its output factor product equals the nested exact finite Boolean sums.
    This theorem holds for arbitrary factor lists, supports, and schedules. -/
theorem run_correct (xs : List (Fin n)) (fs : List (Factor n R))
    (a : Assignment n) :
    product (run xs fs) a = marginalMany xs (product fs) a := by
  induction xs generalizing fs with
  | nil => rfl
  | cons x xs ih =>
      change product (run xs (eliminate x fs)) a =
        marginalMany xs (marginal x (product fs)) a
      rw [ih]
      have heq : product (eliminate x fs) = marginal x (product fs) := by
        funext a
        exact eliminate_correct x fs a
      rw [heq]

end GeneralVE
