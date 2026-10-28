import GeneralVE

namespace GeneralVE
variable {n : Nat} {R : Type*} [CommSemiring R]

private def splitBits (k : Nat) :
    (Fin (k+1) → Bool) ≃ Bool × (Fin k → Bool) where
  toFun := fun c => (c 0, fun i => c i.succ)
  invFun := fun p => Fin.cons p.1 p.2
  left_inv := by
    intro c
    funext j
    exact Fin.cases (by simp) (fun i => by simp) j
  right_inv := by
    intro p
    rcases p with ⟨b,t⟩
    simp

/-- Replace listed coordinates with a Boolean bit-vector of matching length.
    The reversed update order matches the foldl marginalization convention. -/
def applyChoices : (xs : List (Fin n)) →
    (Fin xs.length → Bool) → Assignment n → Assignment n
  | [], _, a => a
  | x :: xs, c, a =>
      Function.update (applyChoices xs (fun j => c j.succ) a) x (c 0)

/-- Generic expansion of iterated marginals as a sum over choice vectors. -/
theorem marginalMany_choices (xs : List (Fin n))
    (f : Assignment n → R) (a : Assignment n) :
    marginalMany xs f a =
      ∑ c : Fin xs.length → Bool, f (applyChoices xs c a) := by
  induction xs generalizing f with
  | nil =>
      simp [marginalMany, applyChoices]
  | cons x xs ih =>
      change marginalMany xs (marginal x f) a = _
      rw [ih]
      have heq :
          (∑ c : Fin (xs.length+1) → Bool, f (applyChoices (x :: xs) c a)) =
          ∑ p : Bool × (Fin xs.length → Bool),
            f (Function.update (applyChoices xs p.2 a) x p.1) := by
        apply Fintype.sum_equiv (splitBits xs.length)
        intro c
        rfl
      simp only [List.length_cons]
      rw [heq]
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      apply Fintype.sum_congr
      intro c
      simp [marginal, Fintype.sum_bool, add_comm]

/-- A unique support position is assigned the matching choice bit. -/
theorem applyChoices_get (xs : List (Fin n))
    (hd : xs.Nodup) (c : Fin xs.length → Bool)
    (a : Assignment n) (j : Fin xs.length) :
    applyChoices xs c a (xs.get j) = c j := by
  induction xs with
  | nil => exact j.elim0
  | cons x xs ih =>
      have hhead : x ∉ xs := (List.nodup_cons.mp hd).1
      have htail : xs.Nodup := (List.nodup_cons.mp hd).2
      cases j using Fin.cases with
      | zero => simp [applyChoices, Function.update]
      | succ j =>
          have hne : xs.get j ≠ x := fun he => hhead (he ▸ List.get_mem xs j)
          have hh := ih htail (fun i : Fin xs.length => c i.succ) j
          change (Function.update
            (applyChoices xs (fun i => c i.succ) a) x (c 0)) (xs.get j) = c j.succ
          rw [Function.update_apply]
          simp only [if_neg hne]
          exact hh

/-- For the canonical complete list of Fin n coordinates, every variable
    is assigned exactly once, independent of the starting assignment. -/
theorem applyChoices_finRange (c : Fin (List.finRange n).length → Bool)
    (a : Assignment n) :
    applyChoices (List.finRange n) c a =
      fun j => c (Fin.cast (by simp) j) := by
  funext j
  have h := applyChoices_get (List.finRange n)
      (List.nodup_finRange n) c a (Fin.cast (by simp) j)
  simpa [List.get_finRange] using h

/-- Full marginalization is the true finite sum over the entire Boolean cube. -/
theorem marginalMany_finRange (f : Assignment n → R)
    (a : Assignment n) :
    marginalMany (List.finRange n) f a = ∑ b : Assignment n, f b := by
  rw [marginalMany_choices]
  let e : Fin (List.finRange n).length ≃ Fin n :=
    (Fin.castOrderIso (List.length_finRange)).toEquiv
  let eqv : (Fin (List.finRange n).length → Bool) ≃ Assignment n :=
    Equiv.piCongrLeft (fun _ => Bool) e
  apply Fintype.sum_equiv eqv
  intro c
  rw [applyChoices_finRange]
  rfl

end GeneralVE
