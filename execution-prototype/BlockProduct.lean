import SupportLeaf

namespace Prototype.BlockProduct
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SAT

/-- Map a CNF's literal indices to a larger ambient variable type. -/
def mapLiteral {V W : Type*} (f : V → W) (l : Literal V) : Literal W :=
  ⟨f l.variable, l.positive⟩

def mapClause {V W : Type*} [DecidableEq W] (f : V → W)
    (C : Clause V) : Clause W := C.image (mapLiteral f)

def mapFormula {V W : Type*} [DecidableEq W] (f : V → W)
    (F : CNF V) : CNF W := F.image (mapClause f)

/-- Disjoint variable blocks shifted to consecutive index ranges. -/
def joined {n m : Nat} (F : CNF (Fin n)) (G : CNF (Fin m)) :
    CNF (Fin (n + m)) :=
  mapFormula (Fin.castAdd m) F ∪ mapFormula (Fin.natAdd n) G

private theorem mapClause_eval {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V → W) (C : Clause V) (a : Assignment W) :
    (mapClause f C).eval a = C.eval (fun v => a (f v)) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    obtain ⟨l,hl,ht⟩ := (Clause.eval_eq_true a (mapClause f C)).mp h
    obtain ⟨x,hx,he⟩ := Finset.mem_image.mp hl
    subst l
    exact (Clause.eval_eq_true (fun v => a (f v)) C).mpr
      ⟨x,hx,by simpa [Literal.eval,mapLiteral] using ht⟩
  · intro h
    obtain ⟨l,hl,ht⟩ := (Clause.eval_eq_true (fun v => a (f v)) C).mp h
    apply (Clause.eval_eq_true a (mapClause f C)).mpr
    exact ⟨mapLiteral f l, Finset.mem_image.mpr ⟨l,hl,rfl⟩,
      by simpa [Literal.eval,mapLiteral] using ht⟩

private theorem mapFormula_eval {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V → W) (F : CNF V) (a : Assignment W) :
    (mapFormula f F).eval a = F.eval (fun v => a (f v)) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    apply (CNF.eval_eq_true (fun v => a (f v)) F).mpr
    intro C hC
    have hm : mapClause f C ∈ mapFormula f F :=
      Finset.mem_image.mpr ⟨C,hC,rfl⟩
    rw [← mapClause_eval f C a]
    exact (CNF.eval_eq_true a (mapFormula f F)).mp h _ hm
  · intro h
    apply (CNF.eval_eq_true a (mapFormula f F)).mpr
    intro C hC
    obtain ⟨D,hD,rfl⟩ := Finset.mem_image.mp hC
    rw [mapClause_eval]
    exact (CNF.eval_eq_true (fun v => a (f v)) F).mp h D hD

/-- Any ambient assignment is uniquely a pair of block assignments. -/
def split {n m : Nat} :
    Assignment (Fin (n + m)) ≃
      (Assignment (Fin n) × Assignment (Fin m)) where
  toFun := fun a => (fun i => a (Fin.castAdd m i), fun j => a (Fin.natAdd n j))
  invFun := fun p => Fin.append p.1 p.2
  left_inv := by
    intro a
    funext i
    exact Fin.addCases
      (motive := fun i => Fin.append (fun j => a (Fin.castAdd m j))
        (fun j => a (Fin.natAdd n j)) i = a i)
      (fun j => Fin.append_left _ _ j)
      (fun j => Fin.append_right _ _ j) i
  right_inv := by
    rintro ⟨a,b⟩
    apply Prod.ext
    · funext i
      exact Fin.append_left a b i
    · funext i
      exact Fin.append_right a b i

private theorem joined_eval {n m : Nat} (F : CNF (Fin n)) (G : CNF (Fin m))
    (a : Assignment (Fin n)) (b : Assignment (Fin m)) :
    (joined F G).eval (Fin.append a b) = (F.eval a && G.eval b) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    have hl : (mapFormula (Fin.castAdd m) F).eval (Fin.append a b) = true :=
      CNF.eval_mono (Finset.subset_union_left) h
    have hr : (mapFormula (Fin.natAdd n) G).eval (Fin.append a b) = true :=
      CNF.eval_mono (Finset.subset_union_right) h
    simp only [mapFormula_eval, Fin.append_left, Fin.append_right] at hl hr
    simpa only [Bool.and_eq_true] using (And.intro hl hr)
  · intro h
    have hp : F.eval a = true ∧ G.eval b = true := by
      simpa only [Bool.and_eq_true] using h
    obtain ⟨hl,hr⟩ := hp
    apply (CNF.eval_eq_true (Fin.append a b) (joined F G)).mpr
    intro C hc
    rcases Finset.mem_union.mp hc with hC | hC
    · have he : (mapFormula (Fin.castAdd m) F).eval (Fin.append a b) = true := by
        simpa only [mapFormula_eval, Fin.append_left] using hl
      exact (CNF.eval_eq_true (Fin.append a b) _).mp he C hC
    · have he : (mapFormula (Fin.natAdd n) G).eval (Fin.append a b) = true := by
        simpa only [mapFormula_eval, Fin.append_right] using hr
      exact (CNF.eval_eq_true (Fin.append a b) _).mp he C hC

private theorem cardinal_eq_sum {n : Nat} (F : CNF (Fin n)) :
    SAT.count F = ∑ a : Assignment (Fin n), if F.eval a = true then (1:Nat) else 0 := by
  change (Finset.univ.filter fun a : Assignment (Fin n) => F.eval a = true).card = _
  rw [Finset.card_filter]

/-- Multiplication law for CNFs on independent variable blocks. -/
theorem count_joined {n m : Nat} (F : CNF (Fin n)) (G : CNF (Fin m)) :
    SAT.count (joined F G) = SAT.count F * SAT.count G := by
  rw [cardinal_eq_sum]
  have hsplit :
      (∑ x : Assignment (Fin (n + m)),
        if (joined F G).eval x = true then (1:Nat) else 0) =
      ∑ p : Assignment (Fin n) × Assignment (Fin m),
        if (F.eval p.1 && G.eval p.2) = true then (1:Nat) else 0 := by
    apply Fintype.sum_equiv (split (n := n) (m := m))
    intro x
    change (if (joined F G).eval x = true then (1 : Nat) else 0) =
      if (F.eval (fun i => x (Fin.castAdd m i)) &&
          G.eval (fun j => x (Fin.natAdd n j))) = true then (1 : Nat) else 0
    have heq := joined_eval F G (fun i => x (Fin.castAdd m i))
      (fun j => x (Fin.natAdd n j))
    have hx : Fin.append (fun i => x (Fin.castAdd m i))
        (fun j => x (Fin.natAdd n j)) = x := (split (n := n) (m := m)).left_inv x
    rw [hx] at heq
    exact congrArg (fun z : Bool => if z = true then (1 : Nat) else 0) heq
  rw [hsplit, Fintype.sum_prod_type]
  have hand (p q : Bool) : (if (p && q) = true then (1:Nat) else 0) =
      (if p = true then 1 else 0) * (if q = true then 1 else 0) := by
    cases p <;> cases q <;> decide
  simp_rw [hand]
  calc
    (∑ a : Assignment (Fin n), ∑ b : Assignment (Fin m),
      (if F.eval a = true then (1 : Nat) else 0) *
      (if G.eval b = true then (1 : Nat) else 0)) =
      (∑ a : Assignment (Fin n),
        (if F.eval a = true then (1 : Nat) else 0) *
          (∑ b : Assignment (Fin m), if G.eval b = true then (1 : Nat) else 0)) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.mul_sum]
    _ = (∑ a : Assignment (Fin n), if F.eval a = true then (1 : Nat) else 0) *
        (∑ b : Assignment (Fin m), if G.eval b = true then (1 : Nat) else 0) := by
        rw [Finset.sum_mul]
    _ = SAT.count F * SAT.count G := by
        rw [cardinal_eq_sum F, cardinal_eq_sum G]

end Prototype.BlockProduct
