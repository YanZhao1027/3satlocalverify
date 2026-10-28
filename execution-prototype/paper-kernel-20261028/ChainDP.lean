import CRTBridgeProof

/-! A verified four-state transfer algorithm for consecutive 3-variable
    factors. Unlike truth-table enumeration, the number of active states is 4.
    The proof is generic in the commutative semiring R and the factor values.
    Thus it also applies to polynomial-valued factors used for exact #SAT. -/

namespace ChainDP

variable {R : Type*} [CommSemiring R]

abbrev Weight (R : Type*) := Bool → Bool → Bool → R

structure State (R : Type*) where
  ff : R
  ft : R
  tf : R
  tt : R

def State.lookup (s : State R) (a b : Bool) : R :=
  match a,b with
  | false,false => s.ff
  | false,true  => s.ft
  | true,false  => s.tf
  | true,true   => s.tt

def State.ofFn (f : Bool → Bool → R) : State R :=
  ⟨f false false, f false true, f true false, f true true⟩

theorem State.lookup_ofFn (f : Bool → Bool → R) (a b : Bool) :
    (State.ofFn f).lookup a b = f a b := by
  cases a <;> cases b <;> rfl

/-- One transfer update. All four coefficients are stored explicitly. -/
def step (s : State R) (w : Weight R) : State R :=
  State.ofFn (fun b c => ∑ a : Bool, s.lookup a b * w a b c)

/-- Compute the weight of all paths ending in each of the four endpoint states. -/
def fastStates (ws : List (Weight R)) : State R :=
  ws.foldl step ⟨1,1,1,1⟩

def fastCount (ws : List (Weight R)) : R :=
  ∑ a : Bool, ∑ b : Bool, (fastStates ws).lookup a b

/-- The obviously correct exponential specification; it chooses each next
    Boolean variable explicitly and multiplies all successive factors. -/
def backward (ws : List (Weight R)) (g : Bool → Bool → R) : Bool → Bool → R :=
  ws.foldr (fun w next a b => ∑ c : Bool, w a b c * next b c) g

def slowCount (ws : List (Weight R)) : R :=
  ∑ a : Bool, ∑ b : Bool, backward ws (fun _ _ => 1) a b

private theorem sum_step (s : State R) (w : Weight R)
    (g : Bool → Bool → R) :
    (∑ b : Bool, ∑ c : Bool, (step s w).lookup b c * g b c) =
      ∑ a : Bool, ∑ b : Bool,
        s.lookup a b * (∑ c : Bool, w a b c * g b c) := by
  simp only [step, State.lookup_ofFn, Fintype.sum_bool]
  ring

/-- Finite sum-product transposition, composing an arbitrary sequence of
    factor transfers. All operations are normal semiring operations. -/
theorem fold_duality (ws : List (Weight R)) (s : State R)
    (g : Bool → Bool → R) :
    (∑ a : Bool, ∑ b : Bool, (ws.foldl step s).lookup a b * g a b) =
      ∑ a : Bool, ∑ b : Bool, s.lookup a b * (backward ws g) a b := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
      calc
        (∑ a : Bool, ∑ b : Bool,
          ((w :: ws).foldl step s).lookup a b * g a b) =
          (∑ a : Bool, ∑ b : Bool,
            (ws.foldl step (step s w)).lookup a b * g a b) := rfl
        _ = (∑ a : Bool, ∑ b : Bool,
            (step s w).lookup a b * (backward ws g) a b) := ih (step s w)
        _ = (∑ a : Bool, ∑ b : Bool,
            s.lookup a b * (∑ c : Bool, w a b c * (backward ws g) b c)) :=
              sum_step s w (backward ws g)
        _ = ∑ a : Bool, ∑ b : Bool,
              s.lookup a b * (backward (w :: ws) g) a b := rfl

/-- Formal verification of the four-state DP for EVERY sequence of local
    triple factors, including factors with polynomial values. -/
theorem fast_eq_slow (ws : List (Weight R)) :
    fastCount ws = slowCount ws := by
  unfold fastCount fastStates slowCount
  conv_lhs => arg 2; intro a; arg 2; intro b; rw [← mul_one ((ws.foldl step ⟨1,1,1,1⟩).lookup a b)]
  rw [fold_duality]
  simp [Fintype.sum_bool, State.lookup]

end ChainDP
