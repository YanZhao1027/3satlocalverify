import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeOuterBudgets

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract

open DisjointReuse

def nativeLeafFeasibleBudget (k Cs sd n L : ℕ) : ℕ :=
  Cs * (L + 1) ^ sd +
    (101 * SparseCountProgram.formulaBound n k + 103) +
    (5 * n + 6)

/-- The three lower budgets share a common polynomial upper budget,
with constants fixed before `n` and `L`.

This establishes budget feasibility only. It does not establish full
general algorithm extraction or a bit-time bound. -/
theorem nativeLeaf_polynomialBudget_feasible (k Cs sd : ℕ) :
    let c : ℕ := 2 + (4 + 8 * k) * (k + 1) * 2 ^ k
    let g : ℕ := max sd (k + 1)
    let K : ℕ := Cs + 101 * c + 114
    ∀ n L : ℕ, n ≤ L →
      let bound := nativeLeafFeasibleBudget k Cs sd n L
      Cs * (L + 1) ^ sd ≤ bound ∧
      101 * SparseCountProgram.formulaBound n k + 103 ≤ bound ∧
      5 * n + 6 ≤ bound ∧
      bound ≤ K * (L + 1) ^ g := by
  dsimp only
  intro n L hn
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold nativeLeafFeasibleBudget
    omega
  · unfold nativeLeafFeasibleBudget
    omega
  · unfold nativeLeafFeasibleBudget
    omega
  · let c : ℕ := 2 + (4 + 8 * k) * (k + 1) * 2 ^ k
    let g : ℕ := max sd (k + 1)
    let K : ℕ := Cs + 101 * c + 114
    let P : ℕ := (L + 1) ^ g
    change nativeLeafFeasibleBudget k Cs sd n L ≤ K * P

    have hsd : sd ≤ g := Nat.le_max_left sd (k + 1)
    have hkg : k + 1 ≤ g := Nat.le_max_right sd (k + 1)
    have h1g : 1 ≤ g := by omega

    have hbase : L + 1 ≤ P := by
      change L + 1 ≤ (L + 1) ^ g
      simpa only [pow_one] using
        (Nat.pow_le_pow_right (by omega) h1g :
          (L + 1) ^ 1 ≤ (L + 1) ^ g)

    have hP : 1 ≤ P := by omega

    have hsdPow : (L + 1) ^ sd ≤ P :=
      Nat.pow_le_pow_right (by omega) hsd

    have hspace : Cs * (L + 1) ^ sd ≤ Cs * P :=
      Nat.mul_le_mul_left Cs hsdPow

    have hformula :
        SparseCountProgram.formulaBound n k ≤ c * P := by
      calc
        SparseCountProgram.formulaBound n k
            ≤ c * (n + 1) ^ (k + 1) :=
          OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.formulaBound_polynomial n k
        _ ≤ c * (L + 1) ^ (k + 1) :=
          Nat.mul_le_mul_left c
            (Nat.pow_le_pow_left
              (by omega : n + 1 ≤ L + 1) (k + 1))
        _ ≤ c * P :=
          Nat.mul_le_mul_left c
            (Nat.pow_le_pow_right (by omega) hkg)

    have hconstant : 103 ≤ 103 * P := by omega

    have hclassifier :
        101 * SparseCountProgram.formulaBound n k + 103 ≤
          (101 * c + 103) * P := by
      calc
        101 * SparseCountProgram.formulaBound n k + 103
            ≤ 101 * (c * P) + 103 * P :=
          Nat.add_le_add (Nat.mul_le_mul_left 101 hformula) hconstant
        _ = (101 * c + 103) * P := by
          simp only [Nat.add_mul, Nat.mul_assoc]

    have hpower : 5 * n + 6 ≤ 11 * P := by omega

    calc
      nativeLeafFeasibleBudget k Cs sd n L =
          Cs * (L + 1) ^ sd +
            (101 * SparseCountProgram.formulaBound n k + 103) +
            (5 * n + 6) := rfl
      _ ≤ Cs * P + ((101 * c + 103) * P) + 11 * P :=
        Nat.add_le_add (Nat.add_le_add hspace hclassifier) hpower
      _ = K * P := by
        dsimp only [K]
        simp only [Nat.add_mul, Nat.mul_assoc]
        omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract
