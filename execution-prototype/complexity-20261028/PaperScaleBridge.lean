import MemoComplexity
import OAI.Algorithms.SubexponentialSAT.SqrtLog.StatementScale

/-! A CONDITIONAL numerical bridge to the exact exponent scale used by the
    upstream paper. This is only about table ROWS, not full bit-machine TIME.
    Crucially the paper-scale WIDTH hypothesis is explicit and is not proved
    for arbitrary CNF (indeed the complete interaction witness contradicts
    such a bound for the raw bucket eliminator). -/
namespace GeneralVE.Complexity

open OAI.Algorithms.SubexponentialSAT.SqrtLog.Statement

variable {n : Nat} {R : Type*} [CommSemiring R]

/-- If a separately verified elimination order has width w no larger than the
    paper's exponentConstant * runtimeScale n, our cached-table row budget
    lies inside that exponential envelope (times schedule length).
    NOT a theorem that the input admits such a schedule; NOT a time theorem. -/
theorem rows_le_paper_scale
    (xs : List (Fin n)) (fs : List (Factor n R))
    (w : Nat) (exponentConstant : ℝ)
    (hwidth : ∀ v ∈ widths xs (fs.map Factor.scope), v ≤ w)
    (hscale : (w : ℝ) ≤ exponentConstant * runtimeScale n) :
    ((sourceTableRows xs fs).sum : ℝ) ≤
      (xs.length : ℝ) * (2 : ℝ) ^ (exponentConstant * runtimeScale n) := by
  have hn := source_table_rows_le xs fs w hwidth
  have hpow : (2 : ℝ) ^ (w : ℝ) ≤
      (2 : ℝ) ^ (exponentConstant * runtimeScale n) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hscale
  calc
    ((sourceTableRows xs fs).sum : ℝ) ≤
        ((xs.length * 2 ^ w : Nat) : ℝ) := by exact_mod_cast hn
    _ = (xs.length : ℝ) * (2 : ℝ) ^ (w : ℝ) := by
      rw [Real.rpow_natCast]
      push_cast
      rfl
    _ ≤ (xs.length : ℝ) * (2 : ℝ) ^
          (exponentConstant * runtimeScale n) :=
        mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg xs.length)

end GeneralVE.Complexity
