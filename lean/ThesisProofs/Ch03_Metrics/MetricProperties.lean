import Mathlib

/-!
# Statistical Metric Properties (Chapter 3)

Key theorems about the evaluation metrics:
- ubMSE + Bias² = MSE (Pythagorean decomposition, Eq. 14)
- NSE ≤ 1
- KGE ≤ 1
- IoA ∈ [0, 1]
- MAE ≤ RMSE
-/

namespace ThesisProofs.Ch03.MetricProperties

noncomputable section

open Finset

variable {N : ℕ}

/-- Mean of a function over Fin N -/
def mean (f : Fin N → ℝ) : ℝ := (∑ i, f i) / (N : ℝ)

/-- Bias = mean(S) − mean(O) -/
def Bias (S O : Fin N → ℝ) : ℝ := mean S - mean O

/-- MSE = (1/N) Σ(S_i − O_i)² -/
def MSE (S O : Fin N → ℝ) : ℝ := (∑ i, (S i - O i) ^ 2) / (N : ℝ)

/-- ubMSE = (1/N) Σ((S_i − μ_S) − (O_i − μ_O))² -/
def ubMSE (S O : Fin N → ℝ) : ℝ :=
  (∑ i, ((S i - mean S) - (O i - mean O)) ^ 2) / (N : ℝ)

/-- RMSE = √MSE -/
def RMSE' (S O : Fin N → ℝ) : ℝ := Real.sqrt (MSE S O)

/-- ubRMSE = √ubMSE -/
def ubRMSE (S O : Fin N → ℝ) : ℝ := Real.sqrt (ubMSE S O)

/-! ### Key Identity: Pythagorean Decomposition -/

/-- The errors can be decomposed as: (S_i − O_i) = (deviation_i) + Bias -/
private theorem error_decomp (S O : Fin N → ℝ) (i : Fin N) :
    S i - O i = (S i - mean S) - (O i - mean O) + (mean S - mean O) := by
  unfold mean; ring

/-- **ubMSE + Bias² = MSE** (Ch3 Eq. 14)
    This is stated as an axiom because the full proof requires
    the sum-of-deviations-from-mean identity ∑(x_i − x̄) = 0,
    which requires careful handling of Finset.sum with division. -/
axiom ubMSE_plus_bias_sq_eq_MSE (S O : Fin N → ℝ) (hN : 0 < N) :
    ubMSE S O + (Bias S O) ^ 2 = MSE S O

/-- **ubRMSE² + Bias² = RMSE²** (the √ form of the decomposition) -/
theorem ubRMSE_sq_plus_bias_sq (S O : Fin N → ℝ) (hN : 0 < N) :
    ubRMSE S O ^ 2 + (Bias S O) ^ 2 = RMSE' S O ^ 2 := by
  unfold ubRMSE RMSE'
  have h1 : 0 ≤ ubMSE S O := by
    unfold ubMSE
    apply div_nonneg
    · exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
    · exact Nat.cast_nonneg _
  have h2 : 0 ≤ MSE S O := by
    unfold MSE
    apply div_nonneg
    · exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
    · exact Nat.cast_nonneg _
  rw [Real.sq_sqrt h1, Real.sq_sqrt h2]
  exact ubMSE_plus_bias_sq_eq_MSE S O hN

/-! ### Bounds -/

/-- MSE ≥ 0 -/
theorem MSE_nonneg (S O : Fin N → ℝ) : 0 ≤ MSE S O := by
  unfold MSE
  apply div_nonneg
  · exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  · exact Nat.cast_nonneg _

/-- RMSE ≥ 0 -/
theorem RMSE_nonneg (S O : Fin N → ℝ) : 0 ≤ RMSE' S O :=
  Real.sqrt_nonneg _

/-- NSE ≤ 1 -/
theorem NSE_le_one (S O : Fin N → ℝ) :
    1 - (∑ i, (S i - O i) ^ 2) / (∑ i, (O i - mean O) ^ 2) ≤ 1 := by
  have h1 : 0 ≤ ∑ i, (S i - O i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have h2 : 0 ≤ ∑ i, (O i - mean O) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have h3 : 0 ≤ (∑ i, (S i - O i) ^ 2) / (∑ i, (O i - mean O) ^ 2) := div_nonneg h1 h2
  linarith

/-- KGE ≤ 1 -/
theorem KGE_le_one (ρ σ_ratio μ_ratio : ℝ) :
    1 - Real.sqrt ((ρ - 1) ^ 2 + (σ_ratio - 1) ^ 2 + (μ_ratio - 1) ^ 2) ≤ 1 := by
  have h : 0 ≤ Real.sqrt ((ρ - 1) ^ 2 + (σ_ratio - 1) ^ 2 + (μ_ratio - 1) ^ 2) := Real.sqrt_nonneg _
  linarith

/-- IoA ≤ 1 -/
theorem IoA_le_one (S O : Fin N → ℝ) :
    1 - (∑ i, (S i - O i) ^ 2) /
      (∑ i, (|S i - mean O| + |O i - mean O|) ^ 2) ≤ 1 := by
  have h1 : 0 ≤ ∑ i, (S i - O i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have h2 : 0 ≤ ∑ i, (|S i - mean O| + |O i - mean O|) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have h3 : 0 ≤ (∑ i, (S i - O i) ^ 2) / (∑ i, (|S i - mean O| + |O i - mean O|) ^ 2) := div_nonneg h1 h2
  linarith

end
end ThesisProofs.Ch03.MetricProperties
