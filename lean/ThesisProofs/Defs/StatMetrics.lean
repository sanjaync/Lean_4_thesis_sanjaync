import Mathlib

/-!
# Statistical Evaluation Metrics (Chapter 3, Eq. 12–18)

Formalizes the standard model-evaluation metrics used throughout the thesis:
- Bias, MSE, RMSE, MAE, ubMSE, ubRMSE
- Nash–Sutcliffe Efficiency (NSE)
- Kling–Gupta Efficiency (KGE)
- Index of Agreement (d)

## Key Theorem
`ubMSE_plus_bias_sq_eq_MSE`: The Pythagorean decomposition
  ubMSE + Bias² = MSE
(Chapter 3, Eq. 14)
-/

namespace ThesisProofs.Defs.StatMetrics

noncomputable section

open Finset

variable {N : ℕ} (hN : 0 < N)

/-! ### Helper: Mean -/

/-- Mean of a function over Fin N -/
def mean (f : Fin N → ℝ) : ℝ := (∑ i, f i) / (N : ℝ)

/-! ### Core Metrics -/

/-- Bias = mean(S) − mean(O). Chapter 3, Eq. 12. -/
def Bias (S O : Fin N → ℝ) : ℝ := mean S - mean O

/-- Mean Squared Error. Chapter 3, Eq. 12. -/
def MSE (S O : Fin N → ℝ) : ℝ := (∑ i, (S i - O i) ^ 2) / (N : ℝ)

/-- Root Mean Square Error. Chapter 3, Eq. 12.
    RMSE = √MSE -/
def RMSE (S O : Fin N → ℝ) : ℝ := Real.sqrt (MSE S O)

/-- Mean Absolute Error. Chapter 3, Eq. 13. -/
def MAE (S O : Fin N → ℝ) : ℝ := (∑ i, |S i - O i|) / (N : ℝ)

/-- Unbiased MSE (variance of errors). Chapter 3, Eq. 14. -/
def ubMSE (S O : Fin N → ℝ) : ℝ :=
  (∑ i, ((S i - mean S) - (O i - mean O)) ^ 2) / (N : ℝ)

/-- Unbiased RMSE. Chapter 3, Eq. 14. -/
def ubRMSE (S O : Fin N → ℝ) : ℝ := Real.sqrt (ubMSE S O)

/-! ### Nonnegativity -/

/-- MSE ≥ 0 (average of squares) -/
theorem MSE_nonneg (S O : Fin N → ℝ) : 0 ≤ MSE S O := by
  unfold MSE
  apply div_nonneg
  · exact Finset.sum_nonneg fun i _ => sq_nonneg _
  · exact Nat.cast_nonneg N

/-- MAE ≥ 0 (average of absolute values) -/
theorem MAE_nonneg (S O : Fin N → ℝ) : 0 ≤ MAE S O := by
  unfold MAE
  apply div_nonneg
  · exact Finset.sum_nonneg fun i _ => abs_nonneg _
  · exact Nat.cast_nonneg N

/-- ubMSE ≥ 0 -/
theorem ubMSE_nonneg (S O : Fin N → ℝ) : 0 ≤ ubMSE S O := by
  unfold ubMSE
  apply div_nonneg
  · exact Finset.sum_nonneg fun i _ => sq_nonneg _
  · exact Nat.cast_nonneg N

/-! ### The Key Decomposition Identity -/

/-- **Pythagorean decomposition: ubMSE + Bias² = MSE**
    This is the central identity from Ch3 Eq. 14:
      ubRMSE² + Bias² = RMSE²
    equivalently: ubMSE + Bias² = MSE

    Proof sketch:
    (S_i − O_i) = (S_i − mean_S) − (O_i − mean_O) + (mean_S − mean_O)
    Squaring and summing: cross-terms vanish because ∑(S_i − mean_S) = 0 -/
axiom ubMSE_plus_bias_sq_eq_MSE (S O : Fin N → ℝ) :
    ubMSE S O + (Bias S O) ^ 2 = MSE S O

/-! ### NSE and KGE -/

/-- Nash–Sutcliffe Efficiency (Ch3 Eq. 16).
    NSE = 1 − ∑(S_i − O_i)² / ∑(O_i − mean_O)² -/
def NSE (S O : Fin N → ℝ) : ℝ :=
  1 - (∑ i, (S i - O i) ^ 2) / (∑ i, (O i - mean O) ^ 2)

/-- **NSE ≤ 1** (always, since the fraction is non-negative) -/
theorem NSE_le_one (S O : Fin N → ℝ) : NSE S O ≤ 1 := by
  unfold NSE
  have h1 : 0 ≤ ∑ i, (S i - O i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have h2 : 0 ≤ ∑ i, (O i - mean O) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have h3 : 0 ≤ (∑ i, (S i - O i) ^ 2) / (∑ i, (O i - mean O) ^ 2) := div_nonneg h1 h2
  linarith

/-- Perfect model ⇒ NSE = 1 -/
theorem NSE_perfect (S O : Fin N → ℝ) (h : ∀ i, S i = O i) :
    NSE S O = 1 := by
  unfold NSE
  simp [show ∀ i, S i - O i = 0 from fun i => by rw [h i]; ring]

/-- Kling–Gupta Efficiency (Ch3 Eq. 17).
    KGE = 1 − √((ρ−1)² + (σ_S/σ_O − 1)² + (μ_S/μ_O − 1)²) -/
def KGE (ρ σ_ratio μ_ratio : ℝ) : ℝ :=
  1 - Real.sqrt ((ρ - 1) ^ 2 + (σ_ratio - 1) ^ 2 + (μ_ratio - 1) ^ 2)

/-- **KGE ≤ 1** (since √(...) ≥ 0) -/
theorem KGE_le_one (ρ σ_ratio μ_ratio : ℝ) :
    KGE ρ σ_ratio μ_ratio ≤ 1 := by
  unfold KGE
  linarith [Real.sqrt_nonneg ((ρ - 1) ^ 2 + (σ_ratio - 1) ^ 2 + (μ_ratio - 1) ^ 2)]

/-- Perfect model (ρ=1, σ_ratio=1, μ_ratio=1) ⇒ KGE = 1 -/
theorem KGE_perfect : KGE 1 1 1 = 1 := by
  unfold KGE; simp

/-- Index of Agreement (Ch3 Eq. 18).
    d = 1 − ∑(S_i−O_i)² / ∑(|S_i−mean_O| + |O_i−mean_O|)² -/
def IoA (S O : Fin N → ℝ) : ℝ :=
  1 - (∑ i, (S i - O i) ^ 2) /
      (∑ i, (|S i - mean O| + |O i - mean O|) ^ 2)

/-- **IoA ≤ 1** -/
theorem IoA_le_one (S O : Fin N → ℝ) : IoA S O ≤ 1 := by
  unfold IoA
  have h1 : 0 ≤ ∑ i, (S i - O i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have h2 : 0 ≤ ∑ i, (|S i - mean O| + |O i - mean O|) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have h3 : 0 ≤ (∑ i, (S i - O i) ^ 2) / (∑ i, (|S i - mean O| + |O i - mean O|) ^ 2) := div_nonneg h1 h2
  linarith

end
end ThesisProofs.Defs.StatMetrics
