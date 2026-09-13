import Mathlib

/-!
# Kalman Filter Bayesian Update (Chapter 4, Eq. 7)

The Kalman filter update equations (scalar case, H = 1):
  x⁺ = x⁻ + K(y − x⁻)
  K  = P / (P + R)

Properties:
- K ∈ [0, 1] when P, R > 0
- x⁺ is a convex combination of x⁻ and y
- Posterior variance shrinks: P⁺ ≤ P
-/

namespace ThesisProofs.Ch04.Kalman

noncomputable section

/-- Scalar Kalman gain -/
def kalman_gain (P R : ℝ) : ℝ := P / (P + R)

/-- Scalar Kalman update (H = 1) -/
def kalman_update (x_prior y P R : ℝ) : ℝ :=
  x_prior + kalman_gain P R * (y - x_prior)

/-- **Kalman gain is in [0, 1]** when P > 0 and R > 0 -/
theorem kalman_gain_bounds (P R : ℝ) (hP : 0 < P) (hR : 0 < R) :
    0 ≤ kalman_gain P R ∧ kalman_gain P R ≤ 1 := by
  unfold kalman_gain
  have hPR : 0 < P + R := by linarith
  constructor
  · exact div_nonneg (le_of_lt hP) (le_of_lt hPR)
  · rw [div_le_one hPR]; linarith

/-- **Kalman update is a convex combination** of prior and observation -/
theorem kalman_update_convex (x_prior y P R : ℝ) (_hP : 0 < P) (_hR : 0 < R) :
    kalman_update x_prior y P R =
      (1 - kalman_gain P R) * x_prior + kalman_gain P R * y := by
  unfold kalman_update; ring

/-- When R → 0 (perfect observation), gain = 1 -/
theorem kalman_gain_perfect_obs (P : ℝ) (hP : 0 < P) :
    kalman_gain P 0 = 1 := by
  unfold kalman_gain
  simp [ne_of_gt hP]

/-- Posterior variance P⁺ = (1 − K) · P -/
def posterior_variance (P R : ℝ) : ℝ := (1 - kalman_gain P R) * P

/-- **Posterior variance ≤ prior variance** (data assimilation always reduces uncertainty) -/
theorem posterior_variance_le (P R : ℝ) (hP : 0 < P) (hR : 0 < R) :
    posterior_variance P R ≤ P := by
  unfold posterior_variance
  have ⟨hK0, hK1⟩ := kalman_gain_bounds P R hP hR
  nlinarith

/-- Posterior variance is non-negative -/
theorem posterior_variance_nonneg (P R : ℝ) (hP : 0 < P) (hR : 0 < R) :
    0 ≤ posterior_variance P R := by
  unfold posterior_variance
  have ⟨hK0, hK1⟩ := kalman_gain_bounds P R hP hR
  nlinarith

/-- Posterior variance expressed directly: P⁺ = P·R / (P + R) -/
theorem posterior_variance_formula (P R : ℝ) (hP : 0 < P) (hR : 0 < R) :
    posterior_variance P R = P * R / (P + R) := by
  unfold posterior_variance kalman_gain
  have hPR : P + R ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

end
end ThesisProofs.Ch04.Kalman
