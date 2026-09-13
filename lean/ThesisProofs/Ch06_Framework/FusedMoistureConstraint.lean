import Mathlib

/-!
# Fused Moisture Constraint f_TRM (Chapter 6, Eq. 6.11–6.12)

Blending weight:
  W = RH^(4·(1−f_REW)·(1−RH))

Fused constraint:
  f_TRM = (1−W)·f_M + W·f_OWUS

Rescaled transpiration:
  λE_C* = λE_C_orig · (f_TRM / f_M)  if f_M > 0

Properties:
- f_TRM is a convex combination
- f_TRM bounded by max(f_M, f_OWUS)
- Boundary cases: W=0 ⟹ pure optical, W=1 ⟹ pure mechanistic
-/

namespace ThesisProofs.Ch06.Fused

noncomputable section

open Real

/-- Blending weight W (Eq. 6.11) -/
def W_blend (RH f_REW : ℝ) : ℝ :=
  RH ^ (4 * (1 - f_REW) * (1 - RH))

/-- Fused moisture constraint (Eq. 6.11) -/
def f_TRM (W f_M f_OWUS : ℝ) : ℝ :=
  (1 - W) * f_M + W * f_OWUS

/-- Rescaled canopy transpiration (Eq. 6.12) -/
def lambda_E_C_star (E_C_orig f_trm f_M : ℝ) : ℝ :=
  if f_M = 0 then 0
  else E_C_orig * (f_trm / f_M)

/-- **f_TRM ≥ 0** when inputs are non-negative and W ∈ [0,1] -/
theorem f_TRM_nonneg (W f_M f_OWUS : ℝ)
    (hW0 : 0 ≤ W) (hW1 : W ≤ 1) (hM : 0 ≤ f_M) (hO : 0 ≤ f_OWUS) :
    0 ≤ f_TRM W f_M f_OWUS := by
  unfold f_TRM
  apply add_nonneg
  · exact mul_nonneg (by linarith) hM
  · exact mul_nonneg hW0 hO

/-- **f_TRM ≤ max(f_M, f_OWUS)** (convex combination bound) -/
theorem f_TRM_le_max (W f_M f_OWUS : ℝ)
    (hW0 : 0 ≤ W) (hW1 : W ≤ 1) :
    f_TRM W f_M f_OWUS ≤ max f_M f_OWUS := by
  unfold f_TRM
  calc (1 - W) * f_M + W * f_OWUS
      ≤ (1 - W) * max f_M f_OWUS + W * max f_M f_OWUS := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (le_max_left f_M f_OWUS) (by linarith)
        · exact mul_le_mul_of_nonneg_left (le_max_right f_M f_OWUS) hW0
    _ = max f_M f_OWUS := by ring

/-- When W = 0, f_TRM = f_M (pure optical proxy) -/
theorem f_TRM_at_zero (f_M f_OWUS : ℝ) :
    f_TRM 0 f_M f_OWUS = f_M := by
  unfold f_TRM; ring

/-- When W = 1, f_TRM = f_OWUS (pure mechanistic) -/
theorem f_TRM_at_one (f_M f_OWUS : ℝ) :
    f_TRM 1 f_M f_OWUS = f_OWUS := by
  unfold f_TRM; ring

/-- f_TRM interpolates: min(f_M, f_OWUS) ≤ f_TRM when W ∈ [0,1] -/
theorem f_TRM_ge_min (W f_M f_OWUS : ℝ)
    (hW0 : 0 ≤ W) (hW1 : W ≤ 1) :
    min f_M f_OWUS ≤ f_TRM W f_M f_OWUS := by
  unfold f_TRM
  calc min f_M f_OWUS
      = (1 - W) * min f_M f_OWUS + W * min f_M f_OWUS := by ring
    _ ≤ (1 - W) * f_M + W * f_OWUS := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (min_le_left f_M f_OWUS) (by linarith)
        · exact mul_le_mul_of_nonneg_left (min_le_right f_M f_OWUS) hW0

end
end ThesisProofs.Ch06.Fused
