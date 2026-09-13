import Mathlib

/-!
# Fresnel Reflectivity (Chapter 4)

Smooth-surface Fresnel reflection coefficients and the h-Q roughness model:
  r_{S,p} = [(1−Q)·r_{0,p} + Q·r_{0,q}] · exp(−h · cos^N θ)

Key properties: convex combination, non-negativity.
-/

namespace ThesisProofs.Ch04.Fresnel

noncomputable section

open Real

/-- Roughness-modified reflectivity (h-Q model, Ch4 Eq. 2) -/
def roughness_reflectivity (Q r0p r0q h cosθ N : ℝ) : ℝ :=
  ((1 - Q) * r0p + Q * r0q) * exp (-h * cosθ ^ N)

/-- Convex combination property: if Q ∈ [0,1] and r₀ ≥ 0, mix is non-negative -/
theorem convex_combination_nonneg (Q r0p r0q : ℝ)
    (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1) (hr0p : 0 ≤ r0p) (hr0q : 0 ≤ r0q) :
    0 ≤ (1 - Q) * r0p + Q * r0q := by
  apply add_nonneg
  · exact mul_nonneg (by linarith) hr0p
  · exact mul_nonneg hQ0 hr0q

/-- Convex combination is bounded above by max -/
theorem convex_combination_le_max (Q r0p r0q : ℝ)
    (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1) :
    (1 - Q) * r0p + Q * r0q ≤ max r0p r0q := by
  calc (1 - Q) * r0p + Q * r0q
      ≤ (1 - Q) * max r0p r0q + Q * max r0p r0q := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith)
        · exact mul_le_mul_of_nonneg_left (le_max_right _ _) hQ0
    _ = max r0p r0q := by ring

/-- Roughness reflectivity is non-negative under physical conditions -/
theorem roughness_reflectivity_nonneg (Q r0p r0q h cosθ N : ℝ)
    (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1) (hr0p : 0 ≤ r0p) (hr0q : 0 ≤ r0q) :
    0 ≤ roughness_reflectivity Q r0p r0q h cosθ N := by
  unfold roughness_reflectivity
  exact mul_nonneg
    (convex_combination_nonneg Q r0p r0q hQ0 hQ1 hr0p hr0q)
    (le_of_lt (exp_pos _))

/-- When Q = 0, reflectivity uses only p-polarization -/
theorem reflectivity_no_mixing (r0p r0q h cosθ N : ℝ) :
    roughness_reflectivity 0 r0p r0q h cosθ N = r0p * exp (-h * cosθ ^ N) := by
  unfold roughness_reflectivity; ring

end
end ThesisProofs.Ch04.Fresnel
