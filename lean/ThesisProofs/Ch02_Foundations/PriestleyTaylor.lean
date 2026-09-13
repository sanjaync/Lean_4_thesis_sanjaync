import Mathlib

/-!
# Priestley–Taylor Formulation (Chapter 2, Eq. 3)

  λE = α · (Δ / (Δ + γ)) · (Rn − G)

where α = 1.26 is the Priestley–Taylor coefficient.
Properties: non-negativity, linearity in α, equilibrium at α = 1.
-/

namespace ThesisProofs.Ch02.PT

noncomputable section

/-- The Priestley–Taylor potential evapotranspiration -/
def PT_PET (α Δ γ Rn G : ℝ) : ℝ := α * (Δ / (Δ + γ)) * (Rn - G)

/-- PT-PET is non-negative under physical conditions -/
theorem PT_PET_nonneg (α Δ γ Rn G : ℝ)
    (hα : 0 ≤ α) (hΔ : 0 ≤ Δ) (hγ : 0 < γ) (hRn : G ≤ Rn) :
    0 ≤ PT_PET α Δ γ Rn G := by
  unfold PT_PET
  apply mul_nonneg
  · apply mul_nonneg hα
    apply div_nonneg hΔ
    linarith
  · linarith

/-- PT-PET scales linearly with α -/
theorem PT_PET_scale (α₁ α₂ Δ γ Rn G : ℝ) :
    PT_PET (α₁ * α₂) Δ γ Rn G = α₁ * PT_PET α₂ Δ γ Rn G := by
  unfold PT_PET; ring

/-- When α = 1, PT reduces to the equilibrium evaporation rate -/
theorem PT_PET_equilibrium (Δ γ Rn G : ℝ) :
    PT_PET 1 Δ γ Rn G = (Δ / (Δ + γ)) * (Rn - G) := by
  unfold PT_PET; ring

/-- PT-PET is monotonically increasing in (Rn − G) when α, Δ/(Δ+γ) > 0 -/
theorem PT_PET_mono_Rn (α Δ γ Rn₁ Rn₂ G : ℝ)
    (hα : 0 < α) (hΔ : 0 < Δ) (hγ : 0 < γ) (h : Rn₁ ≤ Rn₂) :
    PT_PET α Δ γ Rn₁ G ≤ PT_PET α Δ γ Rn₂ G := by
  unfold PT_PET
  apply mul_le_mul_of_nonneg_left
  · linarith
  · apply mul_nonneg (le_of_lt hα)
    exact div_nonneg (le_of_lt hΔ) (by linarith)

end
end ThesisProofs.Ch02.PT
