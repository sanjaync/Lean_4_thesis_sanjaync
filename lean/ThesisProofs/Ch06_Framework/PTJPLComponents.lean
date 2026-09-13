import Mathlib

/-!
# PT-JPL-SM-OWUS Evapotranspiration Components (Chapter 6)

Total ET = Interception + Soil Evaporation + Canopy Transpiration
  λE = λE_I + λE_S + λE_C*

Component definitions from Eq. 6.3–6.5:
- f_wet = RH⁴
- λE_I = f_wet · α · (Δ/(Δ+γ)) · Rn_C
- λE_S = [f_wet + f_rew·(1−f_wet)] · α · (Δ/(Δ+γ)) · (Rn_S − G)
- λE_C = (1−f_wet) · f_G · f_T · f_M · α · (Δ/(Δ+γ)) · Rn_C
-/

namespace ThesisProofs.Ch06.PTJPL

noncomputable section

/-- Wet-surface fraction from relative humidity (Eq. 6.3) -/
def f_wet (RH : ℝ) : ℝ := RH ^ 4

/-- Canopy interception evaporation (Eq. 6.4a) -/
def lambda_E_I (f_w α Δ γ Rn_C : ℝ) : ℝ :=
  f_w * α * (Δ / (Δ + γ)) * Rn_C

/-- Soil evaporation (Eq. 6.4b) -/
def lambda_E_S (f_w f_rew α Δ γ Rn_S G : ℝ) : ℝ :=
  (f_w + f_rew * (1 - f_w)) * α * (Δ / (Δ + γ)) * (Rn_S - G)

/-- Baseline canopy transpiration (Eq. 6.5) -/
def lambda_E_C (f_w f_G f_T f_M α Δ γ Rn_C : ℝ) : ℝ :=
  (1 - f_w) * f_G * f_T * f_M * α * (Δ / (Δ + γ)) * Rn_C

/-- Total ET is additive (Eq. 6.13) -/
def lambda_E_total (E_I E_S E_C : ℝ) : ℝ := E_I + E_S + E_C

/-- Additive decomposition identity -/
theorem total_ET_decomposition (E_I E_S E_C : ℝ) :
    lambda_E_total E_I E_S E_C = E_I + E_S + E_C := by
  unfold lambda_E_total
  rfl

/-- **f_wet ∈ [0, 1]** when RH ∈ [0, 1] -/
theorem f_wet_bounds (RH : ℝ) (hRH0 : 0 ≤ RH) (hRH1 : RH ≤ 1) :
    0 ≤ f_wet RH ∧ f_wet RH ≤ 1 := by
  unfold f_wet
  constructor
  · positivity
  · have h2 : RH ^ 2 ≤ 1 := by nlinarith
    have h4 : (RH ^ 2) ^ 2 ≤ 1 := by nlinarith
    calc RH ^ 4 = (RH ^ 2) ^ 2 := by ring
      _ ≤ 1 := h4

/-- f_wet is monotone in RH -/
theorem f_wet_mono (RH₁ RH₂ : ℝ) (h0 : 0 ≤ RH₁) (h : RH₁ ≤ RH₂) :
    f_wet RH₁ ≤ f_wet RH₂ := by
  unfold f_wet
  have h2 : RH₁ ^ 2 ≤ RH₂ ^ 2 := by nlinarith
  have h4 : (RH₁ ^ 2) ^ 2 ≤ (RH₂ ^ 2) ^ 2 := by nlinarith
  calc RH₁ ^ 4 = (RH₁ ^ 2) ^ 2 := by ring
    _ ≤ (RH₂ ^ 2) ^ 2 := h4
    _ = RH₂ ^ 4 := by ring

/-- The soil evaporation mixing coefficient f_w + f_rew·(1−f_w) ∈ [0,1] -/
theorem soil_evap_coeff_bounds (f_w f_rew : ℝ)
    (hw0 : 0 ≤ f_w) (hw1 : f_w ≤ 1) (hr0 : 0 ≤ f_rew) (hr1 : f_rew ≤ 1) :
    0 ≤ f_w + f_rew * (1 - f_w) ∧ f_w + f_rew * (1 - f_w) ≤ 1 := by
  constructor
  · apply add_nonneg
    · exact hw0
    · exact mul_nonneg hr0 (by linarith)
  · have h_mul : f_rew * (1 - f_w) ≤ 1 * (1 - f_w) := by
      apply mul_le_mul_of_nonneg_right hr1 (by linarith)
    calc f_w + f_rew * (1 - f_w)
      _ ≤ f_w + 1 * (1 - f_w) := by linarith
      _ = 1 := by ring

end
end ThesisProofs.Ch06.PTJPL
