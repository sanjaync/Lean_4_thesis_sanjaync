import Mathlib

/-!
# SPAC Transpiration Flux (Chapter 5, Eq. 9–10)

Transpiration as flux through the Soil-Plant-Atmosphere Continuum:
  T = (K_SR · K_P) / (K_SR + K_P) · (ψ_s − ψ_c)

This is analogous to conductances in series (or parallel resistances).
-/

namespace ThesisProofs.Ch05.SPAC

noncomputable section

/-- Conductances-in-series formula: K_total = (K₁·K₂)/(K₁+K₂) -/
def conductance_series (K_SR K_P : ℝ) : ℝ := (K_SR * K_P) / (K_SR + K_P)

/-- SPAC transpiration flux -/
def T_SPAC (K_SR K_P ψ_s ψ_c : ℝ) : ℝ :=
  conductance_series K_SR K_P * (ψ_s - ψ_c)

/-- Series conductance ≤ each individual conductance -/
theorem conductance_series_le_min (K_SR K_P : ℝ)
    (hSR : 0 < K_SR) (hP : 0 < K_P) :
    conductance_series K_SR K_P ≤ K_SR ∧
    conductance_series K_SR K_P ≤ K_P := by
  unfold conductance_series
  have hSum : 0 < K_SR + K_P := by linarith
  constructor
  · rw [div_le_iff₀ hSum]
    nlinarith
  · rw [div_le_iff₀ hSum]
    nlinarith

/-- Series conductance is non-negative -/
theorem conductance_series_nonneg (K_SR K_P : ℝ)
    (hSR : 0 < K_SR) (hP : 0 < K_P) :
    0 ≤ conductance_series K_SR K_P := by
  unfold conductance_series
  apply div_nonneg
  · exact mul_nonneg (le_of_lt hSR) (le_of_lt hP)
  · linarith

/-- Symmetry: conductance series is symmetric -/
theorem conductance_series_comm (K_SR K_P : ℝ) :
    conductance_series K_SR K_P = conductance_series K_P K_SR := by
  unfold conductance_series; ring

/-- Transpiration is non-negative when water flows downhill (ψ_s ≥ ψ_c) -/
theorem T_SPAC_nonneg (K_SR K_P ψ_s ψ_c : ℝ)
    (hSR : 0 < K_SR) (hP : 0 < K_P) (hψ : ψ_c ≤ ψ_s) :
    0 ≤ T_SPAC K_SR K_P ψ_s ψ_c := by
  unfold T_SPAC
  apply mul_nonneg
  · exact conductance_series_nonneg K_SR K_P hSR hP
  · linarith

/-- When K_SR = K_P, total conductance = K/2 -/
theorem conductance_series_equal (K : ℝ) (hK : K ≠ 0) :
    conductance_series K K = K / 2 := by
  unfold conductance_series
  field_simp
  ring

end
end ThesisProofs.Ch05.SPAC
