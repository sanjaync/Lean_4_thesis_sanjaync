import Mathlib

/-!
# Buckingham-Π Dimensionless Groups (Chapter 5, Eq. 11)

Defines the four non-dimensional hydraulic strategy groups that reduce
the SPAC parameter space from 8 traits to 4 dimensionless numbers:
- Π_R: Risk-tolerance (ψ_g50 / ψ_x50)
- Π_F: Flux-control   (E₀ / (K_Pmax · |ψ_g50|))
- Π_T: Transport-capacity (K_SRmax · |ψ_g50| / E₀)
- Π_S: Soil-suitability  (ψ_g50 / ψ_ssat)

Also defines the well-watered transpiration ratio f_ww (Ch5 Eq. 13).
-/

namespace ThesisProofs.Defs.BuckinghamPi

noncomputable section

open Real

/-! ### Π-Group Definitions -/

/-- Risk-tolerance ratio: Π_R = ψ_g50 / ψ_x50 -/
def Pi_R (ψ_g50 ψ_x50 : ℝ) : ℝ := ψ_g50 / ψ_x50

/-- Flux-control ratio: Π_F = E₀ / (K_Pmax · |ψ_g50|) -/
def Pi_F (E₀ K_Pmax ψ_g50 : ℝ) : ℝ := E₀ / (K_Pmax * |ψ_g50|)

/-- Transport-capacity ratio: Π_T = K_SRmax · |ψ_g50| / E₀ -/
def Pi_T (K_SRmax ψ_g50 E₀ : ℝ) : ℝ := (K_SRmax * |ψ_g50|) / E₀

/-- Soil-suitability ratio: Π_S = ψ_g50 / ψ_ssat -/
def Pi_S (ψ_g50 ψ_ssat : ℝ) : ℝ := ψ_g50 / ψ_ssat

/-! ### Positivity under physical constraints -/

theorem Pi_R_pos (ψ_g50 ψ_x50 : ℝ) (h1 : 0 < ψ_g50) (h2 : 0 < ψ_x50) :
    0 < Pi_R ψ_g50 ψ_x50 := by
  unfold Pi_R
  exact div_pos h1 h2

theorem Pi_F_pos (E₀ K_Pmax ψ_g50 : ℝ) (hE : 0 < E₀) (hK : 0 < K_Pmax) (hψ : ψ_g50 ≠ 0) :
    0 < Pi_F E₀ K_Pmax ψ_g50 := by
  unfold Pi_F
  apply div_pos hE
  exact mul_pos hK (abs_pos.mpr hψ)

theorem Pi_T_pos (K_SRmax ψ_g50 E₀ : ℝ) (hK : 0 < K_SRmax) (hψ : ψ_g50 ≠ 0) (hE : 0 < E₀) :
    0 < Pi_T K_SRmax ψ_g50 E₀ := by
  unfold Pi_T
  apply div_pos
  · exact mul_pos hK (abs_pos.mpr hψ)
  · exact hE

/-! ### Well-Watered Transpiration Ratio -/

/-- Well-watered transpiration ratio f_ww (Ch5 Eq. 13, Ch6 Eq. 6.7).
    The raw (unbounded) expression before clamping to [0,1]:
    f_ww_raw = 1 − (1/(2Π_R)) · [1 + Π_F/2 − √((Π_F/2 + 1)² − 2·Π_F·Π_R)] -/
def f_ww_raw (Pi_R Pi_F : ℝ) : ℝ :=
  1 - (1 / (2 * Pi_R)) * (1 + Pi_F / 2 -
    sqrt (max 0 ((Pi_F / 2 + 1) ^ 2 - 2 * Pi_F * Pi_R)))

/-- Clamped well-watered transpiration ratio -/
def f_ww (Pi_R Pi_F : ℝ) : ℝ := max 0 (min 1 (f_ww_raw Pi_R Pi_F))

/-- **f_ww is bounded in [0, 1]** by construction -/
theorem f_ww_bounds (Pi_R Pi_F : ℝ) :
    0 ≤ f_ww Pi_R Pi_F ∧ f_ww Pi_R Pi_F ≤ 1 := by
  unfold f_ww
  constructor
  · exact le_max_left 0 _
  · exact max_le (by norm_num) (min_le_left 1 _)

end
end ThesisProofs.Defs.BuckinghamPi
