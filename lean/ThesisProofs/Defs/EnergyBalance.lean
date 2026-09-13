import Mathlib

/-!
# Energy Balance Definitions (Chapter 2)

Formalizes:
- Surface energy balance: Rn − G − H = λE
- Priestley–Taylor potential evapotranspiration
- Beer's law radiation partitioning between canopy and soil
-/

namespace ThesisProofs.Defs.EnergyBalance

noncomputable section

open Real

/-! ### Surface Energy Balance -/

/-- Surface energy balance predicate:
    Net radiation = Latent heat + Sensible heat + Ground heat flux -/
def SurfaceEnergyBalance (Rn G H LE : ℝ) : Prop := Rn - G - H = LE

/-! ### Priestley–Taylor Equation -/

/-- Priestley–Taylor potential evapotranspiration (Ch2 Eq. 3):
    PET = α · (Δ / (Δ + γ)) · (Rn − G) -/
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

/-- When α = 1, PT reduces to equilibrium evaporation -/
theorem PT_PET_equilibrium (Δ γ Rn G : ℝ) :
    PT_PET 1 Δ γ Rn G = (Δ / (Δ + γ)) * (Rn - G) := by
  unfold PT_PET; ring

/-! ### Beer's Law Radiation Partition -/

/-- Canopy-intercepted radiation (Ch6 Eq. 6.2):
    Rn_C = Rn · (1 − exp(−k · LAI)) -/
def Rn_canopy (Rn k LAI : ℝ) : ℝ := Rn * (1 - exp (-k * LAI))

/-- Soil-reaching radiation (Ch6 Eq. 6.2):
    Rn_S = Rn · exp(−k · LAI) -/
def Rn_soil (Rn k LAI : ℝ) : ℝ := Rn * exp (-k * LAI)

/-- **Beer's Law Partition Identity**: Canopy + Soil = Total -/
theorem beer_law_partition (Rn k LAI : ℝ) :
    Rn_canopy Rn k LAI + Rn_soil Rn k LAI = Rn := by
  unfold Rn_canopy Rn_soil
  ring

/-- Canopy radiation is in [0, Rn] under physical conditions -/
theorem Rn_canopy_bounds (Rn k LAI : ℝ)
    (hRn : 0 ≤ Rn) (hk : 0 ≤ k) (hLAI : 0 ≤ LAI) :
    0 ≤ Rn_canopy Rn k LAI ∧ Rn_canopy Rn k LAI ≤ Rn := by
  unfold Rn_canopy
  have hexp : 0 < exp (-k * LAI) := exp_pos _
  have hexp1 : exp (-k * LAI) ≤ 1 := by
    rw [exp_le_one_iff]
    nlinarith
  constructor
  · apply mul_nonneg hRn; linarith
  · nlinarith

/-- Soil radiation is non-negative -/
theorem Rn_soil_nonneg (Rn k LAI : ℝ) (hRn : 0 ≤ Rn) :
    0 ≤ Rn_soil Rn k LAI := by
  unfold Rn_soil
  exact mul_nonneg hRn (le_of_lt (exp_pos _))

end
end ThesisProofs.Defs.EnergyBalance
