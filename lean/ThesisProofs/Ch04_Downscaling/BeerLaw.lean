import Mathlib

/-!
# Beer's Law Radiation Partition (Chapter 4 / Chapter 6, Eq. 6.2)

Net radiation is partitioned between canopy and soil using Beer's law:
  Rn_C = Rn · (1 − exp(−k · LAI))
  Rn_S = Rn · exp(−k · LAI)

**Key identity**: Rn_C + Rn_S = Rn
-/

namespace ThesisProofs.Ch04.BeerLaw

noncomputable section

open Real

/-- Canopy-intercepted radiation -/
def Rn_canopy (Rn k LAI : ℝ) : ℝ := Rn * (1 - exp (-k * LAI))

/-- Soil-reaching radiation -/
def Rn_soil (Rn k LAI : ℝ) : ℝ := Rn * exp (-k * LAI)

/-- **Beer's Law Partition Identity**: Canopy + Soil = Total net radiation -/
theorem beer_law_partition (Rn k LAI : ℝ) :
    Rn_canopy Rn k LAI + Rn_soil Rn k LAI = Rn := by
  unfold Rn_canopy Rn_soil
  ring

/-- Canopy radiation is in [0, Rn] when Rn ≥ 0 and k, LAI ≥ 0 -/
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

/-- At LAI = 0, all radiation reaches the soil -/
theorem Rn_soil_at_zero_LAI (Rn k : ℝ) :
    Rn_soil Rn k 0 = Rn := by
  unfold Rn_soil; simp [exp_zero]

/-- At LAI = 0, no radiation is intercepted -/
theorem Rn_canopy_at_zero_LAI (Rn k : ℝ) :
    Rn_canopy Rn k 0 = 0 := by
  unfold Rn_canopy; simp [exp_zero]

end
end ThesisProofs.Ch04.BeerLaw
