import Mathlib

/-!
# Radiation Partition in PT-JPL Context (Chapter 6, Eq. 6.2)

Re-states Beer's law partition specifically for the PT-JPL framework:
  Rn_C = Rn · (1 − exp(−k_Rn · LAI))
  Rn_S = Rn · exp(−k_Rn · LAI)
  Rn_C + Rn_S = Rn
-/

namespace ThesisProofs.Ch06.Radiation

noncomputable section

open Real

/-- Canopy-intercepted net radiation -/
def Rn_C (Rn k_Rn LAI : ℝ) : ℝ := Rn * (1 - exp (-k_Rn * LAI))

/-- Soil net radiation -/
def Rn_S (Rn k_Rn LAI : ℝ) : ℝ := Rn * exp (-k_Rn * LAI)

/-- **Partition identity**: canopy + soil = total radiation -/
theorem radiation_partition (Rn k_Rn LAI : ℝ) :
    Rn_C Rn k_Rn LAI + Rn_S Rn k_Rn LAI = Rn := by
  unfold Rn_C Rn_S; ring

/-- Soil fraction is the complement of canopy fraction -/
theorem soil_is_complement (Rn k_Rn LAI : ℝ) :
    Rn_S Rn k_Rn LAI = Rn - Rn_C Rn k_Rn LAI := by
  have h := radiation_partition Rn k_Rn LAI
  linarith

/-- At LAI = 0, all radiation reaches the soil -/
theorem Rn_S_at_zero_LAI (Rn k_Rn : ℝ) :
    Rn_S Rn k_Rn 0 = Rn := by
  unfold Rn_S; simp [exp_zero]

/-- At LAI = 0, no radiation is intercepted by canopy -/
theorem Rn_C_at_zero_LAI (Rn k_Rn : ℝ) :
    Rn_C Rn k_Rn 0 = 0 := by
  unfold Rn_C; simp [exp_zero]

end
end ThesisProofs.Ch06.Radiation
