import Mathlib

/-!
# Surface Energy Balance (Chapter 2, Eq. 1)

The surface energy balance states that net radiation minus soil heat flux
minus sensible heat flux equals latent heat flux:
  Rn − G − H = λE

Equivalently: Rn = λE + H + G
-/

namespace ThesisProofs.Ch02.EnergyBalance

/-- Surface energy balance: the residual formulation -/
theorem energy_balance_residual (Rn G H LE : ℝ)
    (h : Rn - G - H = LE) : LE = Rn - G - H := by linarith

/-- Energy balance: conservation form -/
theorem energy_balance_conservation (Rn G H LE : ℝ)
    (h : Rn = LE + H + G) : Rn - G - H = LE := by linarith

/-- Latent heat is non-negative when Rn ≥ G + H -/
theorem latent_heat_nonneg (Rn G H LE : ℝ)
    (h : Rn - G - H = LE) (hRn : Rn ≥ G + H) : LE ≥ 0 := by linarith

/-- The closure ratio Rn / (λE + H + G) = 1 when the balance holds -/
theorem closure_ratio_one (Rn G H LE : ℝ)
    (h : Rn = LE + H + G) (hRn : Rn ≠ 0) :
    (LE + H + G) / Rn = 1 := by
  rw [← h]
  exact div_self hRn

end ThesisProofs.Ch02.EnergyBalance
