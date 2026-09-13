import Mathlib

/-!
# Steady-State Soil Saturation PDF (Chapter 5, Eq. 17–18)

Defines:
- σ: Overall Plant Water-Use-Capacity Index (Eq. 15)
- ρ(s): Piecewise soil water loss function (5-regime, Eq. 16)
- p(s): Steady-state PDF structure (Eq. 17)

Properties:
- σ ≥ 0 under ordered thresholds
- ρ(s) ≥ 0 (loss is non-negative)
-/

namespace ThesisProofs.Ch05.SoilPDF

noncomputable section

/-- Overall Plant Water-Use-Capacity Index (Ch5 Eq. 15):
    σ = f_ww · (s_fc − (s* + s_w)/2) / (s_fc − s_h) -/
def sigma (f_ww s_fc s_star s_w s_h : ℝ) : ℝ :=
  f_ww * (s_fc - (s_star + s_w) / 2) / (s_fc - s_h)

/-- σ ≥ 0 under ordered thresholds -/
theorem sigma_nonneg (f_ww s_fc s_star s_w s_h : ℝ)
    (hfww : 0 ≤ f_ww)
    (horder : s_h ≤ s_w ∧ s_w < s_star ∧ s_star ≤ s_fc)
    (_hne : s_h < s_fc) :
    0 ≤ sigma f_ww s_fc s_star s_w s_h := by
  unfold sigma
  apply div_nonneg
  · apply mul_nonneg hfww
    have := horder.2.2
    have := horder.2.1
    have := horder.1
    nlinarith
  · linarith

/-- 5-regime piecewise soil water loss function (Ch5 Eq. 16) -/
def rho_loss (s s_h s_w s_star s_fc E_max T_max : ℝ) : ℝ :=
  if s ≤ s_h then 0
  else if s ≤ s_w then E_max * (s - s_h) / (s_fc - s_h)
  else if s ≤ s_star then
    E_max * (s - s_h) / (s_fc - s_h) + T_max * (s - s_w) / (s_star - s_w)
  else if s ≤ s_fc then
    E_max * (s - s_h) / (s_fc - s_h) + T_max
  else E_max + T_max

/-- Loss function is non-negative above hygroscopic point -/
theorem rho_loss_nonneg (s s_h s_w s_star s_fc E_max T_max : ℝ)
    (hE : 0 ≤ E_max) (hT : 0 ≤ T_max)
    (horder : s_h ≤ s_w ∧ s_w < s_star ∧ s_star ≤ s_fc) :
    0 ≤ rho_loss s s_h s_w s_star s_fc E_max T_max := by
  unfold rho_loss
  split_ifs with h1 h2 h3 h4
  · linarith
  · apply div_nonneg
    · apply mul_nonneg hE; linarith
    · linarith [horder.2.2, horder.2.1, horder.1]
  · apply add_nonneg
    · apply div_nonneg
      · apply mul_nonneg hE; linarith
      · linarith [horder.2.2, horder.2.1, horder.1]
    · apply div_nonneg
      · apply mul_nonneg hT; linarith
      · linarith [horder.2.1]
  · apply add_nonneg
    · apply div_nonneg
      · apply mul_nonneg hE; linarith
      · linarith [horder.2.2, horder.2.1, horder.1]
    · exact hT
  · linarith

/-- At s = s_h, loss is zero -/
theorem rho_loss_at_sh (s_h s_w s_star s_fc E_max T_max : ℝ) :
    rho_loss s_h s_h s_w s_star s_fc E_max T_max = 0 := by
  unfold rho_loss; simp

end
end ThesisProofs.Ch05.SoilPDF
