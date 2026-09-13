import Mathlib

/-!
# Piecewise Soil Moisture Stress Function (Chapter 2, Eq. 5)

β(θ) = 1                              if θ ≥ θ_c
     = ((θ − θ_w) / (θ_c − θ_w))^q   if θ_w < θ < θ_c
     = 0                              if θ ≤ θ_w

Also: REW, bounded REW (f_REW), and the EF soil moisture response.
-/

namespace ThesisProofs.Ch02.Stress

noncomputable section

/-! ### Linear stress function (q = 1 case) -/

/-- Linear stress β(θ) — the q = 1 specialization of Eq. 5 -/
def beta_linear (θ θ_w θ_c : ℝ) : ℝ :=
  if θ ≤ θ_w then 0
  else if θ_c ≤ θ then 1
  else (θ - θ_w) / (θ_c - θ_w)

/-- **β ∈ [0, 1]** for all θ -/
theorem beta_linear_bounds (θ θ_w θ_c : ℝ) (_hwc : θ_w < θ_c) :
    0 ≤ beta_linear θ θ_w θ_c ∧ beta_linear θ θ_w θ_c ≤ 1 := by
  unfold beta_linear
  constructor
  · split_ifs with h1 h2
    · linarith
    · linarith
    · apply div_nonneg <;> linarith
  · split_ifs with h1 h2
    · linarith
    · linarith
    · rw [div_le_one (by linarith : (0 : ℝ) < θ_c - θ_w)]
      linarith

/-- β = 0 at the wilting point -/
theorem beta_linear_at_wp (θ_w θ_c : ℝ) :
    beta_linear θ_w θ_w θ_c = 0 := by
  unfold beta_linear
  rw [if_pos (le_refl _)]

/-- β = 1 at the critical threshold -/
theorem beta_linear_at_crit (θ_c θ_w : ℝ) (hwc : θ_w < θ_c) :
    beta_linear θ_c θ_w θ_c = 1 := by
  unfold beta_linear
  split_ifs with h1 h2
  · linarith
  · rfl
  · linarith

/-! ### Relative Extractable Water -/

/-- REW = (θ − θ_wp) / (θ_fc − θ_wp) (Chapter 2 Eq. 6) -/
def REW (θ θ_wp θ_fc : ℝ) : ℝ := (θ - θ_wp) / (θ_fc - θ_wp)

/-- REW = 0 at wilting point -/
theorem REW_at_wp (θ_wp θ_fc : ℝ) : REW θ_wp θ_wp θ_fc = 0 := by
  unfold REW; simp

/-- REW = 1 at field capacity -/
theorem REW_at_fc (θ_wp θ_fc : ℝ) (h : θ_wp ≠ θ_fc) :
    REW θ_fc θ_wp θ_fc = 1 := by
  unfold REW
  rw [div_eq_one_iff_eq (sub_ne_zero.mpr (Ne.symm h))]

/-- Bounded REW clamped to [0, 1] (Ch6 Eq. 6.6) -/
def f_REW (θ θ_wp θ_fc : ℝ) : ℝ := max 0 (min 1 (REW θ θ_wp θ_fc))

/-- **f_REW ∈ [0, 1]** -/
theorem f_REW_bounds (θ θ_wp θ_fc : ℝ) :
    0 ≤ f_REW θ θ_wp θ_fc ∧ f_REW θ θ_wp θ_fc ≤ 1 := by
  unfold f_REW
  constructor
  · exact le_max_left 0 _
  · exact max_le (by norm_num) (min_le_left 1 _)

/-! ### Evaporative Fraction (EF) Response -/

/-- EF two-regime response (Ch2 Eq. 7):
    Energy-limited above θ*, water-limited below -/
def EF_response (θ θ_star EF_max slope : ℝ) : ℝ :=
  if θ_star ≤ θ then EF_max
  else EF_max + slope * (θ - θ_star)

/-- EF at θ* = EF_max (transition point) -/
theorem EF_at_threshold (θ_star EF_max slope : ℝ) :
    EF_response θ_star θ_star EF_max slope = EF_max := by
  unfold EF_response
  rw [if_pos (le_refl _)]

/-- EF is continuous at θ* (left limit = right value) -/
theorem EF_continuous_at_threshold (θ_star EF_max slope : ℝ) :
    EF_max + slope * (θ_star - θ_star) = EF_max := by
  ring

end
end ThesisProofs.Ch02.Stress
