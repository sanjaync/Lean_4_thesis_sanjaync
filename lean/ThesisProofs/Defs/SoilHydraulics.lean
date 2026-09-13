import Mathlib

/-!
# Soil Hydraulics Definitions

Formalizes the core soil moisture state variables and stress functions
from Chapters 2, 5, and 6 of the thesis.

## Key Definitions
- `REW`: Relative Extractable Water (Ch2 Eq. 6, Ch6 Eq. 6.3)
- `f_REW`: Bounded REW clamped to [0,1] (Ch6 Eq. 6.6)
- `beta_linear`: Piecewise-linear stress function β with q=1 (Ch2 Eq. 5)

## Key Theorems
- `f_REW_bounds`: 0 ≤ f_REW ≤ 1
- `beta_linear_bounds`: 0 ≤ β ≤ 1
- `REW_at_wp`, `REW_at_fc`: Boundary values
-/

namespace ThesisProofs.Defs.SoilHydraulics

noncomputable section

/-! ### Relative Extractable Water (REW) -/

/-- Relative Extractable Water (unbounded).
    REW = (θ − θ_wp) / (θ_fc − θ_wp)
    Chapter 2, Eq. 6. -/
def REW (θ θ_wp θ_fc : ℝ) : ℝ := (θ - θ_wp) / (θ_fc - θ_wp)

/-- REW = 0 at the wilting point -/
theorem REW_at_wp (θ_wp θ_fc : ℝ) : REW θ_wp θ_wp θ_fc = 0 := by
  unfold REW; simp

/-- REW = 1 at field capacity -/
theorem REW_at_fc (θ_wp θ_fc : ℝ) (h : θ_wp ≠ θ_fc) :
    REW θ_fc θ_wp θ_fc = 1 := by
  unfold REW
  rw [div_eq_one_iff_eq (sub_ne_zero.mpr (Ne.symm h))]

/-- REW is monotonically increasing in θ (when θ_fc > θ_wp) -/
theorem REW_mono (θ₁ θ₂ θ_wp θ_fc : ℝ) (hfc : θ_wp < θ_fc) (h12 : θ₁ ≤ θ₂) :
    REW θ₁ θ_wp θ_fc ≤ REW θ₂ θ_wp θ_fc := by
  unfold REW
  apply div_le_div_of_nonneg_right _ (by linarith)
  linarith

/-! ### Bounded REW (clamped to [0,1]) -/

/-- Bounded REW, clamped to [0, 1].
    f_REW = max(0, min(1, REW(θ, θ_wp, θ_fc)))
    Chapter 6, Eq. 6.6. -/
def f_REW (θ θ_wp θ_fc : ℝ) : ℝ := max 0 (min 1 (REW θ θ_wp θ_fc))

/-- **f_REW is bounded in [0, 1]** by construction via max/min -/
theorem f_REW_bounds (θ θ_wp θ_fc : ℝ) :
    0 ≤ f_REW θ θ_wp θ_fc ∧ f_REW θ θ_wp θ_fc ≤ 1 := by
  unfold f_REW
  constructor
  · exact le_max_left 0 _
  · exact max_le (by norm_num) (min_le_left 1 _)

/-! ### Piecewise-Linear Stress Function β -/

/-- Linear soil moisture stress function (q = 1 case).
    β(θ) = 0 if θ ≤ θ_w; 1 if θ ≥ θ_c; linear in between.
    Chapter 2, Eq. 5 with q = 1. -/
def beta_linear (θ θ_w θ_c : ℝ) : ℝ :=
  if θ ≤ θ_w then 0
  else if θ_c ≤ θ then 1
  else (θ - θ_w) / (θ_c - θ_w)

/-- **β is bounded in [0, 1]** for all θ -/
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

/-- β = 1 at and above the critical threshold -/
theorem beta_linear_at_crit (θ_c θ_w : ℝ) (hwc : θ_w < θ_c) :
    beta_linear θ_c θ_w θ_c = 1 := by
  unfold beta_linear
  split_ifs with h1 h2
  · linarith
  · rfl
  · linarith

end
end ThesisProofs.Defs.SoilHydraulics
