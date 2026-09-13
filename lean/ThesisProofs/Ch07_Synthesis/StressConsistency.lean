import Mathlib

/-!
# Stress Function Consistency (Chapter 7)

Shows that different stress formulations across chapters are related:
1. Ch2 empirical β (q=1) ≡ Ch7 β under parameter renaming (θ_c = θ_ref)
2. Ch5 OWUS β with f_ww=1 degenerates to simple linear β
-/

namespace ThesisProofs.Ch07.Consistency

noncomputable section

/-- Chapter 2 linear stress (q=1): β = (θ − θ_w)/(θ_c − θ_w) clamped to [0,1] -/
def beta_ch2 (θ θ_w θ_c : ℝ) : ℝ :=
  if θ ≤ θ_w then 0
  else if θ_c ≤ θ then 1
  else (θ - θ_w) / (θ_c - θ_w)

/-- Chapter 7 empirical beta: β = (θ − θ_wilt)/(θ_ref − θ_wilt) clamped to [0,1] -/
def beta_ch7 (θ θ_wilt θ_ref : ℝ) : ℝ :=
  if θ ≤ θ_wilt then 0
  else if θ_ref ≤ θ then 1
  else (θ - θ_wilt) / (θ_ref - θ_wilt)

/-- **Ch2 and Ch7 β are structurally identical** under parameter mapping
    θ_w ↦ θ_wilt, θ_c ↦ θ_ref -/
theorem ch2_ch7_equivalence (θ θ_w θ_c : ℝ) :
    beta_ch2 θ θ_w θ_c = beta_ch7 θ θ_w θ_c := by
  unfold beta_ch2 beta_ch7
  rfl

/-- OWUS piecewise-linear stress (from Ch5) -/
def beta_OWUS (s s_w s_star f_ww : ℝ) : ℝ :=
  if s ≤ s_w then 0
  else if s_star ≤ s then f_ww
  else f_ww * (s - s_w) / (s_star - s_w)

/-- **OWUS with f_ww = 1 matches the simple linear β**
    This proves the two frameworks are consistent. -/
theorem OWUS_degenerates_to_linear (s s_w s_star : ℝ) :
    beta_OWUS s s_w s_star 1 = beta_ch2 s s_w s_star := by
  unfold beta_OWUS beta_ch2
  split_ifs
  · rfl
  · rfl
  · ring

/-- OWUS with f_ww = 0 produces zero stress everywhere -/
theorem OWUS_zero_capacity (s s_w s_star : ℝ) :
    beta_OWUS s s_w s_star 0 = 0 := by
  unfold beta_OWUS
  split_ifs <;> ring

/-- Scaling property: OWUS β scales linearly with f_ww -/
theorem OWUS_scales (s s_w s_star f_ww₁ f_ww₂ : ℝ)
    (_hws : s_w < s_star) (h : s_w < s) (h' : s < s_star) :
    beta_OWUS s s_w s_star (f_ww₁ * f_ww₂) =
    f_ww₁ * beta_OWUS s s_w s_star f_ww₂ := by
  unfold beta_OWUS
  split_ifs with h1 h2
  · linarith
  · linarith
  · ring

end
end ThesisProofs.Ch07.Consistency
