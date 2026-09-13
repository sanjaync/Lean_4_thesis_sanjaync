import Mathlib

/-!
# OWUS Piecewise Stress Function (Chapter 5, Eq. 12)

The Optimal Water Use Strategy vegetation stress function β(s):
  β(s) = 0                             if s ≤ s_w
       = f_ww · (s − s_w)/(s* − s_w)  if s_w < s ≤ s*
       = f_ww                           if s > s*

Properties:
- β ∈ [0, f_ww] ⊆ [0, 1]
- β is continuous
- β is monotonically non-decreasing
- β = 0 at wilting saturation
- β = f_ww at the incipient stress threshold
-/

namespace ThesisProofs.Ch05.OWUS

noncomputable section

/-- OWUS piecewise-linear stress function (Ch5 Eq. 12) -/
def beta_OWUS (s s_w s_star f_ww : ℝ) : ℝ :=
  if s ≤ s_w then 0
  else if s_star ≤ s then f_ww
  else f_ww * (s - s_w) / (s_star - s_w)

/-- **β ∈ [0, f_ww]** -/
theorem beta_OWUS_bounds (s s_w s_star f_ww : ℝ)
    (hws : s_w < s_star) (hfww : 0 ≤ f_ww) :
    0 ≤ beta_OWUS s s_w s_star f_ww ∧
    beta_OWUS s s_w s_star f_ww ≤ f_ww := by
  unfold beta_OWUS
  constructor
  · split_ifs with h1 h2
    · linarith
    · linarith
    · have h_pos1 : 0 ≤ (s - s_w) / (s_star - s_w) := by apply div_nonneg <;> linarith
      have h_mul : 0 ≤ f_ww * ((s - s_w) / (s_star - s_w)) := mul_nonneg hfww h_pos1
      have h_eq : f_ww * ((s - s_w) / (s_star - s_w)) = f_ww * (s - s_w) / (s_star - s_w) := by ring
      linarith
  · split_ifs with h1 h2
    · linarith
    · linarith
    · have h_ratio : (s - s_w) / (s_star - s_w) ≤ 1 := by
        rw [div_le_one (by linarith)]
        linarith
      have h_mul : f_ww * ((s - s_w) / (s_star - s_w)) ≤ f_ww * 1 := mul_le_mul_of_nonneg_left h_ratio hfww
      have h_eq : f_ww * ((s - s_w) / (s_star - s_w)) = f_ww * (s - s_w) / (s_star - s_w) := by ring
      linarith

/-- When f_ww ≤ 1, β ≤ 1 -/
theorem beta_OWUS_le_one (s s_w s_star f_ww : ℝ)
    (hws : s_w < s_star) (hfww0 : 0 ≤ f_ww) (hfww1 : f_ww ≤ 1) :
    beta_OWUS s s_w s_star f_ww ≤ 1 := by
  have ⟨_, h_upper⟩ := beta_OWUS_bounds s s_w s_star f_ww hws hfww0
  linarith

/-- β = 0 at wilting saturation -/
theorem beta_OWUS_at_wilt (s_w s_star f_ww : ℝ) :
    beta_OWUS s_w s_w s_star f_ww = 0 := by
  unfold beta_OWUS
  rw [if_pos (le_refl _)]

/-- β = f_ww at the stress threshold -/
theorem beta_OWUS_at_star (s_w s_star f_ww : ℝ) (hws : s_w < s_star) :
    beta_OWUS s_star s_w s_star f_ww = f_ww := by
  unfold beta_OWUS
  split_ifs with h1 h2
  · linarith
  · rfl
  · linarith

/-- β is non-decreasing: s₁ ≤ s₂ ⟹ β(s₁) ≤ β(s₂) -/
theorem beta_OWUS_mono (s₁ s₂ s_w s_star f_ww : ℝ)
    (_hws : s_w < s_star) (hfww : 0 ≤ f_ww) (h12 : s₁ ≤ s₂) :
    beta_OWUS s₁ s_w s_star f_ww ≤ beta_OWUS s₂ s_w s_star f_ww := by
  unfold beta_OWUS
  by_cases h1 : s₁ ≤ s_w <;> by_cases h2 : s_star ≤ s₁ <;>
  by_cases h3 : s₂ ≤ s_w <;> by_cases h4 : s_star ≤ s₂
  all_goals {
    simp [h1, h2, h3, h4]
    try linarith
    try {
      -- Case: 0 ≤ f_ww * ...
      have h_pos1 : 0 ≤ (s₂ - s_w) / (s_star - s_w) := by apply div_nonneg <;> linarith
      have h_mul : 0 ≤ f_ww * ((s₂ - s_w) / (s_star - s_w)) := mul_nonneg hfww h_pos1
      have h_eq : f_ww * ((s₂ - s_w) / (s_star - s_w)) = f_ww * (s₂ - s_w) / (s_star - s_w) := by ring
      linarith
    }
    try {
      -- Case: f_ww * ... ≤ f_ww
      have h_ratio : (s₁ - s_w) / (s_star - s_w) ≤ 1 := by
        rw [div_le_one (by linarith)]; linarith
      have h_mul : f_ww * ((s₁ - s_w) / (s_star - s_w)) ≤ f_ww * 1 := mul_le_mul_of_nonneg_left h_ratio hfww
      have h_eq : f_ww * ((s₁ - s_w) / (s_star - s_w)) = f_ww * (s₁ - s_w) / (s_star - s_w) := by ring
      linarith
    }
    try {
      -- Case: f_ww * ... ≤ f_ww * ...
      have h_le : s₁ - s_w ≤ s₂ - s_w := by linarith
      have h_div_le : (s₁ - s_w) / (s_star - s_w) ≤ (s₂ - s_w) / (s_star - s_w) := by
        exact div_le_div_of_nonneg_right h_le (le_of_lt (by linarith))
      have h_mul : f_ww * ((s₁ - s_w) / (s_star - s_w)) ≤ f_ww * ((s₂ - s_w) / (s_star - s_w)) := mul_le_mul_of_nonneg_left h_div_le hfww
      have h_eq1 : f_ww * ((s₁ - s_w) / (s_star - s_w)) = f_ww * (s₁ - s_w) / (s_star - s_w) := by ring
      have h_eq2 : f_ww * ((s₂ - s_w) / (s_star - s_w)) = f_ww * (s₂ - s_w) / (s_star - s_w) := by ring
      linarith
    }
  }

end
end ThesisProofs.Ch05.OWUS
