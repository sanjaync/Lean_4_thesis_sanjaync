import Mathlib

/-!
# Plant Water-Use Optimality Criterion (Chapter 5, Eq. 21)

  ε = (1 − ⟨θ⟩) · ⟨T⟩/⟨P⟩

where:
- ⟨θ⟩ ∈ [0,1] is the mean dynamic water stress
- ⟨T⟩ is mean transpiration
- ⟨P⟩ is mean precipitation

Properties:
- ε ∈ [0, 1] under physical constraints
- ε = 0 when fully stressed (⟨θ⟩ = 1)
- ε = 0 when no transpiration
-/

namespace ThesisProofs.Ch05.Optimality

noncomputable section

/-- Plant water-use performance metric (Ch5 Eq. 21) -/
def epsilon (θ_mean T_mean P_mean : ℝ) : ℝ :=
  (1 - θ_mean) * (T_mean / P_mean)

/-- **ε ∈ [0, 1]** under physical constraints -/
theorem epsilon_bounds (θ_mean T_mean P_mean : ℝ)
    (hθ0 : 0 ≤ θ_mean) (hθ1 : θ_mean ≤ 1)
    (hT : 0 ≤ T_mean) (hP : 0 < P_mean) (hTP : T_mean ≤ P_mean) :
    0 ≤ epsilon θ_mean T_mean P_mean ∧
    epsilon θ_mean T_mean P_mean ≤ 1 := by
  unfold epsilon
  constructor
  · apply mul_nonneg
    · linarith
    · exact div_nonneg hT (le_of_lt hP)
  · calc (1 - θ_mean) * (T_mean / P_mean)
        ≤ 1 * (T_mean / P_mean) := by
          nlinarith [div_nonneg hT (le_of_lt hP)]
      _ = T_mean / P_mean := by ring
      _ ≤ 1 := by rwa [div_le_one hP]

/-- Performance is zero when plant is fully stressed -/
theorem epsilon_full_stress (T_mean P_mean : ℝ) :
    epsilon 1 T_mean P_mean = 0 := by
  unfold epsilon; ring

/-- Performance is zero when there is no transpiration -/
theorem epsilon_no_transpiration (θ_mean P_mean : ℝ) :
    epsilon θ_mean 0 P_mean = 0 := by
  unfold epsilon; simp

/-- ε is monotonically decreasing in stress -/
theorem epsilon_decreasing_in_stress (θ₁ θ₂ T_mean P_mean : ℝ)
    (hT : 0 ≤ T_mean) (hP : 0 < P_mean) (h12 : θ₁ ≤ θ₂) :
    epsilon θ₂ T_mean P_mean ≤ epsilon θ₁ T_mean P_mean := by
  unfold epsilon
  apply mul_le_mul_of_nonneg_right _ (div_nonneg hT (le_of_lt hP))
  linarith

end
end ThesisProofs.Ch05.Optimality
