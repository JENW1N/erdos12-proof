import Mathlib

/-! Independent three-question statement template. Deliberately unproved; never imported by the proof. -/

namespace PrizeTarget

theorem all_parts :
  (∃ A : Set ℕ, (A.Infinite ∧ ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
        a ∣ b + c → a < b → a < c → b = c) ∧
      (0 : ℝ) < Filter.atTop.liminf
        (fun N => (A ∩ Set.Icc 1 N).ncard / (N : ℝ).sqrt)) ∧
  (¬ ∃ c > (0 : ℝ), ∀ A : Set ℕ, (A.Infinite ∧ ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
        a ∣ b + c → a < b → a < c → b = c) →
      {N : ℕ | (A ∩ Set.Icc 1 N).ncard < (N : ℝ) ^ (1 - c)}.Infinite) ∧
  (∀ A : Set ℕ, (A.Infinite ∧ ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
        a ∣ b + c → a < b → a < c → b = c) → Summable (fun n : A => (1 / n : ℝ))) := by
  sorry

end PrizeTarget
