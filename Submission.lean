import Erdos12AllParts

/-! Proof of the independently stated three-question target. -/

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
  exact Erdos12AllParts.all_parts

end PrizeTarget

#print axioms PrizeTarget.all_parts
