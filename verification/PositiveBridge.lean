import Erdos12AllParts

/-! Audit-only bridge from the natural-number formulation to positive integers. -/
namespace PositiveAudit

def Positive (A : Set ℕ) : Prop := ∀ n ∈ A, 0 < n

theorem delete_zero_good {A : Set ℕ} (hA : Erdos12AllParts.IsGood A) :
    Erdos12AllParts.IsGood (A \ {0}) := by
  refine ⟨hA.1.sdiff (Set.finite_singleton 0), ?_⟩
  intro a ha b hb c hc hd hab hac
  exact hA.2 ha.1 hb.1 hc.1 hd hab hac

theorem delete_zero_positive (A : Set ℕ) : Positive (A \ {0}) := by
  intro n hn
  have hn0 : n ≠ 0 := by simpa using hn.2
  omega

theorem delete_zero_interval (A : Set ℕ) (N : ℕ) :
    (A \ {0}) ∩ Set.Icc 1 N = A ∩ Set.Icc 1 N := by
  ext n
  constructor
  · rintro ⟨⟨ha, _⟩, hN⟩
    exact ⟨ha, hN⟩
  · rintro ⟨ha, hN⟩
    refine ⟨⟨ha, ?_⟩, hN⟩
    have hn : 1 ≤ n := hN.1
    simp only [Set.mem_singleton_iff]
    omega

theorem part_i_positive :
    ∃ A : Set ℕ, Erdos12AllParts.IsGood A ∧ Positive A ∧
      (0 : ℝ) < Filter.atTop.liminf
        (fun N => (A ∩ Set.Icc 1 N).ncard / (N : ℝ).sqrt) := by
  obtain ⟨A, hA, hlim⟩ := Erdos12AllParts.part_i
  refine ⟨A \ {0}, delete_zero_good hA, delete_zero_positive A, ?_⟩
  simpa only [delete_zero_interval] using hlim

theorem part_ii_positive :
    ¬ ∃ c > (0 : ℝ), ∀ A : Set ℕ, Erdos12AllParts.IsGood A → Positive A →
      {N : ℕ | (A ∩ Set.Icc 1 N).ncard < (N : ℝ) ^ (1 - c)}.Infinite := by
  rintro ⟨c, hc, hall⟩
  apply Erdos12AllParts.part_ii
  refine ⟨c, hc, ?_⟩
  intro A hA
  have h := hall (A \ {0}) (delete_zero_good hA) (delete_zero_positive A)
  simpa only [delete_zero_interval] using h

#print axioms part_i_positive
#print axioms part_ii_positive
end PositiveAudit
