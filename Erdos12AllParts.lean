import Mathlib

/-!
# All three numbered parts of Erdős Problem 12

This file imports only Mathlib. The formal endpoints are
Erdos12AllParts.part_i, .part_ii, .part_iii, and .all_parts.
The stronger .parameterwise_dense and .uniform_reciprocal_bound are also checked.

Parts (i) and (ii): prior results of AlphaProof Nexus / Google DeepMind,
reported by George Tsoukalas, Anton Kovsharov, Sergey Shirobokov et al.,
Advancing Mathematics Research with AI-Driven Formal Proof Search (2026),
arXiv:2605.22763v2, Appendix B.4.
The embedded source is adapted from Google DeepMind's Apache-2.0 release:
https://github.com/google-deepmind/alphaproof-nexus-results
commit 0647711a71183c1ea492ad60860776617ce1ea88,
APNOutputs/ErdosProblems/erdos_12.parts.i.lean and erdos_12.parts.ii.lean.
Copyright 2025 Google LLC. Original notices are retained in each source block.
Changes: namespaces isolated, redundant imports/options removed, a renamed
Mathlib image-cardinality lemma updated, and the interval-residue counting
proof expanded for compatibility with the pinned Mathlib version.

Part (iii): the supplied proof project and manuscript by Will Howe,
Grant Huffman, Jensen Kohlmeyer, and Liam Kruer; AI assistance acknowledged
in the manuscript. Its 201-module import closure is embedded here.
The Euler--Maclaurin and Mertens formalizations originate in
AlexKontorovich/PrimeNumberTheoremAnd, commit
c6c73610b406689c4b58325cbe1342ecca25d755, obtained via
lixiang90/chen_theorem, commit 11dcca8fc3ab340358503278c46d72aef072a6e7.
The vendored large-sieve development is from subfish-zhou/goldbach-lean,
commit 9d4c3a4010d42aedd9e7231bf94386019cfffccc.
These components are recorded as Apache-2.0 in the supplied provenance.
Original notices and attributions are retained in their source blocks.

Checked environment: Lean 4.35.0-rc2; Mathlib
065356127b1dc0016f66b7283ce0ce2c4055aa55.
No imported Formal Conjectures statement or admitted catalog proof is used.
-/

open scoped Classical


/- BEGIN SOURCE: Erdos12/Basic.lean -/
section
/-
# Property P and its elementary invariances

The convention permits equal larger summands, in which case Property P forces
their equality. It excludes three distinct elements with the least dividing
the sum of the other two. Zero is allowed in the ambient natural-number set.
-/

namespace Erdos12Proof

def PropertyP (A : Set ℕ) : Prop :=
  ∀ ⦃a⦄, a ∈ A → ∀ ⦃b⦄, b ∈ A → ∀ ⦃c⦄, c ∈ A →
    a ∣ b + c → a < b → a < c → b = c

def Primitive (A : Set ℕ) : Prop :=
  ∀ ⦃a⦄, a ∈ A → ∀ ⦃b⦄, b ∈ A → a ∣ b → a = b

def Positive (A : Set ℕ) : Prop := ∀ ⦃a⦄, a ∈ A → 0 < a

abbrev IsGood (A : Set ℕ) : Prop := A.Infinite ∧ PropertyP A

noncomputable def harmonic (B : Finset ℕ) : ℝ := ∑ a ∈ B, (1 / a : ℝ)

theorem PropertyP.mono {A B : Set ℕ} (hA : PropertyP A) (hBA : B ⊆ A) :
    PropertyP B := by
  intro a ha b hb c hc hdiv hab hac
  exact hA (hBA ha) (hBA hb) (hBA hc) hdiv hab hac

theorem Primitive.mono {A B : Set ℕ} (hA : Primitive A) (hBA : B ⊆ A) :
    Primitive B := by
  intro a ha b hb hdiv
  exact hA (hBA ha) (hBA hb) hdiv

theorem PropertyP.dilate {A : Set ℕ} (hA : PropertyP A) {d : ℕ} (hd : 0 < d) :
    PropertyP ((fun n => d * n) '' A) := by
  rintro a ⟨a', ha', rfl⟩ b ⟨b', hb', rfl⟩ c ⟨c', hc', rfl⟩ hdiv hab hac
  have hdiv' : a' ∣ b' + c' := by
    rw [← Nat.mul_add, Nat.mul_dvd_mul_iff_left hd] at hdiv
    exact hdiv
  have heq := hA ha' hb' hc' hdiv'
    ((Nat.mul_lt_mul_left hd).mp hab) ((Nat.mul_lt_mul_left hd).mp hac)
  rw [heq]

theorem PropertyP.of_dilate {A : Set ℕ} {d : ℕ} (hd : 0 < d)
    (hA : PropertyP ((fun n => d * n) '' A)) : PropertyP A := by
  intro a ha b hb c hc hdiv hab hac
  have heq : d * b = d * c := hA ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩
    (by simpa only [Nat.mul_add] using Nat.mul_dvd_mul_left d hdiv)
    ((Nat.mul_lt_mul_left hd).mpr hab) ((Nat.mul_lt_mul_left hd).mpr hac)
  exact Nat.eq_of_mul_eq_mul_left hd heq

theorem Primitive.of_dilate {A : Set ℕ} {d : ℕ} (hd : 0 < d)
    (hA : Primitive ((fun n => d * n) '' A)) : Primitive A := by
  intro a ha b hb hdiv
  exact Nat.eq_of_mul_eq_mul_left hd
    (hA ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ (Nat.mul_dvd_mul_left d hdiv))

theorem PropertyP.unique_larger_multiple {A : Set ℕ} (hA : PropertyP A)
    {a b c : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hab : a < b) (hac : a < c) (hdivb : a ∣ b) (hdivc : a ∣ c) : b = c :=
  hA ha hb hc (dvd_add hdivb hdivc) hab hac

theorem harmonic_nonneg (B : Finset ℕ) : 0 ≤ harmonic B := by
  exact Finset.sum_nonneg (fun a _ => by positivity)

theorem harmonic_mono {B C : Finset ℕ} (hBC : B ⊆ C) : harmonic B ≤ harmonic C := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hBC (fun _ _ _ => by positivity)

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/FiniteMean.lean -/
section
/- # Uniform means on finite product spaces -/

namespace Erdos12Proof

section Field

variable {K : Type*} [Field K]

noncomputable def finiteMean {Ω : Type*} [Fintype Ω] (f : Ω → K) : K :=
  (∑ x, f x) / Fintype.card Ω

theorem finiteMean_const [CharZero K] {Ω : Type*} [Fintype Ω] [Nonempty Ω] (c : K) :
    finiteMean (fun _ : Ω => c) = c := by
  unfold finiteMean
  simp [Fintype.card_ne_zero]

theorem finiteMean_zero {Ω : Type*} [Fintype Ω] :
    finiteMean (fun _ : Ω => (0 : K)) = 0 := by
  simp [finiteMean]

theorem finiteMean_add {Ω : Type*} [Fintype Ω] (f g : Ω → K) :
    finiteMean (fun x => f x + g x) = finiteMean f + finiteMean g := by
  simp only [finiteMean, Finset.sum_add_distrib, add_div]

theorem finiteMean_mul_const {Ω : Type*} [Fintype Ω] (f : Ω → K) (c : K) :
    finiteMean (fun x => f x * c) = finiteMean f * c := by
  simp only [finiteMean, ← Finset.sum_mul]
  ring

theorem finiteMean_const_mul {Ω : Type*} [Fintype Ω] (c : K) (f : Ω → K) :
    finiteMean (fun x => c * f x) = c * finiteMean f := by
  simp only [finiteMean, ← Finset.mul_sum]
  ring

theorem finiteMean_sum {Ω ι : Type*} [Fintype Ω] (s : Finset ι) (f : ι → Ω → K) :
    finiteMean (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, finiteMean (f i) := by
  simp only [finiteMean, Finset.sum_div]
  rw [Finset.sum_comm]

theorem finiteMean_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (f : ∀ i, Ω i → K) :
    finiteMean (fun x : ∀ i, Ω i => ∏ i, f i (x i)) = ∏ i, finiteMean (f i) := by
  unfold finiteMean
  rw [← Fintype.prod_sum, Finset.prod_div_distrib, Fintype.card_pi]
  simp only [Nat.cast_prod]

end Field

theorem finiteMean_nonneg {Ω : Type*} [Fintype Ω] {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ finiteMean f := by
  exact div_nonneg (Finset.sum_nonneg (fun x _ => hf x)) (Nat.cast_nonneg _)

theorem finiteMean_mono {Ω : Type*} [Fintype Ω] {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) :
    finiteMean f ≤ finiteMean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => h x)) (Nat.cast_nonneg _)

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/FiniteProductWeights.lean -/
section
/- # Explicit probability weights on finite product spaces -/

namespace Erdos12Proof

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Ω : ι → Type*} [∀ i, Fintype (Ω i)]

noncomputable def productWeight (w : ∀ i, Ω i → ℝ) (ω : ∀ i, Ω i) : ℝ :=
  ∏ i, w i (ω i)

omit [DecidableEq ι] [∀ i, Fintype (Ω i)] in
theorem productWeight_nonneg (w : ∀ i, Ω i → ℝ) (hw : ∀ i x, 0 ≤ w i x) (ω : ∀ i, Ω i) :
    0 ≤ productWeight w ω := Finset.prod_nonneg (fun i _ => hw i (ω i))

theorem productWeight_sum (w : ∀ i, Ω i → ℝ) :
    (∑ ω : ∀ i, Ω i, productWeight w ω) = ∏ i, ∑ x, w i x := by
  unfold productWeight
  rw [← Fintype.prod_sum]

theorem productWeight_mass (w : ∀ i, Ω i → ℝ) (hw : ∀ i, (∑ x, w i x) = 1) :
    (∑ ω : ∀ i, Ω i, productWeight w ω) = 1 := by
  rw [productWeight_sum]
  simp only [hw, Finset.prod_const_one]

theorem productWeight_factorization (w f : ∀ i, Ω i → ℝ) :
    (∑ ω : ∀ i, Ω i, productWeight w ω * ∏ i, f i (ω i)) =
      ∏ i, ∑ x, w i x * f i x := by
  simp only [productWeight, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => w i x * f i x)).symm

theorem productWeight_restricted_sum (w : ∀ i, Ω i → ℝ) (P : ∀ i, Ω i → Prop)
    [∀ i, DecidablePred (P i)] :
    (∑ ω : ∀ i, Ω i, if ∀ i, P i (ω i) then productWeight w ω else 0) =
      ∏ i, ∑ x, if P i x then w i x else 0 := by
  classical
  have hpoint (ω : ∀ i, Ω i) :
      (if ∀ i, P i (ω i) then productWeight w ω else 0) =
        ∏ i, if P i (ω i) then w i (ω i) else 0 := by
    by_cases h : ∀ i, P i (ω i)
    · rw [ite_eq_left h]
      unfold productWeight
      apply Finset.prod_congr rfl
      intro i _
      rw [ite_eq_left (h i)]
    · rw [ite_eq_right h]
      obtain ⟨i, hi⟩ := not_forall.mp h
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
  simp only [hpoint]
  exact (Fintype.prod_sum (fun i x => if P i x then w i x else 0)).symm

noncomputable def weightedSum {X : Type*} [Fintype X] (w f : X → ℝ) : ℝ :=
  ∑ x, w x * f x

theorem weightedSum_mono {X : Type*} [Fintype X] (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    {f g : X → ℝ} (hfg : ∀ x, f x ≤ g x) : weightedSum w f ≤ weightedSum w g :=
  Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hfg x) (hw x))

theorem weightedSum_finite_sum {X κ : Type*} [Fintype X] (w : X → ℝ)
    (S : Finset κ) (f : κ → X → ℝ) :
    weightedSum w (fun x => ∑ i ∈ S, f i x) = ∑ i ∈ S, weightedSum w (f i) := by
  simp only [weightedSum, Finset.mul_sum]
  rw [Finset.sum_comm]

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/FiniteCoordinateWeights.lean -/
section
/- # Conditional factorization at one finite product coordinate -/

namespace Erdos12Proof

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Ω : ι → Type*} [∀ i, Fintype (Ω i)]

omit [∀ i, Fintype (Ω i)] in
theorem productWeight_splitAt (w : ∀ i, Ω i → ℝ) (i : ι) (x : Ω i)
    (r : ∀ j : {j // j ≠ i}, Ω j) :
    productWeight w ((Equiv.piSplitAt i Ω).symm (x, r)) =
      w i x * productWeight (fun j : {j // j ≠ i} => w j.val) r := by
  unfold productWeight
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
  have hcoord : (Equiv.piSplitAt i Ω).symm (x, r) i = x := by simp [Equiv.piSplitAt]
  rw [hcoord]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  simp [Equiv.piSplitAt, j.property]

theorem weightedSum_splitAt (w : ∀ i, Ω i → ℝ) (F : (∀ i, Ω i) → ℝ) (i : ι) :
    weightedSum (productWeight w) F = ∑ x : Ω i, w i x *
      ∑ r : (∀ j : {j // j ≠ i}, Ω j),
        productWeight (fun j : {j // j ≠ i} => w j.val) r * F ((Equiv.piSplitAt i Ω).symm (x, r)) := by
  classical
  unfold weightedSum
  rw [← (Equiv.piSplitAt i Ω).symm.sum_comp
    (fun ω => productWeight w ω * F ω), Fintype.sum_prod_type]
  simp only [productWeight_splitAt, Finset.mul_sum, mul_assoc]

theorem weightedSum_coordinate_pairing (w : ∀ i, Ω i → ℝ) (i : ι) [Nonempty (Ω i)]
    (hw : (∑ x, w i x) = 1) (g : Ω i → ℝ) (F : (∀ i, Ω i) → ℝ)
    (hF : ∀ ω x, F (Function.update ω i x) = F ω) :
    weightedSum (productWeight w) (fun ω => g (ω i) * F ω) =
      (∑ x, w i x * g x) * weightedSum (productWeight w) F := by
  classical
  let x₀ : Ω i := Classical.choice ‹Nonempty (Ω i)›
  let e := Equiv.piSplitAt i Ω
  let V := ∑ r : (∀ j : {j // j ≠ i}, Ω j),
    productWeight (fun j : {j // j ≠ i} => w j.val) r * F (e.symm (x₀, r))
  have hcoord (x : Ω i) (r : ∀ j : {j // j ≠ i}, Ω j) : e.symm (x, r) i = x := by
    simp [e, Equiv.piSplitAt]
  have hsame (x : Ω i) (r : ∀ j : {j // j ≠ i}, Ω j) : F (e.symm (x, r)) = F (e.symm (x₀, r)) := by
    have heq : e.symm (x, r) = Function.update (e.symm (x₀, r)) i x := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [hcoord]
      · simp [e, Equiv.piSplitAt, hji]
    rw [heq, hF]
  have hbase : weightedSum (productWeight w) F = V := by
    rw [weightedSum_splitAt w F i]
    change (∑ x : Ω i, w i x * ∑ r, productWeight (fun j : {j // j ≠ i} => w j.val) r *
      F (e.symm (x, r))) = V
    simp_rw [hsame]
    change (∑ x : Ω i, w i x * V) = V
    rw [← Finset.sum_mul, hw, one_mul]
  rw [hbase, weightedSum_splitAt w (fun ω => g (ω i) * F ω) i]
  change (∑ x : Ω i, w i x * ∑ r, productWeight (fun j : {j // j ≠ i} => w j.val) r *
    (g (e.symm (x, r) i) * F (e.symm (x, r)))) = _
  simp_rw [hcoord, hsame]
  calc
    _ = ∑ x : Ω i, (w i x * g x) * V := by
      apply Finset.sum_congr rfl
      intro x _
      dsimp only [V]
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = _ := (Finset.sum_mul _ _ _).symm

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/GeometricWeights.lean -/
section
/-
# Exact geometric weights used by the prefix argument

The parameter is the prime value itself. The following identities hold for
every real parameter greater than one, so primality is unnecessary here.
-/

namespace Erdos12Proof

noncomputable def geometricWeight (p : ℝ) (j : ℕ) : ℝ :=
  (1 - 1 / p) * (1 / p) ^ j

theorem geometric_ratio_bounds {p : ℝ} (hp : 1 < p) :
    0 ≤ 1 / p ∧ 1 / p < 1 := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  exact ⟨le_of_lt (one_div_pos.mpr hp0), (div_lt_one hp0).mpr hp⟩

theorem geometricWeight_nonneg {p : ℝ} (hp : 1 < p) (j : ℕ) :
    0 ≤ geometricWeight p j := by
  obtain ⟨h0, h1⟩ := geometric_ratio_bounds hp
  exact mul_nonneg (sub_nonneg.mpr h1.le) (pow_nonneg h0 j)

theorem hasSum_geometricWeight {p : ℝ} (hp : 1 < p) :
    HasSum (geometricWeight p) 1 := by
  obtain ⟨h0, h1⟩ := geometric_ratio_bounds hp
  have hs := (hasSum_geometric_of_lt_one h0 h1).mul_left (1 - 1 / p)
  convert hs using 1
  · rfl
  · have hne : 1 - 1 / p ≠ 0 := ne_of_gt (sub_pos.mpr h1)
    exact (mul_inv_cancel₀ hne).symm

theorem hasSum_geometricWeight_tail {p : ℝ} (hp : 1 < p) (k : ℕ) :
    HasSum (fun j => geometricWeight p (j + k)) ((1 / p) ^ k) := by
  have hs := (hasSum_geometricWeight hp).mul_right ((1 / p) ^ k)
  convert hs using 1
  · funext j
    simp only [geometricWeight, pow_add]
    ring
  · ring

theorem hasSum_repeated_copy_cost {p : ℝ} (hp : 1 < p) :
    HasSum (fun j : ℕ => (j : ℝ) * geometricWeight p (j + 1)) (1 / (p * (p - 1))) := by
  obtain ⟨h0, h1⟩ := geometric_ratio_bounds hp
  have hnorm : ‖1 / p‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg h0]
  have hs := (hasSum_descFactorial_mul_geometric_of_norm_lt_one
    (𝕜 := ℝ) 1 hnorm).mul_left ((1 - 1 / p) * (1 / p))
  convert hs using 1
  · funext j
    simp only [geometricWeight, Nat.descFactorial_one, pow_succ]
    ring
  · norm_num
    have hp0 : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
    have hp1 : p - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hp)
    field_simp

theorem hasSum_stage_budget :
    HasSum (fun k : ℕ => (1 / 2 : ℝ) ^ k * (1 + (k : ℝ))) 4 := by
  have h0 : ‖(1 / 2 : ℝ)‖ < 1 := by norm_num
  have hs0 := hasSum_geometric_of_norm_lt_one h0
  have hs1 := hasSum_descFactorial_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1 h0
  have hs := hs0.add hs1
  convert hs using 1
  · funext k
    simp only [Nat.descFactorial_one]
    ring
  · norm_num

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/TruncatedGeometric.lean -/
section
/- # Finite geometric distributions with the tail collected at the last value -/

namespace Erdos12Proof

theorem sum_geometricWeight_range (p : ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range N, geometricWeight p j) = 1 - (1 / p) ^ N := by
  have h := geom_sum_mul (1 / p : ℝ) N
  unfold geometricWeight
  rw [← Finset.mul_sum]
  nlinarith

noncomputable def truncatedGeometricWeight (p : ℝ) (cap : ℕ) (j : Fin (cap + 1)) : ℝ :=
  if j.val < cap then geometricWeight p j.val else (1 / p) ^ cap

theorem truncatedGeometricWeight_nonneg {p : ℝ} (hp : 1 < p) (cap : ℕ) (j : Fin (cap + 1)) :
    0 ≤ truncatedGeometricWeight p cap j := by
  unfold truncatedGeometricWeight
  split_ifs
  · exact geometricWeight_nonneg hp _
  · exact pow_nonneg (geometric_ratio_bounds hp).1 _

theorem truncatedGeometricWeight_below {cap : ℕ} (p : ℝ) (j : Fin (cap + 1)) (hj : j.val < cap) :
    truncatedGeometricWeight p cap j = geometricWeight p j.val := by
  exact ite_eq_left hj

theorem truncatedGeometricWeight_last (p : ℝ) (cap : ℕ) :
    truncatedGeometricWeight p cap (Fin.last cap) = (1 / p) ^ cap := by
  simp only [truncatedGeometricWeight, Fin.val_last, lt_self_iff_false, ite_false]

theorem truncatedGeometricWeight_sum (p : ℝ) (cap : ℕ) :
    (∑ j : Fin (cap + 1), truncatedGeometricWeight p cap j) = 1 := by
  rw [Fin.sum_univ_castSucc]
  have hbelow (j : Fin cap) : truncatedGeometricWeight p cap j.castSucc = geometricWeight p j.val :=
    truncatedGeometricWeight_below p j.castSucc j.isLt
  simp only [hbelow, truncatedGeometricWeight_last]
  rw [Fin.sum_univ_eq_sum_range, sum_geometricWeight_range]
  ring

theorem truncatedGeometricWeight_tail (p : ℝ) (cap a : ℕ) (ha : a ≤ cap) :
    (∑ j : Fin (cap + 1), if a ≤ j.val then truncatedGeometricWeight p cap j else 0) =
      (1 / p) ^ a := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin (cap + 1)))
    (fun j => j.val < a) (truncatedGeometricWeight p cap)
  have hlow : (∑ j ∈ (Finset.univ : Finset (Fin (cap + 1))).filter (fun j => j.val < a),
      truncatedGeometricWeight p cap j) = 1 - (1 / p) ^ a := by
    calc
      _ = ∑ j ∈ Finset.range a, geometricWeight p j := by
        apply Finset.sum_bij (fun j _ => j.val)
        · intro j hj
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
        · intro i _ j _ hij
          exact Fin.ext hij
        · intro j hj
          refine ⟨⟨j, by have := Finset.mem_range.mp hj; omega⟩, ?_, rfl⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_range.mp hj⟩
        · intro j hj
          exact truncatedGeometricWeight_below p j ((Finset.mem_filter.mp hj).2.trans_le ha)
      _ = _ := sum_geometricWeight_range p a
  rw [hlow, truncatedGeometricWeight_sum] at hsplit
  have hhigh : (∑ j : Fin (cap + 1), if a ≤ j.val then truncatedGeometricWeight p cap j else 0) =
      ∑ j ∈ (Finset.univ : Finset (Fin (cap + 1))).filter (fun j => ¬j.val < a),
        truncatedGeometricWeight p cap j := by
    rw [Finset.sum_filter]
    simp only [not_lt]
  rw [hhigh]
  linarith

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/FiniteGeometricProbability.lean -/
section
/- # Finite geometric product probabilities and predictable-coordinate identities -/

namespace Erdos12Proof

theorem truncatedGeometricWeight_atom (p : ℝ) (cap a : ℕ) (ha : a < cap) :
    (∑ x : Fin (cap + 1), if x.val = a then truncatedGeometricWeight p cap x else 0) =
      geometricWeight p a := by
  classical
  let x : Fin (cap + 1) := ⟨a, by omega⟩
  have hcond (y : Fin (cap + 1)) : y.val = a ↔ y = x := by
    exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  simp only [hcond, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact truncatedGeometricWeight_below p x ha

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def finiteGeometricProductWeight (p : ι → ℝ) (cap : ℕ)
    (ω : ι → Fin (cap + 1)) : ℝ :=
  productWeight (fun i => truncatedGeometricWeight (p i) cap) ω

theorem finiteGeometricProductWeight_mass (p : ι → ℝ) (cap : ℕ) :
    (∑ ω : ι → Fin (cap + 1), finiteGeometricProductWeight p cap ω) = 1 :=
  productWeight_mass _ (fun i => truncatedGeometricWeight_sum (p i) cap)

omit [DecidableEq ι] in
theorem finiteGeometricProductWeight_nonneg (p : ι → ℝ) (hp : ∀ i, 1 < p i)
    (cap : ℕ) (ω : ι → Fin (cap + 1)) : 0 ≤ finiteGeometricProductWeight p cap ω :=
  productWeight_nonneg _ (fun i x => truncatedGeometricWeight_nonneg (hp i) cap x) ω

theorem finiteGeometric_tail_pairing (p : ι → ℝ) (cap : ℕ) (i : ι) (a : ℕ) (ha : a ≤ cap)
    (F : (ι → Fin (cap + 1)) → ℝ)
    (hF : ∀ ω x, F (Function.update ω i x) = F ω) :
    weightedSum (finiteGeometricProductWeight p cap)
      (fun ω => if a ≤ (ω i).val then F ω else 0) =
        (1 / p i) ^ a * weightedSum (finiteGeometricProductWeight p cap) F := by
  have h := weightedSum_coordinate_pairing (fun i => truncatedGeometricWeight (p i) cap) i
    (truncatedGeometricWeight_sum (p i) cap) (fun x => if a ≤ x.val then 1 else 0) F hF
  have hlocal : (∑ x : Fin (cap + 1), truncatedGeometricWeight (p i) cap x *
      (if a ≤ x.val then 1 else 0)) = (1 / p i) ^ a := by
    simp only [mul_ite, mul_one, mul_zero]
    exact truncatedGeometricWeight_tail (p i) cap a ha
  rw [hlocal] at h
  simpa only [weightedSum, finiteGeometricProductWeight, ite_mul, one_mul, zero_mul] using h

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/SelbergTensor.lean -/
section
/- # Orthogonal products underlying the Selberg majorant -/

namespace Erdos12Proof

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Ω : ι → Type*}

noncomputable def tensorBasis (u : ∀ i, Ω i → ℝ) (s : Finset ι) (x : ∀ i, Ω i) : ℝ :=
  ∏ i, if i ∈ s then u i (x i) else 1

noncomputable def tensorWeight (w : ι → ℝ) (s : Finset ι) : ℝ := ∏ i ∈ s, w i

theorem tensorBasis_empty (u : ∀ i, Ω i → ℝ) (x : ∀ i, Ω i) :
    tensorBasis u ∅ x = 1 := by
  simp [tensorBasis]

theorem tensorBasis_mean_product [∀ i, Fintype (Ω i)]
    (u : ∀ i, Ω i → ℝ) (s t : Finset ι) :
    finiteMean (fun x => tensorBasis u s x * tensorBasis u t x) =
      ∏ i, finiteMean (fun x => (if i ∈ s then u i x else 1) *
        (if i ∈ t then u i x else 1)) := by
  simpa only [tensorBasis, Finset.prod_mul_distrib] using
    (finiteMean_prod (fun i x => (if i ∈ s then u i x else 1) *
      (if i ∈ t then u i x else 1)))

theorem tensorBasis_orthogonal [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)]
    (u : ∀ i, Ω i → ℝ) (w : ι → ℝ)
    (hzero : ∀ i, finiteMean (u i) = 0)
    (hsquare : ∀ i, finiteMean (fun x => u i x ^ 2) = w i) (s t : Finset ι) :
    finiteMean (fun x => tensorBasis u s x * tensorBasis u t x) =
      if s = t then tensorWeight w s else 0 := by
  rw [tensorBasis_mean_product]
  by_cases hst : s = t
  · subst t
    rw [ite_eq_left rfl]
    calc
      _ = ∏ i, if i ∈ s then w i else 1 := by
        apply Finset.prod_congr rfl
        intro i _
        by_cases hi : i ∈ s
        · simpa only [ite_eq_left hi, ← pow_two] using hsquare i
        · simp only [ite_eq_right hi, one_mul, finiteMean_const]
      _ = tensorWeight w s := by simp only [Fintype.prod_ite_mem, tensorWeight]
  · rw [ite_eq_right hst]
    have hnot : ¬∀ i, i ∈ s ↔ i ∈ t := by
      intro h
      exact hst (Finset.ext h)
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    by_cases his : i ∈ s
    · have hit : i ∉ t := by
        intro ht
        exact hi (iff_of_true his ht)
      simpa only [ite_eq_left his, ite_eq_right hit, mul_one] using hzero i
    · have hit : i ∈ t := by
        by_contra ht
        exact hi (iff_of_false his ht)
      simpa only [ite_eq_right his, ite_eq_left hit, one_mul] using hzero i

noncomputable def selbergMass (w : ι → ℝ) (F : Finset (Finset ι)) : ℝ :=
  ∑ s ∈ F, tensorWeight w s

noncomputable def selbergSum (u : ∀ i, Ω i → ℝ) (F : Finset (Finset ι))
    (x : ∀ i, Ω i) : ℝ := ∑ s ∈ F, tensorBasis u s x

theorem selbergSum_mean_square [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)]
    (u : ∀ i, Ω i → ℝ) (w : ι → ℝ)
    (hzero : ∀ i, finiteMean (u i) = 0)
    (hsquare : ∀ i, finiteMean (fun x => u i x ^ 2) = w i) (F : Finset (Finset ι)) :
    finiteMean (fun x => selbergSum u F x ^ 2) = selbergMass w F := by
  calc
    _ = finiteMean (fun x => ∑ s ∈ F, ∑ t ∈ F, tensorBasis u s x * tensorBasis u t x) := by
      congr 1
      funext x
      simp only [selbergSum, pow_two, Finset.sum_mul_sum]
    _ = ∑ s ∈ F, ∑ t ∈ F,
        finiteMean (fun x => tensorBasis u s x * tensorBasis u t x) := by
      rw [finiteMean_sum]
      apply Finset.sum_congr rfl
      intro s _
      exact finiteMean_sum F _
    _ = selbergMass w F := by
      unfold selbergMass
      apply Finset.sum_congr rfl
      intro s hs
      simp_rw [tensorBasis_orthogonal u w hzero hsquare]
      simp [hs]

omit [Fintype ι] [DecidableEq ι] in
theorem selbergMass_pos (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (F : Finset (Finset ι)) (hF : ∅ ∈ F) : 0 < selbergMass w F := by
  apply lt_of_lt_of_le (show (0 : ℝ) < 1 from zero_lt_one)
  calc
    1 = tensorWeight w ∅ := by simp [tensorWeight]
    _ ≤ selbergMass w F :=
      Finset.single_le_sum (f := tensorWeight w)
        (fun s _ => Finset.prod_nonneg (fun i _ => hw i)) hF

theorem tensorBasis_on_survivor (u : ∀ i, Ω i → ℝ) (w : ι → ℝ)
    (x : ∀ i, Ω i) (hx : ∀ i, u i (x i) = w i) (s : Finset ι) :
    tensorBasis u s x = tensorWeight w s := by
  simp only [tensorBasis, hx, Fintype.prod_ite_mem, tensorWeight]

theorem selbergSum_on_survivor (u : ∀ i, Ω i → ℝ) (w : ι → ℝ)
    (x : ∀ i, Ω i) (hx : ∀ i, u i (x i) = w i) (F : Finset (Finset ι)) :
    selbergSum u F x = selbergMass w F := by
  apply Finset.sum_congr rfl
  intro s _
  exact tensorBasis_on_survivor u w x hx s

noncomputable def selbergMajorant (u : ∀ i, Ω i → ℝ) (w : ι → ℝ)
    (F : Finset (Finset ι)) (x : ∀ i, Ω i) : ℝ :=
  selbergSum u F x ^ 2 / selbergMass w F ^ 2

theorem selbergMajorant_nonneg (u : ∀ i, Ω i → ℝ) (w : ι → ℝ)
    (F : Finset (Finset ι)) (x : ∀ i, Ω i) : 0 ≤ selbergMajorant u w F x :=
  div_nonneg (sq_nonneg _) (sq_nonneg _)

theorem selbergMajorant_on_survivor (u : ∀ i, Ω i → ℝ) (w : ι → ℝ)
    (F : Finset (Finset ι)) (hF : selbergMass w F ≠ 0)
    (x : ∀ i, Ω i) (hx : ∀ i, u i (x i) = w i) : selbergMajorant u w F x = 1 := by
  unfold selbergMajorant
  rw [selbergSum_on_survivor u w x hx F]
  exact div_self (pow_ne_zero _ hF)

theorem selbergMajorant_mean [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)]
    (u : ∀ i, Ω i → ℝ) (w : ι → ℝ)
    (hzero : ∀ i, finiteMean (u i) = 0)
    (hsquare : ∀ i, finiteMean (fun x => u i x ^ 2) = w i)
    (F : Finset (Finset ι)) (hF : selbergMass w F ≠ 0) :
    finiteMean (selbergMajorant u w F) = 1 / selbergMass w F := by
  change finiteMean (fun x => selbergSum u F x ^ 2 / selbergMass w F ^ 2) = _
  simp only [div_eq_mul_inv, finiteMean_mul_const,
    selbergSum_mean_square u w hzero hsquare F]
  field_simp

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/SelbergEulerWeights.lean -/
section
/- # The finite Euler distribution used to lower-bound the sifting mass -/

namespace Erdos12Proof

variable {ι : Type*} [DecidableEq ι]

noncomputable def subsetMoment (w a : ι → ℝ) (S : Finset ι) : ℝ :=
  ∑ t ∈ S.powerset, tensorWeight w t * ∑ i ∈ t, a i

omit [DecidableEq ι] in
theorem subsetWeight_sum (w : ι → ℝ) (S : Finset ι) :
    (∑ t ∈ S.powerset, tensorWeight w t) = ∏ i ∈ S, (1 + w i) := by
  simpa only [tensorWeight] using (Finset.prod_one_add (f := w) S).symm

theorem subsetMoment_insert (w a : ι → ℝ) (S : Finset ι) {i : ι} (hi : i ∉ S) :
    subsetMoment w a (insert i S) =
      (1 + w i) * subsetMoment w a S + w i * a i * ∏ j ∈ S, (1 + w j) := by
  unfold subsetMoment
  rw [Finset.sum_powerset_insert hi]
  have hsum : (∑ t ∈ S.powerset, tensorWeight w (insert i t) * ∑ j ∈ insert i t, a j) =
      ∑ t ∈ S.powerset, w i * tensorWeight w t * (a i + ∑ j ∈ t, a j) := by
    apply Finset.sum_congr rfl
    intro t ht
    have hit : i ∉ t := fun h => hi ((Finset.mem_powerset.mp ht) h)
    simp only [tensorWeight, Finset.prod_insert hit, Finset.sum_insert hit]
  rw [hsum]
  have hterm (t : Finset ι) : w i * tensorWeight w t * (a i + ∑ j ∈ t, a j) =
      w i * a i * tensorWeight w t + w i * (tensorWeight w t * ∑ j ∈ t, a j) := by ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, subsetWeight_sum]
  ring

theorem subsetMoment_eq (w a : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (S : Finset ι) :
    subsetMoment w a S =
      (∏ i ∈ S, (1 + w i)) * ∑ i ∈ S, (w i / (1 + w i)) * a i := by
  induction S using Finset.induction_on with
  | empty => simp [subsetMoment, tensorWeight]
  | @insert i S hi ih =>
    rw [subsetMoment_insert w a S hi, ih, Finset.prod_insert hi, Finset.sum_insert hi]
    have hne : 1 + w i ≠ 0 := by have := hw i; linarith
    field_simp
    ring

theorem finite_weighted_markov {α : Type*} (S : Finset α) (w c : α → ℝ)
    (hw : ∀ x ∈ S, 0 ≤ w x) (hc : ∀ x ∈ S, 0 ≤ c x) {L : ℝ} (hL : 0 < L)
    (hmean : (∑ x ∈ S, w x * c x) ≤ (L / 2) * ∑ x ∈ S, w x) :
    (∑ x ∈ S with c x < L, w x) ≥ (1 / 2 : ℝ) * ∑ x ∈ S, w x := by
  classical
  have htail : L * (∑ x ∈ S with ¬c x < L, w x) ≤ ∑ x ∈ S, w x * c x := by
    rw [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    by_cases hbad : ¬c x < L
    · rw [ite_eq_left hbad]
      nlinarith [mul_le_mul_of_nonneg_left (le_of_not_gt hbad) (hw x hx)]
    · rw [ite_eq_right hbad, mul_zero]
      exact mul_nonneg (hw x hx) (hc x hx)
  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun x => c x < L) w
  nlinarith

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/SelbergLocal.lean -/
section
/- # The one-coordinate Selberg function and its exact first two moments -/

namespace Erdos12Proof

noncomputable def sieveLocalWeight (p : ℕ) : ℝ := 1 / ((p : ℝ) - 1)

noncomputable def sieveLocal (p : ℕ) (x : Fin p) : ℝ :=
  if x.val = 0 then -1 else sieveLocalWeight p

theorem sieveLocalWeight_pos {p : ℕ} (hp : 1 < p) : 0 < sieveLocalWeight p := by
  unfold sieveLocalWeight
  have : (1 : ℝ) < p := by exact_mod_cast hp
  positivity

theorem sieveLocalWeight_le_one {p : ℕ} (hp : 1 < p) : sieveLocalWeight p ≤ 1 := by
  unfold sieveLocalWeight
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  apply (div_le_one (by linarith : 0 < (p : ℝ) - 1)).mpr
  linarith

theorem sieveLocal_square (p : ℕ) (x : Fin p) :
    sieveLocal p x ^ 2 = sieveLocalWeight p + (sieveLocalWeight p - 1) * sieveLocal p x := by
  unfold sieveLocal
  split_ifs <;> ring

theorem sieveLocal_eq_weight {p : ℕ} {x : Fin p} (hx : x.val ≠ 0) :
    sieveLocal p x = sieveLocalWeight p := by
  simp only [sieveLocal, ite_eq_right hx]

theorem sieveLocal_sum {p : ℕ} (hp : 1 < p) : ∑ x : Fin p, sieveLocal p x = 0 := by
  let _ : NeZero p := ⟨by omega⟩
  have hzero (x : Fin p) : x.val = 0 ↔ x = 0 := by
    constructor
    · intro h
      exact Fin.ext h
    · intro h
      simp [h]
  have hform : (fun x : Fin p => sieveLocal p x) =
      fun x => sieveLocalWeight p + if x = 0 then (-1 - sieveLocalWeight p) else 0 := by
    funext x
    unfold sieveLocal
    simp only [hzero]
    split_ifs <;> ring
  rw [hform, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  unfold sieveLocalWeight
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp
    linarith
  field_simp
  ring

theorem sieveLocal_mean {p : ℕ} (hp : 1 < p) : finiteMean (sieveLocal p) = 0 := by
  simp only [finiteMean, sieveLocal_sum hp, zero_div]

theorem sieveLocal_square_mean {p : ℕ} (hp : 1 < p) :
    finiteMean (fun x => sieveLocal p x ^ 2) = sieveLocalWeight p := by
  let _ : Nonempty (Fin p) := ⟨⟨0, by omega⟩⟩
  simp only [sieveLocal_square, finiteMean_add, finiteMean_const_mul, sieveLocal_mean hp,
    finiteMean_const, mul_zero, add_zero]

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/SelbergSieve.lean -/
section
/-
# The finite Selberg majorant

Subsets of the coordinate set represent squarefree products when the moduli
are distinct primes. The identities in this module only require moduli
greater than one. The Chinese remainder identification with a cyclic group
is a separate step.
-/

namespace Erdos12Proof

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev SieveCube (m : ι → ℕ) := ∀ i, Fin (m i)

noncomputable def sieveSupport (m : ι → ℕ) (z : ℝ) : Finset (Finset ι) :=
  Finset.univ.filter (fun s => ((∏ i ∈ s, m i : ℕ) : ℝ) < z)

noncomputable def sieveMass (m : ι → ℕ) (z : ℝ) : ℝ :=
  selbergMass (fun i => sieveLocalWeight (m i)) (sieveSupport m z)

noncomputable def sieveMajorant (m : ι → ℕ) (z : ℝ) (x : SieveCube m) : ℝ :=
  selbergMajorant (fun i => sieveLocal (m i)) (fun i => sieveLocalWeight (m i))
    (sieveSupport m z) x

omit [DecidableEq ι] in
theorem sieveSupport_empty {m : ι → ℕ} {z : ℝ} (hz : 1 < z) :
    ∅ ∈ sieveSupport m z := by
  simp [sieveSupport, hz]

omit [DecidableEq ι] in
theorem sieveMass_pos {m : ι → ℕ} (hm : ∀ i, 1 < m i) {z : ℝ} (hz : 1 < z) :
    0 < sieveMass m z := by
  exact selbergMass_pos _ (fun i => (sieveLocalWeight_pos (hm i)).le)
    _ (sieveSupport_empty hz)

theorem sieveMajorant_nonneg (m : ι → ℕ) (z : ℝ) (x : SieveCube m) :
    0 ≤ sieveMajorant m z x :=
  selbergMajorant_nonneg _ _ _ _

theorem sieveMajorant_eq_one {m : ι → ℕ} (hm : ∀ i, 1 < m i) {z : ℝ} (hz : 1 < z)
    {x : SieveCube m} (hx : ∀ i, (x i).val ≠ 0) : sieveMajorant m z x = 1 := by
  apply selbergMajorant_on_survivor _ _ _ (ne_of_gt (sieveMass_pos hm hz))
  exact fun i => sieveLocal_eq_weight (hx i)

theorem sieveMajorant_mean {m : ι → ℕ} (hm : ∀ i, 1 < m i) {z : ℝ} (hz : 1 < z) :
    finiteMean (sieveMajorant m z) = 1 / sieveMass m z := by
  let _ : ∀ i, Nonempty (Fin (m i)) := fun i => ⟨⟨0, by have := hm i; omega⟩⟩
  exact selbergMajorant_mean _ _ (fun i => sieveLocal_mean (hm i))
    (fun i => sieveLocal_square_mean (hm i)) _ (ne_of_gt (sieveMass_pos hm hz))

def residueCube (m : ι → ℕ) (hm : ∀ i, 0 < m i) (n : ℕ) : SieveCube m :=
  fun i => ⟨n % m i, Nat.mod_lt n (hm i)⟩

theorem sieveMajorant_residue_eq_one {m : ι → ℕ} (hm : ∀ i, 1 < m i)
    {z : ℝ} (hz : 1 < z) {n : ℕ} (hn : ∀ i, ¬m i ∣ n) :
    sieveMajorant m z (residueCube m (fun i => Nat.zero_lt_of_lt (hm i)) n) = 1 := by
  apply sieveMajorant_eq_one hm hz
  intro i hzero
  exact hn i (Nat.dvd_of_mod_eq_zero hzero)

omit [Fintype ι] [DecidableEq ι] in
theorem residueCube_periodic (m : ι → ℕ) (hm : ∀ i, 0 < m i) {L : ℕ}
    (hL : ∀ i, m i ∣ L) (n : ℕ) : residueCube m hm (n + L) = residueCube m hm n := by
  funext i
  apply Fin.ext
  change (n + L) % m i = n % m i
  simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd (hL i)]

omit [DecidableEq ι] in
theorem sieveMass_mono {m : ι → ℕ} (hm : ∀ i, 1 < m i) {z Z : ℝ} (hzZ : z ≤ Z) :
    sieveMass m z ≤ sieveMass m Z := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro s hs
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, lt_of_lt_of_le (Finset.mem_filter.mp hs).2 hzZ⟩
  · intro s _ _
    exact Finset.prod_nonneg (fun i _ => (sieveLocalWeight_pos (hm i)).le)

omit [DecidableEq ι] in
theorem sieveSupport_downwardClosed {m : ι → ℕ} (hm : ∀ i, 1 ≤ m i) (z : ℝ) :
    ∀ s ∈ sieveSupport m z, ∀ t : Finset ι, t ⊆ s → t ∈ sieveSupport m z := by
  intro s hs t hts
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  have hprod : (∏ i ∈ t, m i) ≤ ∏ i ∈ s, m i :=
    Finset.prod_le_prod_of_subset_of_one_le hts (fun i _ _ => hm i)
  exact lt_of_le_of_lt (by exact_mod_cast hprod) (Finset.mem_filter.mp hs).2

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/SieveMassComparison.lean -/
section
/- # Comparing sieve masses after removing coordinates -/

namespace Erdos12Proof

variable {ι : Type*} [DecidableEq ι]

theorem tensorWeight_split (w : ι → ℝ) (s R : Finset ι) :
    tensorWeight w s = tensorWeight w (s \ R) * tensorWeight w (s ∩ R) := by
  have hdis : Disjoint (s \ R) (s ∩ R) := by
    apply Finset.disjoint_left.mpr
    intro i hi hit
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_inter.mp hit).2
  unfold tensorWeight
  rw [← Finset.prod_union hdis, Finset.sdiff_union_inter]

theorem selbergMass_remove_bound (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (F : Finset (Finset ι)) (R : Finset ι)
    (hdown : ∀ s ∈ F, ∀ t : Finset ι, t ⊆ s → t ∈ F) :
    selbergMass w F ≤
      selbergMass w (F.filter (fun s => Disjoint s R)) * ∏ i ∈ R, (1 + w i) := by
  let D := F.filter (fun s => Disjoint s R)
  let T := D ×ˢ R.powerset
  let code : Finset ι → Finset ι × Finset ι := fun s => (s \ R, s ∩ R)
  have hinj : Set.InjOn code F := by
    intro s _ t _ hst
    have hout := congrArg Prod.fst hst
    have hin := congrArg Prod.snd hst
    dsimp only [code] at hout hin
    calc
      s = s \ R ∪ s ∩ R := (Finset.sdiff_union_inter _ _).symm
      _ = t \ R ∪ t ∩ R := by rw [hout, hin]
      _ = t := Finset.sdiff_union_inter _ _
  have hcode : F.image code ⊆ T := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    apply Finset.mem_product.mpr
    constructor
    · exact Finset.mem_filter.mpr ⟨hdown s hs _ Finset.sdiff_subset, Finset.sdiff_disjoint⟩
    · exact Finset.mem_powerset.mpr Finset.inter_subset_right
  have hsum : selbergMass w F ≤ ∑ p ∈ T, tensorWeight w p.1 * tensorWeight w p.2 := by
    apply Finset.sum_le_sum_of_injOn code hinj hcode
    · intro s _
      exact (tensorWeight_split w s R).le
    · intro p _ _
      exact mul_nonneg (Finset.prod_nonneg (fun i _ => hw i))
        (Finset.prod_nonneg (fun i _ => hw i))
  calc
    _ ≤ ∑ p ∈ T, tensorWeight w p.1 * tensorWeight w p.2 := hsum
    _ = _ := by
      dsimp only [T, D, selbergMass]
      rw [Finset.sum_product]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul, subsetWeight_sum]

variable [Fintype ι]

theorem sieveMass_subtype (m : ι → ℕ) (P : ι → Prop) [DecidablePred P] (z : ℝ) :
    sieveMass (fun i : Subtype P => m i) z =
      selbergMass (fun i => sieveLocalWeight (m i))
        ((sieveSupport m z).filter (fun s => ∀ i ∈ s, P i)) := by
  unfold sieveMass selbergMass
  apply Finset.sum_bij (fun s _ => s.map (Function.Embedding.subtype P))
  · intro s hs
    apply Finset.mem_filter.mpr
    constructor
    · simpa only [sieveSupport, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.prod_map, Function.Embedding.subtype_apply] using hs
    · intro i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
      exact j.property
  · intro s _ t _ hst
    exact Finset.map_injective _ hst
  · intro s hs
    obtain ⟨hsF, hsP⟩ := Finset.mem_filter.mp hs
    refine ⟨s.subtype P, ?_, Finset.subtype_map_of_mem hsP⟩
    simp only [sieveSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hsF ⊢
    rw [Finset.prod_subtype_of_mem m hsP]
    exact hsF
  · intro s _
    simp only [tensorWeight, Finset.prod_map, Function.Embedding.subtype_apply]

theorem sieveMass_remove_bound (m : ι → ℕ) (hm : ∀ i, 1 < m i) (z : ℝ) (R : Finset ι) :
    sieveMass m z ≤
      sieveMass (fun i : {i // i ∉ R} => m i) z *
        ∏ i ∈ R, (1 + sieveLocalWeight (m i)) := by
  have h := selbergMass_remove_bound (fun i => sieveLocalWeight (m i))
    (fun i => (sieveLocalWeight_pos (hm i)).le) (sieveSupport m z) R
    (sieveSupport_downwardClosed (fun i => (hm i).le) z)
  have hfilter : (sieveSupport m z).filter (fun s => ∀ i ∈ s, i ∉ R) =
      (sieveSupport m z).filter (fun s => Disjoint s R) := by
    ext s
    simp only [Finset.mem_filter, Finset.disjoint_left]
  rw [sieveMass_subtype, hfilter]
  exact h

end Erdos12Proof
end

/- BEGIN SOURCE: ChenTheorem/Analysis/PNT/EulerMaclaurin.lean -/
section
/-
Adapted from PrimeNumberTheoremAnd/EulerMaclaurin.lean
Upstream commit: c6c73610b406689c4b58325cbe1342ecca25d755
License: Apache-2.0; see LICENSE and NOTICE in this directory tree.
Blueprint annotations removed; imports localized. See SOURCES.json.
-/

/- We prove the 1st order Euler-Maclaurin formula by specialising Abel summation and manipulating integrals. -/


open Finset Interval MeasureTheory


variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}

/- The 1st Bernoulli function. -/
noncomputable def B1 (x : ℝ) : ℝ := x - ⌊x⌋₊ - 1 / 2

lemma aestronglyMeasurable_B1 : AEStronglyMeasurable B1 := by
  unfold B1
  fun_prop

lemma abs_B1_le_half {x : ℝ} (hx : 0 ≤ x) : |B1 x| ≤ 1 / 2 := by
  unfold B1
  refine abs_le.mpr ⟨?_, ?_⟩
  · grind [Nat.floor_le hx]
  · grind [Nat.lt_succ_floor x]

lemma integral_deriv_mul_add_const (c : 𝕜) (hab : a ≤ b) (h_int : IntervalIntegrable (deriv f) volume a b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) :
    ∫ t in a..b, (t + c) * deriv f t = (b + c) * f b - (a + c) * f a - ∫ t in a..b, f t := by
  rw [← Set.uIcc_of_le hab] at hf_diff
  have : ∀ t ∈ [[a, b]], HasDerivAt (fun (t : ℝ) ↦ t + c) 1 t := by
    intro t ht
    simp only [hasDerivAt_add_const_iff]
    convert! ContinuousLinearMap.hasDerivAt (RCLike.ofRealCLM (K := 𝕜)) using 1
    simp
  replace hf_diff := fun t ht ↦ (hf_diff t ht).hasDerivAt
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul this hf_diff (by simp) h_int]
  simp

lemma intervalIntegrable_deriv_mul_B1 (ha : 0 ≤ a) (hab : a ≤ b) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    IntervalIntegrable (fun t ↦ deriv f t * B1 t) volume a b := by
  have hB1 : AEStronglyMeasurable B1 := aestronglyMeasurable_B1
  refine IntervalIntegrable.continuousOn_mul ?_ h_cont
  rw [intervalIntegrable_iff']
  apply MeasureTheory.Measure.integrableOn_of_bounded (by simp) (by fun_prop) (M := 1 / 2)
  filter_upwards [self_mem_ae_restrict (by measurability)] with x hx
  rw [Set.uIcc_of_le hab, Set.mem_Icc] at hx
  norm_cast
  exact abs_B1_le_half (by linarith)

lemma integral_deriv_mul_floor_add_one (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∫ t in a..b, deriv f t * (⌊t⌋₊ + 1) = (b + 1 / 2) * f b - (a + 1 / 2) * f a - (∫ t in a..b, f t) - ∫ t in a..b, deriv f t * B1 t := by
  calc
  _ = ∫ t in a..b, (deriv f t * (t + 1 / 2) -deriv f t * B1 t) := by
    congr
    ext
    simp only [B1]
    push_cast
    ring
  _ = (∫ t in a..b, deriv f t * (t + 1 / 2)) - ∫ t in a..b, deriv f t * B1 t := by
    exact intervalIntegral.integral_sub (ContinuousOn.intervalIntegrable (by fun_prop)) (intervalIntegrable_deriv_mul_B1 ha hab h_cont)
  _ = _ := by
    conv => lhs; arg 1; arg 1; ext; rw [mul_comm]
    rw [integral_deriv_mul_add_const _ hab h_cont.intervalIntegrable hf_diff]

theorem sum_eq_integral_add_integral_deriv (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k =
      f a * B1 a - f b * B1 b + (∫ t in a..b, f t) + ∫ t in a..b, deriv f t * B1 t  := by
  have := sum_mul_eq_sub_sub_integral_mul (fun _ ↦ 1) ha hab hf_diff (Set.uIcc_of_le hab ▸ h_cont).integrableOn_Icc
  simp only [mul_one, sum_const, Nat.card_Icc, tsub_zero, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one] at this
  rw [this, ← intervalIntegral.integral_of_le hab]
  rw [integral_deriv_mul_floor_add_one ha hab hf_diff h_cont]
  unfold B1
  push_cast
  ring
end

/- BEGIN SOURCE: ChenTheorem/Analysis/PNT/IEANTN/Mertens.lean -/
section
/-
Adapted from PrimeNumberTheoremAnd/IEANTN/Mertens.lean
Upstream commit: c6c73610b406689c4b58325cbe1342ecca25d755
License: Apache-2.0; see LICENSE and NOTICE in this directory tree.
Blueprint annotations removed; imports localized. See SOURCES.json.
-/

















theorem Filter.EventuallyEq.iff_eventually {α : Type _} {β : Type _} {l : Filter α} {f g : α → β} : f =ᶠ[l] g ↔ ∀ᶠ (x : α) in l, f x = g x := by rfl


namespace Real

open Filter Asymptotics

theorem inv_log_eq_o_one : (fun x ↦ 1 / log x) =o[atTop] (fun _ ↦ (1:ℝ)) := by
    rw [isLittleO_one_iff]
    convert tendsto_log_atTop.inv_tendsto_atTop using 1
    ext; simp

theorem one_eq_o_log_log : (fun _ ↦ (1:ℝ)) =o[atTop] (fun x ↦ log (log x)) := by
    simp only [isLittleO_one_left_iff, norm_eq_abs]
    exact tendsto_abs_atTop_atTop.comp (tendsto_log_atTop.comp tendsto_log_atTop)

end Real

section Issue1584
open MeasureTheory Set Filter Topology

/- The integrand `log v * exp (-v)` is integrable on `Ioi 0`. -/
private lemma integrableOn_log_mul_exp_neg :
    IntegrableOn (fun v : ℝ => Real.log v * Real.exp (-v)) (Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ), integrableOn_union]
  constructor
  · -- On `Ioc 0 1`: dominate by `|log v|`, which is integrable.
    have hlog : IntegrableOn (fun v : ℝ => Real.log v) (Ioc 0 1) volume := by
      have := (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1))
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one' ℝ)] at this
    apply Integrable.mono' hlog.norm
    · apply (Measurable.aestronglyMeasurable ?_)
      exact (Real.measurable_log.mul (Real.measurable_exp.comp measurable_neg))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with v hv
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 : |Real.exp (-v)| = Real.exp (-v) := abs_of_pos (Real.exp_pos _)
      have h2 : Real.exp (-v) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hv.1])
      rw [h1]
      nlinarith [abs_nonneg (Real.log v), Real.exp_pos (-v)]
  · -- On `Ioi 1`: dominate by `2 * exp (-v/2)`, integrable.
    have hexp : IntegrableOn (fun v : ℝ => (2 : ℝ) * Real.exp ((-1/2) * v)) (Ioi 1) volume := by
      exact (integrableOn_exp_mul_Ioi (by norm_num : (-1/2 : ℝ) < 0) 1).const_mul 2
    apply Integrable.mono' hexp
    · apply (Measurable.aestronglyMeasurable ?_)
      exact (Real.measurable_log.mul (Real.measurable_exp.comp measurable_neg))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with v hv
      have hv1 : (1 : ℝ) ≤ v := le_of_lt hv
      have hvpos : (0 : ℝ) < v := by linarith
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hlogabs : |Real.log v| = Real.log v :=
        abs_of_nonneg (Real.log_nonneg hv1)
      have hexpabs : |Real.exp (-v)| = Real.exp (-v) := abs_of_pos (Real.exp_pos _)
      rw [hlogabs, hexpabs]
      -- `log v ≤ v`
      have hlogv : Real.log v ≤ v := (Real.log_le_sub_one_of_pos hvpos).trans (by linarith)
      -- `v ≤ 2 * exp (v/2)`
      have hvexp : v ≤ 2 * Real.exp (v/2) := by
        have := Real.add_one_le_exp (v/2)
        nlinarith [Real.exp_pos (v/2)]
      -- combine: log v * exp(-v) ≤ v * exp(-v) ≤ 2 exp(v/2) exp(-v) = 2 exp(-v/2)
      have hstep : Real.log v * Real.exp (-v) ≤ 2 * Real.exp (v/2) * Real.exp (-v) := by
        apply mul_le_mul_of_nonneg_right (hlogv.trans hvexp) (le_of_lt (Real.exp_pos _))
      have heq : 2 * Real.exp (v/2) * Real.exp (-v) = 2 * Real.exp ((-1/2) * v) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf
      rw [heq] at hstep
      exact hstep

/- Helper: `∫_0^∞ log t · e^{-t} dt = Γ'(1)` (real). -/
private lemma integral_log_mul_exp_neg_eq_deriv_Gamma :
    ∫ t in Ioi (0:ℝ), Real.log t * Real.exp (-t) = deriv Real.Gamma 1 := by
  set I : ℝ := ∫ t in Ioi (0:ℝ), Real.log t * Real.exp (-t) with hI
  -- Step 1: derivative of GammaIntegral at 1.
  have h1 := Complex.hasDerivAt_GammaIntegral (s := (1 : ℂ)) (by norm_num)
  -- Step 2: simplify the integrand to `↑(log t * exp (-t))` and pull out `ofReal`.
  have hval : (∫ t : ℝ in Ioi 0, (↑t : ℂ) ^ ((1 : ℂ) - 1) * (↑(Real.log t) * ↑(Real.exp (-t))))
      = (I : ℂ) := by
    have key : ∀ t : ℝ, (↑t : ℂ) ^ ((1 : ℂ) - 1) * (↑(Real.log t) * ↑(Real.exp (-t)))
        = ((Real.log t * Real.exp (-t) : ℝ) : ℂ) := by
      intro t
      rw [sub_self, Complex.cpow_zero, one_mul, Complex.ofReal_mul]
    simp_rw [key]
    rw [integral_complex_ofReal, hI]
  rw [hval] at h1
  -- Step 3: transfer to Complex.Gamma (agrees with GammaIntegral on `{re > 0}`).
  have h2 : HasDerivAt Complex.Gamma (I : ℂ) 1 := by
    apply h1.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (0:ℝ) < (1:ℂ).re by norm_num)] with z hz
    exact Complex.Gamma_eq_integral hz
  -- Step 4: transfer ℂ → ℝ.
  have h3 := h2.real_of_complex
  have h4 : HasDerivAt Real.Gamma I 1 := by
    have hcongr : (fun x : ℝ => (Complex.Gamma ↑x).re) = Real.Gamma := by
      funext x
      rw [Complex.Gamma_ofReal, Complex.ofReal_re]
    rw [hcongr, Complex.ofReal_re] at h3
    exact h3
  rw [← h4.deriv]

/- Core of #1584, stated with explicit qualifiers (outside `namespace Mertens`,
where `Finset` is open and would clash with `Set.Ioi`). -/
private theorem mul_integ_log_log_eq_aux (s : ℝ) (hs : 1 < s) :
    (s - 1) * ∫ x in Ioi (1:ℝ), Real.log (Real.log x) * x ^ (-s) =
      - Real.log (s - 1) + deriv Real.Gamma 1 := by
  have hs0 : 0 < s - 1 := by linarith
  set f : ℝ → ℝ := fun x => (s - 1) * Real.log x with hf_def
  set f' : ℝ → ℝ := fun x => (s - 1) / x with hf'_def
  set g : ℝ → ℝ := fun u => (Real.log u - Real.log (s - 1)) * Real.exp (-u) with hg_def
  -- f 1 = 0
  have hf1 : f 1 = 0 := by simp [hf_def]
  -- ContinuousOn f (Ici 1)
  have hf_cont : ContinuousOn f (Ici 1) := by
    apply ContinuousOn.mul continuousOn_const
    apply Real.continuousOn_log.mono
    intro x hx
    simp only [mem_Ici] at hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith
  -- Tendsto f atTop atTop
  have hft : Tendsto f atTop atTop := by
    apply Filter.Tendsto.const_mul_atTop hs0
    exact Real.tendsto_log_atTop
  -- HasDerivWithinAt f (f' x) (Ioi x) x for x ∈ Ioi 1
  have hff' : ∀ x ∈ Ioi (1:ℝ), HasDerivWithinAt f (f' x) (Ioi x) x := by
    intro x hx
    simp only [mem_Ioi] at hx
    have hxne : x ≠ 0 := by linarith
    have := (Real.hasDerivAt_log hxne).const_mul (s - 1)
    have h2 : HasDerivAt f ((s - 1) * x⁻¹) x := this
    have : (s - 1) * x⁻¹ = f' x := by rw [hf'_def]; field_simp
    rw [this] at h2
    exact h2.hasDerivWithinAt
  -- image facts: f strictly mono on Ici 1
  have hmono : StrictMonoOn f (Ici 1) := by
    intro a ha b hb hab
    simp only [mem_Ici] at ha hb
    apply mul_lt_mul_of_pos_left _ hs0
    exact Real.log_lt_log (by linarith) hab
  have himg_Ioi : f '' Ioi 1 = Ioi 0 := by
    ext y
    simp only [Set.mem_image, mem_Ioi]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : 0 < Real.log x := Real.log_pos hx
      positivity
    · intro hy
      refine ⟨Real.exp (y / (s - 1)), ?_, ?_⟩
      · exact Real.one_lt_exp_iff.mpr (div_pos hy hs0)
      · rw [hf_def]
        simp only [Real.log_exp]
        field_simp
  have himg_Ici : f '' Ici 1 = Ici 0 := by
    ext y
    simp only [Set.mem_image, mem_Ici]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : 0 ≤ Real.log x := Real.log_nonneg hx
      rw [hf_def]; positivity
    · intro hy
      refine ⟨Real.exp (y / (s - 1)), ?_, ?_⟩
      · exact Real.one_le_exp_iff.mpr (div_nonneg hy hs0.le)
      · rw [hf_def]
        simp only [Real.log_exp]
        field_simp
  -- ContinuousOn g (f '' Ioi 1) = ContinuousOn g (Ioi 0)
  have hg_cont : ContinuousOn g (f '' Ioi 1) := by
    rw [himg_Ioi]
    apply ContinuousOn.mul
    · apply ContinuousOn.sub _ continuousOn_const
      apply Real.continuousOn_log.mono
      intro u hu
      simp only [mem_Ioi] at hu
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      linarith
    · exact (Real.continuous_exp.comp continuous_neg).continuousOn
  -- IntegrableOn g (f '' Ici 1) = IntegrableOn g (Ici 0)
  have hg1 : IntegrableOn g (f '' Ici 1) := by
    rw [himg_Ici, integrableOn_Ici_iff_integrableOn_Ioi]
    have e1 : IntegrableOn (fun u => Real.log u * Real.exp (-u)) (Ioi 0) :=
      integrableOn_log_mul_exp_neg
    have e2 : IntegrableOn (fun u => Real.log (s - 1) * Real.exp (-u)) (Ioi 0) :=
      (integrableOn_exp_neg_Ioi 0).const_mul _
    have : g = fun u => Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u) := by
      funext u; rw [hg_def]; ring
    rw [this]
    exact e1.sub e2
  -- IntegrableOn (fun x => (g ∘ f) x * f' x) (Ici 1)
  have hg2 : IntegrableOn (fun x => (g ∘ f) x * f' x) (Ici 1) := by
    -- HasDerivWithinAt f (f' x) (Ici 1) x for x ∈ Ici 1.
    have hff'_Ici : ∀ x ∈ Ici (1:ℝ), HasDerivWithinAt f (f' x) (Ici 1) x := by
      intro x hx
      simp only [mem_Ici] at hx
      have hxne : x ≠ 0 := by linarith
      have hd : HasDerivAt f ((s - 1) * x⁻¹) x := (Real.hasDerivAt_log hxne).const_mul (s - 1)
      have heq : (s - 1) * x⁻¹ = f' x := by rw [hf'_def]; field_simp
      rw [heq] at hd
      exact hd.hasDerivWithinAt
    -- f injective on Ici 1.
    have hinj : InjOn f (Ici 1) := hmono.injOn
    -- transfer hg1 through the integrability change of variables.
    have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul
      (s := Ici (1:ℝ)) (f := f) (f' := f') measurableSet_Ici hff'_Ici hinj g
    rw [hiff] at hg1
    -- relate to our integrand on Ici 1.
    apply hg1.congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
    simp only [mem_Ici] at hx
    have hxpos : (0:ℝ) < x := by linarith
    have hf'pos : 0 < f' x := by rw [hf'_def]; positivity
    simp only [smul_eq_mul, Function.comp, abs_of_pos hf'pos]
    ring
  -- Apply change of variables.
  have hcov := integral_comp_mul_deriv_Ioi hf_cont hft hff' hg_cont hg1 hg2
  rw [hf1] at hcov
  -- RHS: ∫ u in Ioi 0, g u = deriv Gamma 1 - log (s-1)
  have hrhs : ∫ u in Ioi (0:ℝ), g u = deriv Real.Gamma 1 - Real.log (s - 1) := by
    have e1 : IntegrableOn (fun u => Real.log u * Real.exp (-u)) (Ioi 0) :=
      integrableOn_log_mul_exp_neg
    have e2 : IntegrableOn (fun u => Real.log (s - 1) * Real.exp (-u)) (Ioi 0) :=
      (integrableOn_exp_neg_Ioi 0).const_mul _
    have hsplit : (fun u => g u)
        = fun u => Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u) := by
      funext u; rw [hg_def]; ring
    rw [show (∫ u in Ioi (0:ℝ), g u)
        = ∫ u in Ioi (0:ℝ), (Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u))
        from by rw [hsplit]]
    rw [integral_sub e1 e2, integral_log_mul_exp_neg_eq_deriv_Gamma]
    rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
  -- LHS: ∫ x in Ioi 1, (g∘f) x * f' x = (s-1) * ∫ x in Ioi 1, log(log x) * x^(-s)
  have hlhs : ∫ x in Ioi (1:ℝ), (g ∘ f) x * f' x
      = (s - 1) * ∫ x in Ioi (1:ℝ), Real.log (Real.log x) * x ^ (-s) := by
    have hpt : ∀ x ∈ Ioi (1:ℝ), (g ∘ f) x * f' x
        = (s - 1) * (Real.log (Real.log x) * x ^ (-s)) := by
      intro x hx
      simp only [mem_Ioi] at hx
      have hxpos : (0:ℝ) < x := by linarith
      have hlogpos : 0 < Real.log x := Real.log_pos hx
      have hlogne : Real.log x ≠ 0 := ne_of_gt hlogpos
      have hs1ne : s - 1 ≠ 0 := ne_of_gt hs0
      simp only [Function.comp, hf_def, hg_def, hf'_def]
      -- log ((s-1) * log x) - log (s-1) = log (log x)
      rw [Real.log_mul hs1ne hlogne]
      -- exp (-((s-1) * log x)) = x ^ (-(s-1))
      have hexp : Real.exp (-((s - 1) * Real.log x)) = x ^ (-(s - 1)) := by
        rw [Real.rpow_def_of_pos hxpos]
        ring_nf
      rw [hexp]
      -- x ^ (-(s-1)) * ((s-1)/x) = (s-1) * x^(-s)
      have hx1 : x ^ (-(s - 1)) * ((s - 1) / x) = (s - 1) * x ^ (-s) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one x]
        rw [show x ^ (-(s - 1)) * ((s - 1) * x ^ (-1 : ℝ))
            = (s - 1) * (x ^ (-(s - 1)) * x ^ (-1 : ℝ)) by ring]
        rw [← Real.rpow_add hxpos]
        ring_nf
      rw [show (Real.log (s - 1) + Real.log (Real.log x) - Real.log (s - 1))
          = Real.log (Real.log x) by ring]
      linear_combination Real.log (Real.log x) * hx1
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  rw [hlhs, hrhs] at hcov
  rw [hcov]
  ring

end Issue1584

namespace Mertens

/-
\section{Mertens' theorems}

In this section we give explicit versions of Mertens' theorems:
\begin{itemize}
\item Mertens' first theorem (von Mangoldt form): $\sum_{n \leq x} \frac{\Lambda(n)}{n} = \log x + O(1)$.
\item Mertens' first theorem (prime form): $\sum_{p \leq x} \frac{\log p}{p} = \log x + O(1)$.
\item Mertens' second theorem (von Mangoldt form): $\sum_{n \leq x} \frac{\Lambda(n)}{n \log n} = \log \log x + \gamma + O(1/\log x)$.
\item Mertens' second theorem (prime form): $\sum_{p \leq x} \frac{1}{p} = \log \log x + M + O(1/\log x)$, where $M$ is the Meissel-Mertens constant.
\item Mertens' third theorem: $\prod_{p \leq x} (1 - \frac{1}{p}) = e^{-\gamma}/\log x + O(1/\log^2 x)$.
\end{itemize}
We aim to upstreaming these results to Mathlib.  In particular, the arguments here should be self-contained and written for efficiency, coherency, and clarity.  As such, extensive use of AI tools is \emph{strongly discouraged} in this section.

The arguments here are drawn from Leo Goldmakher's ``A quick proof of Mertens' theorem'' from https://web.williams.edu/Mathematics/lg5/mertens.pdf

The unfinished formalization of Mertens' theorems by Arend Mellendijk in https://github.com/FLDutchmann/Analytic/blob/main/Analytic/Mertens.lean may also be relevant here.
-/


open Real Finset Filter Asymptotics Topology
open ArithmeticFunction hiding log

lemma sum_Ioc_one_eq_sum_Ioc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf : f 1 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Ioc 0 x, f n := by
  rw [(by rfl : Ioc 0 x = Icc 1 x), ← add_sum_Ioc_eq_sum_Icc hx]
  simpa


theorem sum_log_eq {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n =
      x * log x - (x - ⌊x⌋₊ - 1 / 2) * log x - x + 1 + ∫ t in 1..x, (t - ⌊t⌋₊ - 1 / 2) / t := by
  rw [← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp)]
  have : 1 = ⌊(1 : ℝ)⌋₊ := by simp
  nth_rw 1 [this]
  rw [sum_eq_integral_add_integral_deriv (by norm_num) hx (fun _ _ ↦ (by fun_prop (disch := grind)))]
  · simp only [log_one, B1, Nat.floor_one, Nat.cast_one, sub_self, zero_sub,
    RCLike.ofReal_real_eq_id, id_eq, mul_neg, zero_mul, neg_zero, integral_log, mul_zero, sub_zero,
    deriv_log']
    ring_nf
    congr
    ext
    ring
  · simp only [deriv_log', Set.uIcc_of_le hx]
    fun_prop (disch := grind)


theorem sum_log_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≤ x * log x := by
  calc
  _ ≤ ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log x := by
    refine sum_le_sum fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    exact log_le_log (by exact_mod_cast hn.1) (Nat.le_floor_iff (by linarith)|>.mp hn.2)
  _ = ⌊x⌋₊ * log x := by simp
  _ ≤ _ := by
    gcongr
    · exact log_nonneg hx
    · exact Nat.floor_le (by linarith)


lemma integral_log_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, log t ≤ log b * (b - a) := by
  apply le_of_abs_le
  have : ∀ t ∈ Set.uIoc a b, ‖log t‖ ≤ log b := by
    intro t ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    rw [norm_of_nonneg <| log_nonneg (by linarith)]
    gcongr <;> linarith
  grw [← norm_eq_abs, intervalIntegral.norm_integral_le_of_norm_le_const this,
    abs_of_nonneg (by linarith)]


theorem sum_log_ge {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≥ x * log x - 2 * x := by
  have one_le_floor : 1 ≤ ⌊x⌋₊ := by simpa
  calc
  _ = ∑ n ∈ Icc 1 ⌊ x ⌋₊, log n := by rfl
  _ = ∑ n ∈ Ico (1 + 1) (⌊ x ⌋₊ + 1), log n := by
    rw [← add_sum_Ioc_eq_sum_Icc one_le_floor]
    simp
    rfl
  _ = ∑ n ∈ Ico 1 ⌊ x ⌋₊, log ((n + 1 : ℕ)) := by
    rw [← Finset.sum_Ico_add']
  _ ≥ ∫ t in 1..⌊x⌋₊, log t := by
    convert MonotoneOn.integral_le_sum_Ico one_le_floor ?_|>.ge
    · norm_cast
    · exact StrictMonoOn.monotoneOn (strictMonoOn_log.mono fun y hy ↦ (by simp_all; linarith))
  _ = (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log t := by
    nth_rw 3 [intervalIntegral.integral_symm]
    rw [sub_neg_eq_add, intervalIntegral.integral_add_adjacent_intervals] <;> exact intervalIntegral.intervalIntegrable_log'
  _ ≥ (∫ t in 1..x, log t) - log x := by
    gcongr
    grw [integral_log_le (by simpa) (Nat.floor_le (by linarith))]
    nth_rw 2 [← mul_one (log x)]
    gcongr
    · exact log_nonneg hx
    · linarith [Nat.lt_floor_add_one x]
  _ ≥ x * log x - x - log x := by simp only [integral_log, log_one, mul_zero, sub_zero, ge_iff_le,
    tsub_le_iff_right, sub_add_cancel, le_add_iff_nonneg_right, zero_le_one]
  _ ≥ _ := by linarith [log_le_self (by linarith : 0 ≤ x)]


theorem sum_log_eq_log_factorial (x : ℝ) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n = log (Nat.floor x).factorial := by
    rw [←prod_Ico_id_eq_factorial, ←log_prod, prod_natCast]
    · congr
    intro x hx
    simp at hx ⊢; grind


theorem sum_log_eq_sum_mangoldt {x : ℝ} :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
  have : ∀ n : ℕ, log n = (Λ * zeta) n := by simp [vonMangoldt_mul_zeta]
  simp_rw [this, sum_Ioc_mul_zeta_eq_sum, ← Nat.floor_div_natCast]


noncomputable abbrev E₁Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x

theorem sum_mangoldt_div_eq (x : ℝ) : ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d = log x + E₁Λ x := by
    grind


theorem E₁Λ.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x  ≥ -2 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d  ≥ x * (log x - 2) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≥ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
    gcongr
    exact Nat.floor_le <| div_nonneg (by linarith) (by linarith)
  _ ≥ x * log x - 2 * x :=
    sum_log_eq_sum_mangoldt ▸ sum_log_ge hx
  _ = _ := by ring


theorem E₁Λ.le {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ log 4 + 4 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ x * (log x + log 4 + 4) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (⌊x / d⌋₊ + 1) := by
    gcongr
    exact Nat.lt_floor_add_one _|>.le
  _ = (∑ d ∈ Ioc 0 ⌊x⌋₊, log d) + ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d := by
    simp_rw [mul_add, mul_one]
    rw [Finset.sum_add_distrib, sum_log_eq_sum_mangoldt]
  _ ≤ x * log x + (log 4 + 4) * x := by
    gcongr
    · exact sum_log_le hx
    · exact Chebyshev.psi_le_const_mul_self (by linarith)
  _ = _ := by ring


theorem sum_mangoldt_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x| ≤ log 4 + 4 := by
  grind [E₁Λ.le hx, E₁Λ.ge hx, log_nonneg]

theorem E₁Λ.bounded' : ∃ c > 0, ∀ x ≥ 1, |E₁Λ x| ≤ c := by
  exact ⟨log 4 + 4, (by positivity), fun x hx ↦ sum_mangoldt_div_eq_log hx⟩


theorem E₁Λ.bounded : E₁Λ =O[atTop] (fun _ ↦ (1:ℝ)) := by
  simp only [isBigO_iff, norm_eq_abs, norm_one, mul_one,
    eventually_atTop]
  exact ⟨log 4 + 4, 1, fun _ hx ↦ sum_mangoldt_div_eq_log hx⟩

theorem one_eq_o_log : (fun _ ↦ (1:ℝ)) =o[atTop] (fun x ↦ log x) := by
    simp only [isLittleO_one_left_iff, norm_eq_abs]
    exact tendsto_abs_atTop_atTop.comp tendsto_log_atTop


theorem sum_mangoldt_div_eq_log' :
    (fun x ↦ ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d) ~[atTop] (fun x ↦ log x) := by
    apply IsLittleO.isEquivalent (IsBigO.trans_isLittleO _ one_eq_o_log)
    convert! E₁Λ.bounded using 1


noncomputable abbrev E₁p (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x

theorem sum_log_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p = log x + E₁p x := by
    grind


theorem E₁p.le_E₁Λ (x : ℝ) :
    E₁p x ≤ E₁Λ x := by
    unfold E₁p E₁Λ; rw [sum_filter]
    gcongr with p _
    split_ifs with hp
    · simp [vonMangoldt_apply_prime hp]
    have : 0 ≤ Λ p := vonMangoldt_nonneg
    positivity


theorem E₁p.le {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≤ log 4 + 4 := by
    linarith [E₁Λ.le hx, E₁p.le_E₁Λ x]

noncomputable abbrev E₁ : ℝ := ∑' p : ℕ, if p.Prime then (log p) / (p*(p-1)) else 0

lemma E₁.summand_nonneg (p : ℕ) : 0 ≤ if p.Prime then (log p) / (p*(p-1)) else 0 := by
  split_ifs with h
  · refine div_nonneg (log_natCast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ?_)
    suffices 1 ≤ (p : ℝ) by linarith
    exact_mod_cast h.one_le
  · rfl


theorem E₁.summable : Summable (fun p : ℕ ↦ if p.Prime then (log p) / (p*(p-1)) else 0) := by
  refine (Real.summable_one_div_nat_rpow.mpr (by norm_num: 1 < (3 : ℝ) / 2)|>.const_div
    4).of_nonneg_of_le E₁.summand_nonneg fun n ↦ ?_
  split_ifs with h
  · grw [Real.log_le_rpow_div (Nat.cast_nonneg _) (by norm_num : 0 < (1 : ℝ) / 2)]
    · have denom : (n : ℝ) * ((n : ℝ) - 1) ≥ n ^ 2/ 2 := by
        rw [sq, mul_div_assoc]
        gcongr
        suffices (n : ℝ) ≥ 2 by linarith
        exact_mod_cast h.two_le
      grw [denom]
      · apply le_of_eq
        rw [← Real.rpow_natCast]
        field_simp
        rw [mul_div_assoc, ← Real.rpow_sub (mod_cast h.pos)]
        norm_num
        rw [Real.rpow_neg (Nat.cast_nonneg _)]
        field
      · exact div_pos (pow_pos (mod_cast h.pos) _) (by norm_num)
    · apply mul_nonneg (Nat.cast_nonneg _)
      suffices 1 ≤ (n : ℝ) by linarith
      exact_mod_cast h.one_le
  · positivity

private lemma antitoneOn_log_div_sq :
    AntitoneOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp at ht
    have : (t + 2) ≠ 0 := by simp; linarith
    fun_prop (disch := grind)
  · refine fun t ht ↦ DifferentiableAt.differentiableWithinAt ?_
    simp at ht
    have : (t + 2) ^ 2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · intro t ht
    simp at ht
    rw [deriv_fun_div (by fun_prop (disch := grind)) (by fun_prop) (by simp; grind), deriv_comp_add_const, deriv_log]
    simp
    field_simp
    simp only [mul_zero, tsub_le_iff_right, zero_add]
    rw [← log_rpow (by linarith), ← log_exp 1, rpow_ofNat]
    gcongr
    nlinarith [exp_one_lt_three]

private lemma log_div_sq_nonneg :
    ∀ t ∈ Set.Ioi 0, 0 ≤ log (t + 2) / (t + 2) ^ 2 := by
  exact fun t ht ↦  div_nonneg (log_nonneg (by simp_all; linarith)) (by positivity)

private lemma log_div_sq_is_deriv :
    ∀ x ∈ Set.Ici 0, HasDerivAt (fun t ↦ (-log (t + 2) - 1) / (t + 2)) (log (x + 2) / (x + 2) ^ 2) x := by
  intro t ht
  simp at ht
  apply HasDerivAt.comp_add_const (f := (fun t ↦ (-log t - 1)/ t)) t 2
  convert! HasDerivAt.fun_div (c' := -1 / (t + 2)) (d' := (1 : ℝ)) _ _  _ using 1
  · field
  · apply HasDerivAt.sub_const
    convert! (hasDerivAt_log (by linarith : t + 2 ≠ 0)).neg using 1
    ring_nf
  · exact hasDerivAt_id _
  · linarith

private lemma tendsto_antideriv_log_div_sq :
    Tendsto (fun t ↦ (-log (t + 2) - 1) / (t + 2)) atTop (nhds 0) := by
  have : Tendsto (fun (t : ℝ) ↦ t + 2) atTop atTop := by exact tendsto_atTop_add_const_right atTop 2 tendsto_id
  apply Tendsto.comp (g := (fun t ↦ (-log t - 1) / t)) _ this
  convert! Tendsto.sub (f := (fun t ↦ -log t / t)) (a := 0) _ tendsto_inv_atTop_zero using 1
  · ring_nf
  · ring_nf
  · convert! (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by linarith)).neg using 1
    · ext; ring
    · simp

private lemma integrableOn_log_div_sq :
    MeasureTheory.IntegrableOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ioi 0) := by
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq

private lemma integral_log_div_sq :
    ∫ t in Set.Ioi 0, log (t + 2) / (t + 2) ^ 2 = (log 2 + 1) / 2 := by
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq]
  ring_nf

private lemma summable_log_div_sq :
    Summable (fun (n : ℕ)↦ log (n + 3) / (n + 3) ^ 2) := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  suffices Summable (fun (n : ℕ) ↦ g n ) by
    convert! summable_nat_add_iff 1|>.mpr this using 2
    unfold g
    push_cast
    ring_nf
  exact antitoneOn_log_div_sq.summable_of_integrableOn_Ioi_zero integrableOn_log_div_sq log_div_sq_nonneg

private lemma sum_log_div_sq_le :
    ∑' (n : ℕ), log (n + 3) / (n + 3) ^2 ≤ (log 2 + 1) / 2 := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  calc
  _ = ∑' (n : ℕ), g (n + 1 : ℕ):= by
    unfold g
    congr
    push_cast
    ring_nf
  _ ≤ ∫ x in Set.Ioi 0, g x := by
    exact antitoneOn_log_div_sq.tsum_add_one_le_integral integrableOn_log_div_sq log_div_sq_nonneg
  _ = _ := by
    exact integral_log_div_sq


theorem E₁.le : E₁ ≤ (5 * log 2 + 3) / 4 := by
  unfold E₁
  calc
  _ = log 2 / 2 + ∑' (n : ℕ), if (n + 3).Prime then log (n + 3) / ((n + 3) * (n + 2)) else 0 := by
    rw [← E₁.summable.sum_add_tsum_nat_add 3, (by rfl : range 3 = {0, 1, 2})]
    simp [Nat.prime_two]
    ring_nf
  _ ≤ log 2 / 2 + ∑' (n : ℕ), (3 / 2) * (log (n + 3) / (n + 3) ^ 2) := by
    gcongr with n
    · convert! summable_nat_add_iff 3|>.mpr E₁.summable using 4
      · norm_cast
      · push_cast; ring
    · exact summable_log_div_sq.mul_left _
    · split_ifs with h
      · grw [(by linarith : (n + 2 : ℝ) ≥ 2 * (n + 3) / 3)]
        · field_simp
          rfl
        · exact log_nonneg (by grind)
      · exact mul_nonneg (by norm_num) (div_nonneg (log_nonneg (by grind)) (by positivity))
  _ = log 2 / 2 + (3 / 2) * ∑' (n : ℕ), log (n + 3) / (n + 3) ^ 2 := by
    rw [tsum_mul_left]
  _ ≤ _ := by
    grw [sum_log_div_sq_le]
    ring_nf
    rfl

theorem E₁.nonneg : E₁ ≥ 0 :=
  tsum_nonneg E₁.summand_nonneg


theorem E₁Λ.le_E₁p_add_E₁ {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ E₁p x + E₁ := by
  unfold E₁Λ E₁p
  suffices ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / p + E₁ by linarith
  simp_rw [vonMangoldt_apply, ite_div, zero_div, ← sum_filter, Chebyshev.sum_PrimePow_eq_sum_sum _ (by linarith)]
  calc
  _ = ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    refine sum_congr rfl fun k hk ↦ sum_congr rfl fun p hp ↦ ?_
    rw [Nat.Prime.pow_minFac (by simp_all) (by simp_all; linarith)]
  _ ≤ ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    gcongr with k hk
    apply rpow_le_self_of_one_le hx
    simp only [mem_Icc] at hk
    exact div_le_one₀ (by norm_cast; linarith)|>.mpr (mod_cast hk.1)
  _ ≤ ∑ k ∈ Icc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    apply sum_le_sum_of_subset_of_nonneg
    · gcongr
      exact le_max_right ..
    · exact fun _ _ _ ↦ sum_nonneg fun _ _ ↦ (by positivity)
  _ = ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, (log p / p) + ∑ k ∈ Ioc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    rw [← add_sum_Ioc_eq_sum_Icc (le_max_left ..)]
    simp
  _ ≤ _ := by
    gcongr
    rw [sum_comm]
    conv => lhs; arg 2; ext p; arg 2; ext k; rw [← mul_one_div, Nat.cast_pow, ← one_div_pow]
    simp_rw [← mul_sum]
    calc
    _ ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p * (p - 1)) := by
      gcongr with p hp
      simp only [mem_filter, mem_Ioc] at hp
      conv => rhs; rw [← mul_one_div]
      gcongr
      rw [(by rfl : Ioc 1 (max 1 ⌊log x / log 2⌋₊) = Ico 2 (max 1 ⌊log x / log 2⌋₊  + 1))]
      grw [geom_sum_Ico_le_of_lt_one (by simp)]
      · apply le_of_eq
        have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.1.1.ne.symm
        field
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast hp.2.one_lt)
    _ ≤ _ := by
      rw [sum_filter]
      exact E₁.summable.sum_le_tsum _ fun p hp ↦ E₁.summand_nonneg p

theorem E₁p.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≥ -2 - E₁ := by
    linarith [E₁Λ.le_E₁p_add_E₁ hx, E₁Λ.ge hx]


theorem sum_log_prime_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x| ≤ log 4 + 4 := by
    rw [abs_le']
    refine ⟨ E₁p.le hx, ?_ ⟩
    have : log 2 > 0 := by apply log_pos; norm_num
    have : log 4 = 2 * log 2 := by rw [←Real.log_rpow (by norm_num)]; norm_num
    grind [E₁p.ge hx, E₁.le]

theorem E₁p.bounded : ∃ c > 0, ∀ x ≥ 1, |E₁p x| ≤ c := by
  exact ⟨log 4 + 4, (by positivity), fun _ hx ↦ sum_log_prime_div_eq_log  hx⟩


theorem sum_log_prime_div_eq_log' : E₁p =O[atTop] (fun _ ↦ (1:ℝ)) := by
    simp only [isBigO_iff, norm_eq_abs, one_mem, CStarRing.norm_of_mem_unitary, mul_one,
      eventually_atTop, E₁p]
    exact ⟨ log 4 + 4, 1, fun _ ↦ sum_log_prime_div_eq_log ⟩


theorem sum_log_prime_div_eq_log'' : (fun x ↦ ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p) ~[atTop] (fun x ↦ log x) := by
    apply IsLittleO.isEquivalent (IsBigO.trans_isLittleO _ one_eq_o_log)
    convert! sum_log_prime_div_eq_log' using 1


noncomputable abbrev γ : ℝ := (∫ t in Set.Ioi 2, E₁Λ t / (t * log t^2)) + 1 - log (log 2)


noncomputable abbrev E₂Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x) - γ

lemma sum_Ioc_one_eq_sum_Icc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf1 : f 1 = 0) (hf0 : f 0 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Icc 0 x, f n := by
  rw [sum_Ioc_one_eq_sum_Ioc_zero hx hf1, ← add_sum_Ioc_eq_sum_Icc (by linarith)]
  simpa


private theorem sum_div_log_eq {x : ℝ} (hx : 2 ≤ x) (f : ℕ → ℝ) :
    ∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n / log n =
      (∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n) / log x + ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊ t ⌋₊, f n) / (t * log t^2) := by
  let g : ℕ → ℝ := (fun n ↦ if n < 2 then 0 else f n)
  trans ∑ n ∈ Icc 0 ⌊ x ⌋₊, (log n)⁻¹ * g n
  · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp) (by simp)]
    refine sum_congr rfl fun n hn ↦ ?_
    have : ¬(n ≤ 1) := by simp_all
    simp [g, this]
    field
  rw [sum_mul_eq_sub_integral_mul₁ g (f := (fun n ↦ (log n)⁻¹)) (by simp [g]) (by simp [g])]
  · rw [intervalIntegral.integral_of_le hx, mul_comm, ← div_eq_mul_inv, ← sub_neg_eq_add]
    simp_rw [deriv_inv_log]
    congr 1
    · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      congr 1
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
    · rw [← MeasureTheory.integral_neg]
      refine  MeasureTheory.setIntegral_congr_fun (by measurability) fun t ht ↦ ?_
      simp only [Set.mem_Ioc] at ht
      rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      field_simp
      congr 2
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
  · intro t ht
    simp only [Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp only [Set.mem_Icc] at ht
    conv => arg 1; ext x; rw [deriv_inv_log]
    have : log t ^2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)

private theorem integrable_const_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ c / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  conv => arg 1; ext t; rw [← mul_one_div]
  apply MeasureTheory.Integrable.const_mul
  refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' ?_ ?_ tendsto_log_atTop.inv_tendsto_atTop.neg
  · intro t ht
    simp only [Set.mem_Ici] at ht
    have : log t ≠ 0 := by simp; grind
    have : DifferentiableAt ℝ (fun t ↦ -(log t)⁻¹) t := by
      fun_prop (disch := grind)
    convert! this.hasDerivAt using 1
    simp [deriv_inv_log]
    field
  · intro t ht
    simp only [Set.mem_Ioi] at ht
    exact one_div_nonneg.mpr <| mul_nonneg (by linarith) (sq_nonneg _)


private theorem integrable_E₁Λ_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ E₁Λ x / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  obtain ⟨c, hc1, hc2⟩ := E₁Λ.bounded'
  apply MeasureTheory.Integrable.mono (integrable_const_div_mul_log_sq c hx)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, norm_eq_abs, norm_mul, norm_pow, sq_abs, abs_of_pos hc1]
    gcongr
    exact hc2 t (by linarith)

private theorem integrable_E₁p_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ E₁p x / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  obtain ⟨c, hc1, hc2⟩ := E₁p.bounded
  apply MeasureTheory.Integrable.mono (integrable_const_div_mul_log_sq c hx)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, norm_eq_abs, norm_mul, norm_pow, sq_abs, abs_of_pos hc1]
    gcongr
    exact hc2 t (by linarith)

lemma deriv_log_log {x : ℝ} (hx : 1 < x) :
    deriv (fun t ↦ log (log t)) x = 1 / (x * log x) := by
  rw [deriv.log (differentiableAt_log (by linarith)) (by simp; grind), deriv_log]
  field

lemma integral_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in 2..x, 1 / (t * log t) = log (log x) - log (log 2) := by
  rw [← intervalIntegral.integral_deriv_eq_sub (f := fun t ↦ log (log t))]
  · refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [deriv_log_log]
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    linarith
  · intro t ht
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.intervalIntegrable ?_
    apply ContinuousOn.congr (f := (fun t ↦ 1 / (t * log t)))
    · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      have : log t ≠ 0 := by simp; grind
      fun_prop (disch := grind)
    · intro t ht
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      exact deriv_log_log (by linarith)

lemma intervalIntegrable_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t ↦ 1 / (t * log t)) MeasureTheory.volume 2 x := by
  refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
  have : log t ≠ 0 := by simp; grind
  fun_prop (disch := grind)


theorem E₂Λ.eq {x : ℝ} (hx : 2 ≤ x) :
    E₂Λ x = E₁Λ x / log x - ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) := by
  unfold E₂Λ
  rw [← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp)]
  conv => lhs; arg 1; arg 1; arg 2; ext n; rw [(by field : Λ n / (n * log n) = (Λ n / n) / log n)]
  rw [sum_div_log_eq hx]
  rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), sum_mangoldt_div_eq]
  have : ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊t⌋₊, Λ n / n) / (t * log t ^ 2) = ∫ t in 2..x, (1 / (t * log t) + E₁Λ t / (t * log t ^ 2)) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), sum_mangoldt_div_eq]
    field
  rw [this, intervalIntegral.integral_add]
  · rw [integral_one_div_mul_log hx, add_div, div_self (by simp; grind)]
    unfold γ
    calc
    _ = E₁Λ x / log x + (∫ (x : ℝ) in 2..x, E₁Λ x / (x * log x ^ 2)) -
      ((∫ (t : ℝ) in Set.Ioi 2, E₁Λ t / (t * log t ^ 2))) := by ring
    _ = _ := by
      rw [← intervalIntegral.integral_interval_add_Ioi (integrable_E₁Λ_div_mul_log_sq (by rfl)) (integrable_E₁Λ_div_mul_log_sq hx)]
      ring
  · exact intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact integrable_E₁Λ_div_mul_log_sq (x := 2) (by rfl)|>.mono (by grind) (by rfl)

private theorem integ_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Ioi x, c / (t * log t^2) = c / log x := by
    convert! MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' (m := 0) (f := fun x ↦ - c / log x) ?_
      (integrable_const_div_mul_log_sq c hx) ?_ using 1
    · grind
    · intro t ht; simp at ht
      convert! HasDerivAt.fun_div (hasDerivAt_const _ (-c)) (hasDerivAt_log (by linarith)) ?_ using 1
      · grind
      simp; grind
    convert! tendsto_log_atTop.inv_tendsto_atTop.const_mul (-c) using 1
    simp


theorem E₂Λ.abs_le {x : ℝ} (hx : 2 ≤ x) :
    |E₂Λ x| ≤ (log 4 + 6) / log x := by
    have : 0 < log x := by apply log_pos; linarith
    rw [E₂Λ.eq hx, abs_le']
    constructor
    · grw [E₁Λ.le (by linarith)]
      have : ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) ≥ - 2 / log x := calc
        _ ≥ ∫ t in Set.Ioi x, (-2) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_const_div_mul_log_sq (-2) hx)
            (integrable_E₁Λ_div_mul_log_sq hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁Λ.ge (by linarith)
        _ = _ := integ_div_mul_log_sq (-2) hx
      grw [this]
      grind
    grw [E₁Λ.ge (by linarith)]
    have : ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) ≤ (log 4 + 4) / log x := calc
        _ ≤ ∫ t in Set.Ioi x, (log 4 + 4) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_E₁Λ_div_mul_log_sq hx)
            (integrable_const_div_mul_log_sq (log 4 + 4) hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁Λ.le (by linarith)
        _ = _ := integ_div_mul_log_sq (log 4 + 4) hx
    grw [this]
    grind


theorem E₂Λ.bound : E₂Λ =O[atTop] (fun x ↦ 1 / log x) := by
    simp only [one_div, isBigO_iff, norm_eq_abs, norm_inv, eventually_atTop]
    use log 4 + 6, 2
    intro x hx
    convert E₂Λ.abs_le hx using 1
    have : 0 < log x := by apply log_pos; linarith
    grind [abs_of_pos this]


theorem E₂Λ.bound' : E₂Λ =o[atTop] (fun _ ↦ (1:ℝ)) := E₂Λ.bound.trans_isLittleO inv_log_eq_o_one


theorem log_zeta_eq_sum (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = ∑' n, Λ n / (n^s * log n) := by
  have hsc : (1 : ℝ) < ((s : ℂ)).re := by simpa using hs
  -- (II) Euler log product
  have hep := riemannZeta_eulerProduct_exp_log (s := (s : ℂ)) hsc
  set S : ℂ := ∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ))) with hS
  -- bridge: prime cpow equals real rpow
  have hcpow : ∀ p : Nat.Primes, (p : ℂ) ^ (-(s : ℂ)) = (((p : ℝ) ^ (-s) : ℝ) : ℂ) := by
    intro p
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast; ring_nf
  -- the real value of each prime term
  set z : Nat.Primes → ℝ := fun p => (p : ℝ) ^ (-s) with hz
  -- z p ∈ (0,1)
  have hz_pos : ∀ p : Nat.Primes, 0 < z p := fun p => by
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
    positivity
  have hz_lt_one : ∀ p : Nat.Primes, z p < 1 := by
    intro p
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    change (p : ℝ) ^ (-s) < 1
    rw [Real.rpow_neg (by positivity), inv_lt_one_iff₀]
    right
    exact (Real.one_lt_rpow_iff_of_pos (by positivity)).mpr (Or.inl ⟨hp1, by linarith⟩)
  -- each summand is the ofReal of a real number
  have hterm : ∀ p : Nat.Primes,
      -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ))) = ((-Real.log (1 - z p) : ℝ) : ℂ) := by
    intro p
    rw [hcpow p]
    have h1z : (0 : ℝ) < 1 - z p := by have := hz_lt_one p; linarith
    rw [show (1 : ℂ) - ((z p : ℝ) : ℂ) = (((1 - z p : ℝ)) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_log h1z.le]
    push_cast; ring
  -- (III) S is real: S = (Sr : ℂ) with Sr the real sum
  set Sr : ℝ := ∑' p : Nat.Primes, -Real.log (1 - z p) with hSr
  have hSeq : S = (Sr : ℂ) := by
    rw [hS, hSr, Complex.ofReal_tsum]
    exact tsum_congr hterm
  have hSim : S.im = 0 := by rw [hSeq]; exact Complex.ofReal_im _
  have hSre : S.re = Sr := by rw [hSeq]; exact Complex.ofReal_re _
  -- (IV) invert exp: log ζ = S
  have hlog_zeta : Complex.log (riemannZeta (s : ℂ)) = S := by
    rw [← hep, Complex.log_exp (by rw [hSim]; exact neg_lt_zero.mpr Real.pi_pos)
      (by rw [hSim]; exact Real.pi_pos.le)]
  -- relate Real.log ζ.re to S.re = Sr
  have hkey : Real.log (riemannZeta (s : ℂ)).re = Sr := by
    have hζim : (riemannZeta (s : ℂ)).im = 0 := riemannZeta_im_eq_zero_of_one_lt hs
    have hζeq : riemannZeta (s : ℂ) = ((riemannZeta (s : ℂ)).re : ℂ) := by
      apply Complex.ext <;> simp [hζim]
    have : Real.log (riemannZeta (s : ℂ)).re
        = (Complex.log (riemannZeta (s : ℂ))).re := by
      conv_rhs => rw [hζeq]
      rw [Complex.log_ofReal_re]
    rw [this, hlog_zeta, hSre]
  rw [hkey]
  -- now goal: Sr = ∑' n, Λ n / (n^s * log n)
  -- (V) expand each prime term via real Taylor series
  have habs : ∀ p : Nat.Primes, |z p| < 1 := by
    intro p
    rw [abs_of_pos (hz_pos p)]; exact hz_lt_one p
  have htaylor : ∀ p : Nat.Primes,
      HasSum (fun n : ℕ => (z p) ^ (n + 1) / (n + 1)) (-Real.log (1 - z p)) :=
    fun p => hasSum_pow_div_log_of_abs_lt_one (habs p)
  have hSr_double : Sr = ∑' (p : Nat.Primes) (n : ℕ), (z p) ^ (n + 1) / (n + 1) := by
    rw [hSr]
    exact tsum_congr fun p => ((htaylor p).tsum_eq).symm
  -- summability of the prime sum ∑ z p
  have hsummable_z : Summable z := Nat.Primes.summable_rpow.mpr (by linarith)
  -- summability of ∑ p, -log(1 - z p)
  have hsummable_prime : Summable (fun p : Nat.Primes => -Real.log (1 - z p)) := by
    have := Real.summable_log_one_add_of_summable hsummable_z.neg
    convert! this.neg using 1
  -- summability of g over the product
  have hg_nonneg : ∀ pk : Nat.Primes × ℕ, 0 ≤ (z pk.1) ^ (pk.2 + 1) / (pk.2 + 1) := by
    intro pk; positivity [hz_pos pk.1]
  have hsummable_g : Summable (fun pk : Nat.Primes × ℕ => (z pk.1) ^ (pk.2 + 1) / (pk.2 + 1)) := by
    rw [summable_prod_of_nonneg hg_nonneg]
    refine ⟨fun p => (htaylor p).summable, ?_⟩
    refine hsummable_prime.congr (fun p => ?_)
    exact ((htaylor p).tsum_eq).symm
  -- pointwise: F (p^(n+1)) = g (p, n)
  have hpoint : ∀ (p : Nat.Primes) (n : ℕ),
      Λ ((p : ℕ) ^ (n + 1)) /
        ((((p : ℕ) ^ (n + 1) : ℕ) : ℝ) ^ s * Real.log (((p : ℕ) ^ (n + 1) : ℕ) : ℝ))
      = (z p) ^ (n + 1) / (n + 1) := by
    intro p n
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
    rw [vonMangoldt_apply_pow (Nat.succ_ne_zero n), vonMangoldt_apply_prime p.prop]
    have hcast : (((p : ℕ) ^ (n + 1) : ℕ) : ℝ) = (p : ℝ) ^ (n + 1) := by push_cast; ring
    rw [hcast, Real.log_pow]
    rw [show (z p) ^ (n + 1) = ((p : ℝ) ^ (n + 1)) ^ (-s) by
      rw [hz]; rw [← Real.rpow_natCast ((p : ℝ) ^ (-s)) (n + 1),
        ← Real.rpow_natCast ((p : ℝ)) (n + 1), ← Real.rpow_mul (by positivity),
        ← Real.rpow_mul (by positivity)]; ring_nf]
    rw [Real.rpow_neg (by positivity)]
    field_simp
    push_cast
    ring
  -- (VI) reindex via the prime-power equivalence
  set F : ℕ → ℝ := fun n => Λ n / ((n : ℝ) ^ s * Real.log n) with hF
  -- support of F is contained in prime powers
  have hsupp : Function.support F ⊆ {n : ℕ | IsPrimePow n} := by
    intro n hn
    rw [Function.mem_support] at hn
    simp only [Set.mem_ofPred_eq]
    by_contra hpp
    apply hn
    simp only [hF, vonMangoldt_eq_zero_iff.mpr hpp, zero_div]
  -- the product sum equals the subtype sum
  have hprod_eq : (∑' pk : Nat.Primes × ℕ, (z pk.1) ^ (pk.2 + 1) / (pk.2 + 1))
      = ∑' m : {n : ℕ // IsPrimePow n}, F m.val := by
    rw [← Equiv.tsum_eq Nat.Primes.prodNatEquiv (fun m : {n : ℕ // IsPrimePow n} => F m.val)]
    apply tsum_congr
    intro pk
    rw [Nat.Primes.coe_prodNatEquiv_apply, hF]
    exact (hpoint pk.1 pk.2).symm
  -- assemble
  rw [hSr_double, ← hsummable_g.tsum_prod' (fun p => (htaylor p).summable), hprod_eq]
  exact tsum_subtype_eq_of_support_subset hsupp

section
open MeasureTheory Set

-- Helpers for `log_zeta_eq_integ` (#1583): Abel summation / sum-integral interchange.
namespace LogZetaInteg

/- The summatory coefficient `Λ d / (d log d)`. -/
private noncomputable def c (d : ℕ) : ℝ := Λ d / (d * Real.log d)

/- The per-index integrand: `c d` times the rpow restricted to `Ici (d:ℝ)`. -/
private noncomputable def f (s : ℝ) (d : ℕ) (x : ℝ) : ℝ :=
    c d * (Set.Ici (d:ℝ)).indicator (fun x => x ^ (-s)) x

private lemma c_zero : c 0 = 0 := by simp [c]
private lemma c_one : c 1 = 0 := by simp [c, vonMangoldt_apply_one]

/- `c d ≥ 0` for all `d`. -/
private lemma c_nonneg (d : ℕ) : 0 ≤ c d := by
  unfold c
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; simp
  · apply div_nonneg vonMangoldt_nonneg
    have : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
    have hlog : 0 ≤ Real.log d := Real.log_natCast_nonneg d
    positivity

/- General comparison majorant: `(log n)^a / n^s` is summable for any real `a` and `s > 1`,
since `(log x)^a = o(x^ε)` for every `ε > 0`. All the summability conditions below reduce to
this by domination. -/
private lemma summable_log_rpow_div_rpow (a : ℝ) {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => (Real.log n) ^ a / (n:ℝ) ^ s) := by
  have hε : (0:ℝ) < (s - 1) / 2 := by linarith
  refine summable_of_isBigO_nat (g := fun n : ℕ => (n:ℝ) ^ ((s - 1) / 2 - s)) ?_ ?_
  · rw [Real.summable_nat_rpow]; linarith
  · have ho : (fun x : ℝ => (Real.log x) ^ a) =O[atTop] (fun x : ℝ => x ^ ((s - 1) / 2)) :=
      (isLittleO_log_rpow_rpow_atTop a hε).isBigO
    have hmul : (fun x : ℝ => (Real.log x) ^ a / x ^ s)
        =O[atTop] (fun x : ℝ => x ^ ((s - 1) / 2) / x ^ s) := by
      simpa only [div_eq_mul_inv] using ho.mul (isBigO_refl (fun x : ℝ => (x ^ s)⁻¹) atTop)
    have heq : (fun x : ℝ => x ^ ((s - 1) / 2) / x ^ s)
        =ᶠ[atTop] (fun x : ℝ => x ^ ((s - 1) / 2 - s)) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [← Real.rpow_sub hx]
    exact (hmul.trans_eventuallyEq heq).natCast_atTop

/- Real summability of `Λ n / n^s` for `s > 1`: dominated by `log n / n^s` via `Λ n ≤ log n`. -/
private lemma summable_vonMangoldt_div_rpow (s : ℝ) (hs : 1 < s) :
    Summable (fun n : ℕ => (Λ n : ℝ) / (n:ℝ) ^ s) := by
  refine Summable.of_nonneg_of_le (fun n => div_nonneg vonMangoldt_nonneg (by positivity)) ?_
    (summable_log_rpow_div_rpow 1 hs)
  intro n
  rw [Real.rpow_one]
  gcongr
  exact vonMangoldt_le_log

/- Real summability of `Λ n / (n^s * log n)` for `s > 1` (compare with the previous lemma). -/
private lemma summable_c_term (s : ℝ) (hs : 1 < s) :
    Summable (fun d : ℕ => c d * ((d:ℝ) ^ (1 - s) / (s - 1))) := by
  have hs1 : (0:ℝ) < s - 1 := by linarith
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- Majorise by `(1/(log 2·(s-1)))·(Λ d/d^s)`, summable by `summable_vonMangoldt_div_rpow`.
  refine Summable.of_nonneg_of_le (fun d => ?_) (fun d => ?_)
    ((summable_vonMangoldt_div_rpow s hs).mul_left (1 / (Real.log 2 * (s - 1))))
  · -- `0 ≤ c d * (d^(1-s)/(s-1))`
    refine mul_nonneg (c_nonneg d) (div_nonneg ?_ hs1.le)
    rcases eq_or_ne (d:ℝ) 0 with hd | hd
    · rw [hd, Real.zero_rpow (by linarith : (1 - s) ≠ 0)]
    · positivity
  · -- `c d * (d^(1-s)/(s-1)) ≤ (1/(log 2·(s-1)))·(Λ d/d^s)`
    rcases lt_or_ge d 2 with hd | hd
    · have hc : c d = 0 := by interval_cases d <;> simp [c_zero, c_one]
      rw [hc, zero_mul]
      exact mul_nonneg (by positivity) (div_nonneg vonMangoldt_nonneg (by positivity))
    · have hd2 : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
      have hd0 : (0:ℝ) < (d:ℝ) := by linarith
      have hlogge : Real.log 2 ≤ Real.log d := Real.log_le_log (by norm_num) hd2
      have hds : (0:ℝ) < (d:ℝ) ^ s := Real.rpow_pos_of_pos hd0 s
      have hkey : c d * ((d:ℝ) ^ (1 - s) / (s - 1)) = Λ d / ((d:ℝ) ^ s * Real.log d * (s - 1)) := by
        unfold c
        rw [show (1 - s : ℝ) = -s + 1 by ring, Real.rpow_add hd0, Real.rpow_one, Real.rpow_neg hd0.le]
        field_simp
      -- `Λ d / (d^s·log d·(s-1)) ≤ Λ d / (d^s·log 2·(s-1))` since `log 2 ≤ log d`.
      have hcb : (d:ℝ) ^ s * Real.log 2 * (s - 1) ≤ (d:ℝ) ^ s * Real.log d * (s - 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogge hds.le) hs1.le
      rw [hkey, show (1 / (Real.log 2 * (s - 1))) * ((Λ d : ℝ) / (d:ℝ) ^ s)
          = Λ d / ((d:ℝ) ^ s * Real.log 2 * (s - 1)) from by field_simp]
      exact div_le_div_of_nonneg_left vonMangoldt_nonneg (by positivity) hcb

/- The integration-by-parts identity (#1583), with explicit qualifiers. -/
theorem log_zeta_eq_integ_aux (s : ℝ) (hs : 1 < s) :
    Real.log (riemannZeta (s:ℂ)).re =
      (s - 1) * ∫ x in Set.Ioi 1, (Real.log (Real.log x) + γ + E₂Λ x) * x ^ (-s) := by
  rw [Mertens.log_zeta_eq_sum s hs]
  symm
  have hstep1 : ∀ x ∈ Set.Ioi (1:ℝ),
      (Real.log (Real.log x) + γ + E₂Λ x) * x ^ (-s)
        = (∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, c d) * x ^ (-s) := by
    intro x hx
    simp only [Mertens.E₂Λ, c]
    ring
  have hstep2 : ∀ x ∈ Set.Ioi (1:ℝ),
      (Real.log (Real.log x) + γ + E₂Λ x) * x ^ (-s) = ∑' d : ℕ, f s d x := by
    intro x hx
    rw [hstep1 x hx]
    simp only [f]
    rw [Finset.sum_mul]
    have hx0 : (0:ℝ) ≤ x := by have := hx; simp only [Set.mem_Ioi] at this; linarith
    rw [tsum_eq_sum (s := Finset.Ioc 0 ⌊x⌋₊) ?_]
    · apply Finset.sum_congr rfl
      intro d hd
      simp only [Finset.mem_Ioc] at hd
      have hdx : (d:ℝ) ≤ x := by
        rw [← Nat.le_floor_iff hx0]; exact hd.2
      rw [Set.indicator_of_mem (by simpa using hdx)]
    · intro d hd
      simp only [Finset.mem_Ioc, not_and, not_le] at hd
      rcases Nat.eq_zero_or_pos d with hd0 | hd0
      · subst hd0; simp [c_zero]
      · have hfloor : ⌊x⌋₊ < d := hd hd0
        have hdx : x < (d:ℝ) := by
          rw [← Nat.floor_lt hx0]; exact hfloor
        rw [Set.indicator_of_notMem (by simpa using not_le.mpr hdx)]
        ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hstep2]
  have hperterm : ∀ d : ℕ, ∫ x in Set.Ioi (1:ℝ), f s d x = c d * ((d:ℝ) ^ (1 - s) / (s - 1)) := by
    intro d
    rcases Nat.eq_zero_or_pos d with hd0 | hd0
    · subst hd0; simp [f, c_zero]
    simp only [f]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.setIntegral_indicator measurableSet_Ici]
    congr 1
    have hdR : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd0
    have hdR0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd0
    set A : Set ℝ := Set.Ioi (1:ℝ) ∩ Set.Ici (d:ℝ) with hA
    have hae : A =ᵐ[volume] Set.Ioi (d:ℝ) := by
      have h1 : A =ᵐ[volume] (Set.Ici (1:ℝ) ∩ Set.Ici (d:ℝ) : Set ℝ) :=
        MeasureTheory.ae_eq_set_inter MeasureTheory.Ioi_ae_eq_Ici (ae_eq_refl _)
      rw [Set.Ici_inter_Ici, max_eq_right hdR] at h1
      exact h1.trans MeasureTheory.Ioi_ae_eq_Ici.symm
    rw [MeasureTheory.setIntegral_congr_set hae]
    rw [integral_Ioi_rpow_of_lt (by linarith : (-s:ℝ) < -1) hdR0,
      show (-s + 1 : ℝ) = 1 - s by ring]
    have hs1 : (1 - s) ≠ 0 := by linarith
    have hs2 : (s - 1) ≠ 0 := by linarith
    field_simp
    ring
  have hint : ∀ d : ℕ, MeasureTheory.IntegrableOn (f s d) (Set.Ioi (1:ℝ)) := by
    intro d
    unfold f
    apply MeasureTheory.Integrable.const_mul
    rw [show MeasureTheory.Integrable ((Set.Ici (d:ℝ)).indicator fun x => x ^ (-s))
        (volume.restrict (Set.Ioi (1:ℝ)))
      ↔ MeasureTheory.IntegrableOn ((Set.Ici (d:ℝ)).indicator fun x => x ^ (-s))
          (Set.Ioi (1:ℝ)) volume from Iff.rfl,
      MeasureTheory.integrableOn_indicator_iff measurableSet_Ici]
    apply MeasureTheory.IntegrableOn.mono_set
      (integrableOn_Ioi_rpow_of_lt (by linarith : (-s:ℝ) < -1) (by norm_num : (0:ℝ) < 1/2))
    intro x hx
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioi] at hx ⊢
    linarith [hx.2]
  have hnorm_int : ∀ d : ℕ,
      ∫ x in Set.Ioi (1:ℝ), ‖f s d x‖ = c d * ((d:ℝ) ^ (1 - s) / (s - 1)) := by
    intro d
    rw [← hperterm d]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hfnn : 0 ≤ f s d x := by
      simp only [f]
      apply mul_nonneg (c_nonneg d)
      by_cases hxd : (d:ℝ) ≤ x
      · rw [Set.indicator_of_mem (by simpa using hxd)]
        exact le_of_lt (Real.rpow_pos_of_pos (by linarith) _)
      · rw [Set.indicator_of_notMem (by simpa using hxd)]
    change ‖f s d x‖ = f s d x
    rw [Real.norm_eq_abs, abs_of_nonneg hfnn]
  have hinterchange : ∫ x in Set.Ioi (1:ℝ), ∑' d : ℕ, f s d x
      = ∑' d : ℕ, ∫ x in Set.Ioi (1:ℝ), f s d x := by
    refine (MeasureTheory.integral_tsum_of_summable_integral_norm hint ?_).symm
    apply (summable_c_term s hs).congr
    intro d
    exact (hnorm_int d).symm
  rw [hinterchange]
  simp_rw [hperterm]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro d
  rcases Nat.eq_zero_or_pos d with hd0 | hd0
  · subst hd0; simp [c_zero]
  · have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd0
    have hsub : (d:ℝ) ^ (1 - s) = (d:ℝ) ^ (-s) * (d:ℝ) := by
      rw [show (1 - s : ℝ) = -s + 1 by ring, Real.rpow_add hdR, Real.rpow_one]
    have hs1 : s - 1 ≠ 0 := by linarith
    have hneg : (d:ℝ) ^ (-s) = ((d:ℝ) ^ s)⁻¹ := by
      rw [Real.rpow_neg (le_of_lt hdR)]
    unfold c
    rw [hsub, hneg]
    field_simp

end LogZetaInteg
end


private theorem log_zeta_eq_integ (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = (s - 1) * ∫ x in .Ioi 1, (log (log x) + γ + E₂Λ x) * x^(-s) :=
  LogZetaInteg.log_zeta_eq_integ_aux s hs


private theorem mul_integ_log_log_eq (s : ℝ) (hs : 1 < s) :
    (s - 1) * ∫ x in .Ioi 1, log (log x) * x^(-s) = - log (s - 1) + deriv Gamma 1 :=
  mul_integ_log_log_eq_aux s hs


private theorem mul_integ_gamma_eq (s) (hs : 1 < s) : (s - 1) * ∫ x in .Ioi 1, γ * x^(-s) = γ := by
  rw [MeasureTheory.integral_const_mul γ (· ^ (-s)), @integral_Ioi_rpow_of_lt (-s), one_rpow] <;>
    grind

-- Integrability helpers for the integral splitting in `log_zeta_eq` (#1319).
-- Each summand of `(log (log x) + γ + E₂Λ x) * x^(-s)` is separately integrable on `Ioi 1`.

/- Comparison test for `x ^ (-s)` decay: if `f` is measurable and dominated by `B * x ^ a` on
`Set.Ioi c` (with `0 < c` and `a + 1 < s`), then `fun x ↦ f x * x ^ (-s)` is integrable there.
This is the integral analogue of the summability of `O(x ^ a / x ^ s)` series and packages the
decay estimate reused for each tail in `log_zeta_eq`. -/
private theorem integrableOn_Ioi_mul_rpow_neg_of_abs_le
    {c B a s : ℝ} (hc : 0 < c) (has : a + 1 < s) {f : ℝ → ℝ} (hf : Measurable f)
    (hbound : ∀ x ∈ Set.Ioi c, |f x| ≤ B * x ^ a) :
    MeasureTheory.IntegrableOn (fun x => f x * x ^ (-s)) (Set.Ioi c) := by
  have hg : MeasureTheory.IntegrableOn (fun x => B * x ^ (a - s)) (Set.Ioi c) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : a - s < -1) hc).const_mul B
  refine MeasureTheory.Integrable.mono' hg
    (hf.mul (measurable_id.pow_const (-s))).aestronglyMeasurable ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
  have hxpos : (0:ℝ) < x := hc.trans hx
  have hxs : (0:ℝ) < x ^ (-s) := Real.rpow_pos_of_pos hxpos _
  rw [norm_mul, norm_eq_abs, norm_eq_abs, abs_of_pos hxs]
  calc |f x| * x ^ (-s) ≤ B * x ^ a * x ^ (-s) :=
        mul_le_mul_of_nonneg_right (hbound x hx) hxs.le
    _ = B * x ^ (a - s) := by rw [mul_assoc, ← Real.rpow_add hxpos, sub_eq_add_neg]

/- `log (log x) * x ^ (-s)` is integrable on `Ioi 1` for `s > 1`
(log-log singularity at `1` is integrable; `x^(-s)` gives decay). -/
private theorem integrableOn_log_log_mul_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun x => log (log x) * x ^ (-s)) (Set.Ioi 1) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (1:ℝ) ≤ 2)]
  apply MeasureTheory.IntegrableOn.union
  · -- Near `1`: `log (log x)` is integrable (log-log singularity) and `x^(-s) ≤ 1`.
    have hll : MeasureTheory.IntegrableOn (fun x => log (log x)) (Set.Ioc 1 2) := by
      have h : IntervalIntegrable (log ∘ log) MeasureTheory.volume 1 2 := by
        apply MeromorphicOn.intervalIntegrable_log
        intro x hx
        rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)] at hx
        exact (analyticAt_log (by linarith [hx.1] : 0 < x)).meromorphicAt
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp h
    have hmul : MeasureTheory.IntegrableOn (fun x => x ^ (-s) * log (log x)) (Set.Ioc 1 2) := by
      apply hll.bdd_mul (c := 1)
      · fun_prop
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
        rw [norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith [hx.1] : (0:ℝ) ≤ x) _)]
        calc x ^ (-s) ≤ (1:ℝ) ^ (-s) :=
              Real.rpow_le_rpow_of_nonpos (by norm_num) hx.1.le (by linarith)
          _ = 1 := Real.one_rpow _
    simpa [mul_comm] using hmul
  · -- Tail (`Ioi 2`): `|log (log x)| ≤ (1/ε + |log (log 2)|)·x^ε` with `ε = (s-1)/2`, `ε + 1 < s`.
    set ε := (s - 1) / 2 with hε
    have hεpos : 0 < ε := by rw [hε]; linarith
    refine integrableOn_Ioi_mul_rpow_neg_of_abs_le (a := ε) (B := 1 / ε + |log (log 2)|)
      (by norm_num) (by rw [hε]; linarith) (Real.measurable_log.comp Real.measurable_log) ?_
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hx1 : (1:ℝ) ≤ x ^ ε := Real.one_le_rpow (by linarith) hεpos.le
    have hlogx : 0 < log x := Real.log_pos (by linarith)
    have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
    have hmono : log 2 ≤ log x := Real.log_le_log (by norm_num) (by linarith)
    have hub : log (log x) ≤ x ^ ε / ε :=
      calc log (log x) ≤ log x := (Real.log_le_sub_one_of_pos hlogx).trans (by linarith)
        _ ≤ x ^ ε / ε := Real.log_le_rpow_div (by linarith) hεpos
    have hlb : log (log 2) ≤ log (log x) := Real.log_le_log hlog2 hmono
    have hxε : 0 ≤ x ^ ε / ε := by positivity
    calc |log (log x)| ≤ x ^ ε / ε + |log (log 2)| := by
          rw [abs_le]
          exact ⟨by linarith [neg_abs_le (log (log 2))],
            by linarith [abs_nonneg (log (log 2))]⟩
      _ ≤ (1 / ε + |log (log 2)|) * x ^ ε := by
          have h2 : |log (log 2)| ≤ |log (log 2)| * x ^ ε := le_mul_of_one_le_right (abs_nonneg _) hx1
          have h1 : x ^ ε / ε = 1 / ε * x ^ ε := by ring
          rw [add_mul]; linarith

/- `γ * x ^ (-s)` is integrable on `Ioi 1` for `s > 1`. -/
private theorem integrableOn_γ_mul_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun x => γ * x ^ (-s)) (Set.Ioi 1) := by
  exact (integrableOn_Ioi_rpow_of_lt (by linarith : -s < -1) one_pos).const_mul γ

/- `E₂Λ x * x ^ (-s)` is integrable on `Ioi 1` for `s > 1`
(`E₂Λ ~ -log(log x)` near `1`, and `E₂Λ = O(1/log x)` at `∞`). -/
private theorem integrableOn_E₂Λ_mul_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun x => E₂Λ x * x ^ (-s)) (Set.Ioi 1) := by
  rw [← Set.Ioo_union_Ici_eq_Ioi (by norm_num : (1:ℝ) < 2)]
  apply MeasureTheory.IntegrableOn.union
  · -- Near `1`: `⌊x⌋₊ = 1`, the sum is `0`, so `E₂Λ x = -log (log x) - γ`.
    have hsub : Set.Ioo (1:ℝ) 2 ⊆ Set.Ioi 1 := fun x hx => hx.1
    have h1 := (integrableOn_γ_mul_rpow s hs).mono_set hsub
    have h2 := (integrableOn_log_log_mul_rpow s hs).mono_set hsub
    have hb : MeasureTheory.IntegrableOn
        (fun x => -(log (log x) * x ^ (-s)) - γ * x ^ (-s)) (Set.Ioo 1 2) :=
      h2.neg.sub h1
    apply hb.congr_fun _ measurableSet_Ioo
    intro x hx
    simp only [Set.mem_Ioo] at hx
    have hfloor : ⌊ x ⌋₊ = 1 := by
      rw [Nat.floor_eq_iff (by linarith)]
      exact ⟨by push_cast; linarith [hx.1], by push_cast; linarith [hx.2]⟩
    have hsum : (∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / ((d:ℝ) * log d)) = 0 := by rw [hfloor]; norm_num
    change -(log (log x) * x ^ (-s)) - γ * x ^ (-s)
        = (∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x) - γ) * x ^ (-s)
    rw [hsum]; ring
  · -- Tail: `|E₂Λ x| ≤ (log 4 + 6)/log x ≤ (log 4 + 6)/log 2` is bounded (`a = 0`), times decay.
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    refine integrableOn_Ioi_mul_rpow_neg_of_abs_le (a := 0) (B := (log 4 + 6) / log 2)
      (by norm_num) (by linarith) (by fun_prop) ?_
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
    have hc : 0 ≤ log 4 + 6 := by positivity
    rw [Real.rpow_zero, mul_one]
    have hb2 : (log 4 + 6) / log x ≤ (log 4 + 6) / log 2 :=
      div_le_div_of_nonneg_left hc hlog2 (Real.log_le_log (by norm_num) (le_of_lt hx))
    exact (E₂Λ.abs_le (le_of_lt hx)).trans hb2


private theorem log_zeta_eq (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = - log (s - 1) + deriv Gamma 1 + γ + (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x^(-s) := by
  -- Start from the integration-by-parts identity (#1583).
  rw [log_zeta_eq_integ s hs]
  -- Linearity of the integral: split into the three summands (uses the integrability helpers).
  have key : (∫ x in Set.Ioi 1, (log (log x) + γ + E₂Λ x) * x ^ (-s))
      = (∫ x in Set.Ioi 1, log (log x) * x ^ (-s))
        + (∫ x in Set.Ioi 1, γ * x ^ (-s))
        + (∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s)) := by
    rw [← MeasureTheory.integral_add (integrableOn_log_log_mul_rpow s hs)
      (integrableOn_γ_mul_rpow s hs)]
    rw [← MeasureTheory.integral_add (f := fun x => log (log x) * x ^ (-s) + γ * x ^ (-s))
      (g := fun x => E₂Λ x * x ^ (-s))
      ((integrableOn_log_log_mul_rpow s hs).add (integrableOn_γ_mul_rpow s hs))
      (integrableOn_E₂Λ_mul_rpow s hs)]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x _
    ring
  -- Apply sublemmas #1584 and #1585, then finish algebraically.
  rw [key, mul_add, mul_add, mul_integ_log_log_eq s hs, mul_integ_gamma_eq s hs]

private lemma zeta_pole_mul_re_tendsto_one :
    Filter.Tendsto (fun s : ℝ => (s - 1) * (riemannZeta (s : ℂ)).re)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
  have hofReal :
      Filter.Tendsto (fun s : ℝ => (s : ℂ)) (nhdsWithin 1 (Set.Ioi 1))
        (nhdsWithin (1 : ℂ) ({1} : Set ℂ)ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact Set.mem_compl_singleton_iff.mpr (by
        norm_num
        exact ne_of_gt (Set.mem_Ioi.mp hs))
  have hcomplex :
      Filter.Tendsto (fun s : ℝ => ((s : ℂ) - 1) * riemannZeta (s : ℂ))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) :=
    riemannZeta_residue_one.comp hofReal
  have hreal :
      Filter.Tendsto
        (fun s : ℝ => (((s : ℂ) - 1) * riemannZeta (s : ℂ)).re)
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (1 : ℝ)) :=
    (Complex.continuous_re.tendsto (1 : ℂ)).comp hcomplex
  simpa [Complex.ofReal_sub, Complex.ofReal_mul] using hreal


private theorem log_zeta_limit :
    Filter.Tendsto
      (fun s : ℝ => Real.log (riemannZeta (s : ℂ)).re + Real.log (s - 1))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
  have hlog :
      Filter.Tendsto
        (fun s : ℝ => Real.log ((s - 1) * (riemannZeta (s : ℂ)).re))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (Real.log 1)) :=
    (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
      zeta_pole_mul_re_tendsto_one
  have hEq :
      (fun s : ℝ => Real.log (riemannZeta (s : ℂ)).re + Real.log (s - 1))
        =ᶠ[nhdsWithin 1 (Set.Ioi 1)]
      fun s : ℝ => Real.log ((s - 1) * (riemannZeta (s : ℂ)).re) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hspos : 0 < s - 1 := sub_pos.mpr (Set.mem_Ioi.mp hs)
    have hzpos : 0 < (riemannZeta (s : ℂ)).re :=
      riemannZeta_re_pos_of_one_lt (Set.mem_Ioi.mp hs)
    rw [Real.log_mul hspos.ne' hzpos.ne']
    ring
  simpa using hlog.congr' (hEq.mono fun s hs => hs.symm)

-- Helpers for `deriv_gamma_add_γ_eq_zero` (#1320): take `s → 1⁺` in `log_zeta_eq`.
section
open MeasureTheory Set

/- `E₂Λ` is measurable: its Mangoldt-sum part factors through `⌊·⌋₊` and the rest is
continuous/measurable. -/
private lemma measurable_E₂Λ : Measurable E₂Λ := by fun_prop

/- On `(1,2)` the Mangoldt sum is empty (`⌊x⌋₊ = 1`), so `E₂Λ x = - log (log x) - γ`. -/
private lemma E₂Λ_eq_on_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (1 : ℝ) 2) :
    E₂Λ x = - log (log x) - γ := by
  obtain ⟨h1, h2⟩ := hx
  have hf : ⌊x⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by linarith)]
    exact ⟨by exact_mod_cast h1.le, by exact_mod_cast h2⟩
  unfold E₂Λ
  rw [hf]
  simp

/- Domination of `|E₂Λ|` near `1`: for `x ∈ (1,2)`, `|E₂Λ x| ≤ |log (x-1)| + log 2 + |γ|`,
the RHS being integrable on `(1,2)` (the `log (x-1)` is integrable across the singularity at `1`). -/
private lemma abs_E₂Λ_le_on_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (1 : ℝ) 2) :
    |E₂Λ x| ≤ |log (x - 1)| + log 2 + |γ| := by
  obtain ⟨hx1, hx2⟩ := hx
  have hloglog : |log (log x)| ≤ |log (x - 1)| + log 2 := by
    have hxpos : (0:ℝ) < x := by linarith
    have hlogx_pos : 0 < log x := Real.log_pos hx1
    have hxm1 : 0 < x - 1 := by linarith
    have hub : log x ≤ x - 1 := by have := Real.log_le_sub_one_of_pos hxpos; linarith
    have hlb2 : (x - 1) / 2 ≤ log x := by
      have h := Real.log_le_sub_one_of_pos (x := 1 / x) (by positivity)
      rw [Real.log_div one_ne_zero (by positivity), Real.log_one] at h
      simp only [zero_sub] at h
      have h12 : (x - 1) / 2 ≤ 1 - 1 / x := by
        rw [← sub_nonneg]
        have e : (1 - 1 / x) - (x - 1) / 2 = (3 * x - 2 - x ^ 2) / (2 * x) := by field_simp; ring
        rw [e]; exact div_nonneg (by nlinarith [hx1, hx2]) (by positivity)
      linarith
    have hupper : log (log x) ≤ log (x - 1) := Real.log_le_log hlogx_pos hub
    have hlower : log (x - 1) - log 2 ≤ log (log x) := by
      have := Real.log_le_log (show (0:ℝ) < (x - 1) / 2 by positivity) hlb2
      rwa [Real.log_div (by linarith) (by norm_num)] at this
    have h2 : (0:ℝ) ≤ log 2 := Real.log_nonneg (by norm_num)
    rw [abs_le]
    exact ⟨by have := neg_abs_le (log (x - 1)); linarith,
          by have := le_abs_self (log (x - 1)); linarith⟩
  rw [E₂Λ_eq_on_Ioo ⟨hx1, hx2⟩]
  have htri : |(- log (log x) - γ)| ≤ |log (log x)| + |γ| := by
    have h := abs_sub (-log (log x)) γ
    rwa [abs_neg] at h
  linarith

/- Constant bound on `|E₂Λ|` for `2 ≤ x`, sharpening `E₂Λ.abs_le` via `log 2 ≤ log x`. -/
private lemma abs_E₂Λ_le_const {x : ℝ} (hx : 2 ≤ x) :
    |E₂Λ x| ≤ (log 4 + 6) / log 2 :=
  (E₂Λ.abs_le hx).trans <| div_le_div_of_nonneg_left (by positivity)
    (Real.log_pos (by norm_num)) (Real.log_le_log (by norm_num) hx)

/- The near-1 dominating function `|log (x-1)| + log 2 + |γ|` is integrable on `(1,2)`
(it dominates `|E₂Λ|` there, handling the log-log singularity at `1`). -/
private lemma integrableOn_log_sub_one_bound :
    IntegrableOn (fun x => |log (x - 1)| + log 2 + |γ|) (Set.Ioo 1 2) volume := by
  have hlog : IntegrableOn (fun x => |log (x - 1)|) (Set.Ioo 1 2) volume := by
    have h0 : IntervalIntegrable (fun x => log x) volume 0 1 :=
      intervalIntegral.intervalIntegrable_log'
    have h1 : IntervalIntegrable (fun x => log (x - 1)) volume (0 + 1) (1 + 1) :=
      h0.comp_sub_right 1
    norm_num at h1
    exact (h1.1.mono_set Set.Ioo_subset_Ioc_self).abs
  have hc : IntegrableOn (fun _ : ℝ => log 2 + |γ|) (Set.Ioo (1 : ℝ) 2) volume :=
    integrableOn_const (measure_Ioo_lt_top).ne (by finiteness)
  have hsum : IntegrableOn (fun x => |log (x - 1)| + (log 2 + |γ|)) (Set.Ioo 1 2) volume :=
    hlog.add hc
  exact hsum.congr_fun (fun x _ => by ring) measurableSet_Ioo

/- `E₂Λ` is integrable on every bounded interval `(1, X)` (`X ≥ 2`): log-log singularity near
`1` plus boundedness on `[2, X]`. -/
private lemma integrableOn_E₂Λ_Ioo {X : ℝ} (_hX : 2 ≤ X) :
    IntegrableOn E₂Λ (Set.Ioo 1 X) volume := by
  have hsub : Set.Ioo (1 : ℝ) X ⊆ Set.Ioo 1 2 ∪ Set.Icc 2 X := by
    intro x hx; simp only [Set.mem_Ioo, Set.mem_union, Set.mem_Icc] at *
    rcases lt_or_ge x 2 with h | h
    · exact Or.inl ⟨hx.1, h⟩
    · exact Or.inr ⟨h, hx.2.le⟩
  apply IntegrableOn.mono_set _ hsub
  apply IntegrableOn.union
  · have hg := integrableOn_log_sub_one_bound
    refine Integrable.mono' hg measurable_E₂Λ.aestronglyMeasurable ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs]; exact abs_E₂Λ_le_on_Ioo hx
  · refine Integrable.mono' (g := fun _ => (log 4 + 6) / log 2) ?_
      measurable_E₂Λ.aestronglyMeasurable ?_
    · exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by finiteness)
    · filter_upwards [self_mem_ae_restrict measurableSet_Icc] with x hx
      rw [Real.norm_eq_abs]; exact abs_E₂Λ_le_const hx.1

/- The error integral, scaled by `(s-1)`, vanishes as `s → 1⁺` (uses `E₂Λ =o(1)`). -/
private lemma sub_one_mul_integral_E₂Λ_tendsto :
    Filter.Tendsto (fun s : ℝ => (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  -- Choose `X ≥ 2` so that `|E₂Λ x| ≤ ε/2` for `x ≥ X` (from `E₂Λ =o(1)`).
  obtain ⟨X₀, hX₀⟩ : ∃ X, ∀ x ≥ X, |E₂Λ x| ≤ ε / 2 := by
    have := E₂Λ.bound'.def (by positivity : (0:ℝ) < ε / 2)
    simp only [Real.norm_eq_abs, abs_one, mul_one] at this
    rw [Filter.eventually_atTop] at this; exact this
  set X := max X₀ 2 with hXdef
  have hX2 : 2 ≤ X := le_max_right _ _
  have hXge : ∀ x ≥ X, |E₂Λ x| ≤ ε / 2 := fun x hx => hX₀ x (le_trans (le_max_left _ _) hx)
  -- `B` is the (finite) mass of `|E₂Λ|` on `(1, X)`.
  set B := ∫ x in Set.Ioo 1 X, |E₂Λ x| with hBdef
  have hB0 : 0 ≤ B := setIntegral_nonneg measurableSet_Ioo (fun x _ => abs_nonneg _)
  refine ⟨min 1 (ε / 2 / (B + 1)), by positivity, ?_⟩
  intro s hs hdist
  simp only [Set.mem_Ioi] at hs
  rw [Real.dist_eq] at hdist
  have hs1 : s - 1 < min 1 (ε / 2 / (B + 1)) := by
    rw [abs_of_pos (by linarith)] at hdist; exact hdist
  have hsm1 : 0 < s - 1 := by linarith
  -- `|E₂Λ|·x^(-s)` is integrable on `(1,∞)` and its subintervals.
  have hintAbs : IntegrableOn (fun x => |E₂Λ x| * x ^ (-s)) (Set.Ioi 1) volume := by
    have h2 : IntegrableOn (fun x => |E₂Λ x * x ^ (-s)|) (Set.Ioi 1) volume :=
      (integrableOn_E₂Λ_mul_rpow s hs).abs
    refine h2.congr_fun ?_ measurableSet_Ioi
    intro x hx; simp only [Set.mem_Ioi] at hx
    change |E₂Λ x * x ^ (-s)| = |E₂Λ x| * x ^ (-s)
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  have hintAbsIoc : IntegrableOn (fun x => |E₂Λ x| * x ^ (-s)) (Set.Ioc 1 X) volume :=
    hintAbs.mono_set Set.Ioc_subset_Ioi_self
  have hintAbsIoiX : IntegrableOn (fun x => |E₂Λ x| * x ^ (-s)) (Set.Ioi X) volume :=
    hintAbs.mono_set (Set.Ioi_subset_Ioi (by linarith))
  -- Split `∫_{(1,∞)} = ∫_{(1,X]} + ∫_{(X,∞)}`.
  have hsplit : ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) =
      (∫ x in Set.Ioc 1 X, |E₂Λ x| * x ^ (-s)) + ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s) := by
    have hu : Set.Ioi (1:ℝ) = Set.Ioc 1 X ∪ Set.Ioi X :=
      (Set.Ioc_union_Ioi_eq_Ioi (by linarith)).symm
    rw [hu, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hintAbs.mono_set (by rw [hu]; exact Set.subset_union_left))
      (hintAbs.mono_set (by rw [hu]; exact Set.subset_union_right))]
  -- Piece 1: on `(1,X]`, `x^(-s) ≤ 1`, so the integral is `≤ B`.
  have hp1 : ∫ x in Set.Ioc 1 X, |E₂Λ x| * x ^ (-s) ≤ B := by
    rw [hBdef]
    have ha : IntegrableOn (fun x => |E₂Λ x|) (Set.Ioo 1 X) volume := (integrableOn_E₂Λ_Ioo hX2).abs
    have habsIoc : IntegrableOn (fun x => |E₂Λ x|) (Set.Ioc 1 X) volume :=
      ha.congr_set_ae (Ioo_ae_eq_Ioc).symm
    rw [← integral_Ioc_eq_integral_Ioo]
    apply setIntegral_mono_on hintAbsIoc habsIoc measurableSet_Ioc
    intro x hx
    have hx1 : (1:ℝ) ≤ x := by have := hx.1; linarith
    have hle1 : x ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    calc |E₂Λ x| * x ^ (-s) ≤ |E₂Λ x| * 1 := by gcongr
      _ = |E₂Λ x| := mul_one _
  -- Piece 2: on `(X,∞)`, `|E₂Λ| ≤ ε/2`, and `∫_{(X,∞)} x^(-s) = X^(1-s)/(s-1)`.
  have hp2 : ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s) ≤ (ε / 2) * (X ^ (1 - s) / (s - 1)) := by
    have hrpow_int : IntegrableOn (fun x : ℝ => x ^ (-s)) (Set.Ioi X) volume :=
      integrableOn_Ioi_rpow_of_lt (by linarith) (by linarith : (0:ℝ) < X)
    have hval : ∫ x in Set.Ioi X, x ^ (-s) = X ^ (1 - s) / (s - 1) := by
      rw [integral_Ioi_rpow_of_lt (by linarith) (by linarith : (0:ℝ) < X),
        show -s + 1 = 1 - s by ring, show (1:ℝ) - s = -(s - 1) by ring]
      rw [div_neg, neg_div, neg_neg]
    rw [← hval, ← integral_const_mul]
    apply setIntegral_mono_on hintAbsIoiX (hrpow_int.const_mul (ε / 2)) measurableSet_Ioi
    intro x hx
    have hxpos : (0:ℝ) < x := by simp only [Set.mem_Ioi] at hx; linarith
    have hnn : 0 ≤ x ^ (-s) := Real.rpow_nonneg hxpos.le _
    have hb : |E₂Λ x| ≤ ε / 2 := hXge x (by simp only [Set.mem_Ioi] at hx; linarith)
    gcongr
  have hXpow : X ^ (1 - s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  -- Assemble: `(s-1)·∫|E₂Λ|·x^(-s) ≤ (s-1)·B + ε/2`.
  have hbound : (s - 1) * ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) ≤ (s - 1) * B + ε / 2 := by
    rw [hsplit, mul_add]
    have ht2 : (s - 1) * ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s) ≤ ε / 2 := by
      calc (s - 1) * ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s)
          ≤ (s - 1) * ((ε / 2) * (X ^ (1 - s) / (s - 1))) :=
            mul_le_mul_of_nonneg_left hp2 hsm1.le
        _ = (ε / 2) * X ^ (1 - s) := by
              have hne : s - 1 ≠ 0 := by linarith
              field_simp
        _ ≤ (ε / 2) * 1 := by gcongr
        _ = ε / 2 := mul_one _
    have ht1 : (s - 1) * ∫ x in Set.Ioc 1 X, |E₂Λ x| * x ^ (-s) ≤ (s - 1) * B :=
      mul_le_mul_of_nonneg_left hp1 hsm1.le
    linarith
  -- `|(s-1)·∫ E₂Λ·x^(-s)| ≤ (s-1)·∫|E₂Λ|·x^(-s)`.
  have habs_le : |(s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s)|
      ≤ (s - 1) * ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) := by
    rw [abs_mul, abs_of_pos hsm1]
    gcongr
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    simp only [Set.mem_Ioi] at hx
    change ‖E₂Λ x * x ^ (-s)‖ = |E₂Λ x| * x ^ (-s)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  rw [Real.dist_eq, sub_zero]
  -- `(s-1)·B + ε/2 < ε` since `s - 1 < ε/2/(B+1)`.
  have hfin : (s - 1) * B + ε / 2 < ε := by
    have hlt : s - 1 < ε / 2 / (B + 1) := lt_of_lt_of_le hs1 (min_le_right _ _)
    have hBp : 0 < B + 1 := by linarith
    have h1 : (s - 1) * B ≤ (s - 1) * (B + 1) := by nlinarith
    have h2 : (s - 1) * (B + 1) < (ε / 2 / (B + 1)) * (B + 1) := mul_lt_mul_of_pos_right hlt hBp
    have h3 : (ε / 2 / (B + 1)) * (B + 1) = ε / 2 := by field_simp
    linarith
  calc |(s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s)|
      ≤ (s - 1) * ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) := habs_le
    _ ≤ (s - 1) * B + ε / 2 := hbound
    _ < ε := hfin

end


theorem deriv_gamma_add_γ_eq_zero : deriv Gamma 1 + γ = 0 := by
  -- For `s > 1`, `log_zeta_eq` rearranges to a constant identity.
  have key : ∀ s : ℝ, 1 < s →
      (Real.log (riemannZeta (s:ℂ)).re + Real.log (s - 1))
        - (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s) = deriv Gamma 1 + γ := by
    intro s hs
    have h := log_zeta_eq s hs
    linarith
  -- The LHS is eventually constant, so its limit is that constant.
  have hconst : Filter.Tendsto
      (fun s : ℝ => (Real.log (riemannZeta (s:ℂ)).re + Real.log (s - 1))
        - (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (deriv Gamma 1 + γ)) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (key s hs).symm
  -- But the same function tends to `0 - 0` by the two limit lemmas.
  have hlim := log_zeta_limit.sub sub_one_mul_integral_E₂Λ_tendsto
  rw [sub_zero] at hlim
  exact tendsto_nhds_unique hconst hlim

theorem γ.eq_eulerMascheroni : γ = eulerMascheroniConstant := by
  linarith [Real.eulerMascheroniConstant_eq_neg_deriv, deriv_gamma_add_γ_eq_zero]

theorem sum_mangoldt_div_log_eq (x : ℝ) : ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) = log (log x) + eulerMascheroniConstant + E₂Λ x := by
    grind [γ.eq_eulerMascheroni]


theorem sum_mangoldt_div_log_eq_log_log : ∃ C, ∀ x, 2 ≤ x →
    |∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x)| ≤ C := by
    use (log 4 + 6)/log 2 + |eulerMascheroniConstant|
    intro x hx
    rw [sum_mangoldt_div_log_eq]
    calc
      _ = |E₂Λ x + eulerMascheroniConstant| := by ring_nf
      _ ≤ (log 4 + 6)/log x + |eulerMascheroniConstant| := by grw [abs_add_le, E₂Λ.abs_le hx]
      _ ≤ _ := by gcongr


theorem sum_mangoldt_div_log_eq_log_log' : (fun x ↦ ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x)) =O[atTop] (fun _ ↦ (1:ℝ)) := by
    simp only [isBigO_iff, norm_eq_abs, one_mem, CStarRing.norm_of_mem_unitary, mul_one,
      eventually_atTop]
    obtain ⟨ C, _ ⟩ := sum_mangoldt_div_log_eq_log_log
    use C, 2


theorem sum_mangoldt_div_log_eq_log_log'' : (fun x ↦ ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d)) ~[atTop] (fun x ↦ log (log x)) := by
    apply IsLittleO.isEquivalent (IsBigO.trans_isLittleO _ one_eq_o_log_log)
    convert! sum_mangoldt_div_log_eq_log_log' using 1


noncomputable def M : ℝ := (∫ t in Set.Ioi 2, E₁p t / (t * log t^2)) + 1 - log (log 2)


theorem M.le : M ≤ (log 4 + 4) / log 2 + 1 - log (log 2) := calc
    _ ≤ (∫ t in Set.Ioi 2, (log 4 + 4) / (t * log t^2)) + 1 - log (log 2) := by
      unfold M; gcongr with x hx
      · exact integrable_E₁p_div_mul_log_sq (by norm_num)
      · exact integrable_const_div_mul_log_sq _ (by norm_num)
      · measurability
      · simp at hx; positivity
      simp at hx; exact E₁p.le (by linarith)
    _ = _ := by rw [integ_div_mul_log_sq _ (by norm_num)]


theorem M.ge : M ≥ (-2 - E₁) / log 2 + 1 - log (log 2) := calc
    _ ≥ (∫ t in Set.Ioi 2, (-2 - E₁) / (t * log t^2)) + 1 - log (log 2) := by
      unfold M; gcongr with x hx
      · exact integrable_const_div_mul_log_sq _ (by norm_num)
      · exact integrable_E₁p_div_mul_log_sq (by norm_num)
      · measurability
      · simp at hx; positivity
      simp at hx; exact E₁p.ge (by linarith)
    _ = _ := by rw [integ_div_mul_log_sq _ (by norm_num)]


noncomputable abbrev E₂p (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1:ℝ) / p - log (log x) - M

theorem sum_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1:ℝ) / p = log (log x) + M + E₂p x := by
    ring


theorem E₂p.eq {x : ℝ} (hx : 2 ≤ x) :
    E₂p x = E₁p x / log x - ∫ t in Set.Ioi x, E₁p t / (t * log t^2) := by
  unfold E₂p
  rw [sum_filter, ← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp [Nat.not_prime_one])]
  have (n : ℕ) : (if Nat.Prime n then (1 : ℝ) / n else 0) = (if Nat.Prime n then log n / n else 0) / log n := by
    split_ifs with h
    · have : log n ≠ 0 := by simp; grind [h.two_le]
      field
    · simp
  simp_rw [this]
  rw [sum_div_log_eq hx, sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter]
  rw [sum_log_prime_div_eq]
  have : ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊t⌋₊, if Nat.Prime n then log ↑n / ↑n else 0) / (t * log t ^ 2) = ∫ t in 2..x, (1 / (t * log t) + E₁p t / (t * log t ^2)) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter, sum_log_prime_div_eq]
    field
  rw [this, intervalIntegral.integral_add]
  · rw [integral_one_div_mul_log hx, add_div, div_self (by simp; grind)]
    unfold M
    calc
    _ = E₁p x / log x + (∫ (x : ℝ) in 2..x, E₁p x / (x * log x ^ 2)) -
      ((∫ (t : ℝ) in Set.Ioi 2, E₁p t / (t * log t ^ 2))) := by ring
    _ = _ := by
      rw [← intervalIntegral.integral_interval_add_Ioi (integrable_E₁p_div_mul_log_sq (by rfl)) (integrable_E₁p_div_mul_log_sq hx)]
      ring
  · exact intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact integrable_E₁p_div_mul_log_sq (x := 2) (by rfl)|>.mono (by grind) (by rfl)


theorem E₂p.abs_le {x : ℝ} (hx : 2 ≤ x) :
    |E₂p x| ≤ (log 4 + 6 + E₁) / log x := by
    have : 0 < log x := by apply log_pos; linarith
    rw [E₂p.eq hx, abs_le']
    constructor
    · grw [E₁p.le (by linarith)]
      have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≥ (- 2 - E₁) / log x := calc
        _ ≥ ∫ t in Set.Ioi x, (-2 - E₁) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_const_div_mul_log_sq (-2 - E₁) hx)
            (integrable_E₁p_div_mul_log_sq hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁p.ge (by linarith)
        _ = _ := integ_div_mul_log_sq (-2 - E₁) hx
      grw [this]
      grind
    grw [E₁p.ge (by linarith)]
    have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≤ (log 4 + 4) / log x := calc
        _ ≤ ∫ t in Set.Ioi x, (log 4 + 4) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_E₁p_div_mul_log_sq hx)
            (integrable_const_div_mul_log_sq (log 4 + 4) hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁p.le (by linarith)
        _ = _ := integ_div_mul_log_sq (log 4 + 4) hx
    grw [this]
    grind


theorem E₂p.bound : E₂p =O[atTop] (fun x ↦ 1 / log x) := by
    simp only [one_div, isBigO_iff, norm_eq_abs, norm_inv, eventually_atTop]
    use log 4 + 6 + E₁, 2
    intro x hx
    convert E₂p.abs_le hx using 1
    have : 0 < log x := by apply log_pos; linarith
    grind [abs_of_pos this]


theorem E₂p.bound' : E₂p =o[atTop] (fun _ ↦ (1:ℝ)) := E₂p.bound.trans_isLittleO inv_log_eq_o_one


theorem sum_prime_div_eq_log_log : ∃ C, ∀ x, 2 ≤ x →
    |∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1:ℝ) / p - log (log x)| ≤ C := by
    use |M| + (log 4 + 6 + E₁) / log 2
    intro x hx
    rw [sum_prime_div_eq]
    calc
      _ = |M + E₂p x| := by ring_nf
      _ ≤ |M| + (log 4 + 6 + E₁) / log x := by grw [abs_add_le, E₂p.abs_le hx]
      _ ≤ _ := by
        gcongr
        have : 0 < log 4 := by apply log_pos; norm_num
        linarith [E₁.nonneg]


theorem sum_prime_div_eq_log_log' : (fun x ↦ ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1:ℝ) / p - log (log x)) =O[atTop] (fun _ ↦ (1:ℝ)) := by
    simp only [isBigO_iff, norm_eq_abs, one_mem, CStarRing.norm_of_mem_unitary, mul_one,
      eventually_atTop]
    obtain ⟨ C, hC ⟩ := sum_prime_div_eq_log_log
    use C, 2


theorem sum_prime_div_eq_log_log'' : (fun x ↦ ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1:ℝ) / p) ~[atTop] (fun x ↦ log (log x)) := by
    apply IsLittleO.isEquivalent (IsBigO.trans_isLittleO _ one_eq_o_log_log)
    convert! sum_prime_div_eq_log_log' using 1

lemma HasSum_log_one_sub_one_div_prime {p : ℕ} (hp : p.Prime) :
    HasSum (fun n : ℕ ↦ (-1 : ℝ) / (( n + 1) * p ^ (n + 1))) (log (1 - 1 / p)) := by
  convert! Real.hasSum_pow_div_log_of_abs_lt_one (x := 1 / p) _|>.neg using 1
  · ext
    rw [div_pow, one_pow, div_div]
    ring
  · ring
  · simp only [one_div, abs_inv, Nat.abs_cast]
    exact inv_lt_one_of_one_lt₀ (mod_cast hp.one_lt)

lemma E₂Λ_sub_E₂p_tendsto :
    Tendsto (E₂Λ - E₂p) atTop (nhds 0) := by
  exact isLittleO_one_iff ℝ|>.mp <| E₂Λ.bound'.sub E₂p.bound'

/- Function used in the proof of `M.eq`, `Λ n / n * log n` restricted to not primes. -/
noncomputable abbrev M_eq_f (n : ℕ) :=
    if ¬n.Prime then Λ n /(n * log n) else 0

lemma E₂Λ_sub_E₂p_eq (x : ℝ) :
    E₂Λ x - E₂p x = ∑ n ∈ Ioc 0 ⌊x⌋₊, M_eq_f n - (γ - M) := by
  calc
  _ = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n * log n) - ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 : ℝ) / p - (γ - M) := by ring
  _ = _ := by
    rw [sum_filter, ← sum_sub_distrib]
    congr
    ext n
    split_ifs with hn
    · rw [vonMangoldt_apply_prime hn]
      have : log n ≠ 0 := by simp; grind [hn.two_le]
      field
    · ring

lemma M_eq_f.sum_tendsto :
    Tendsto (fun (x : ℝ) ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, M_eq_f n) atTop (nhds (γ - M)) := by
  apply tendsto_sub_nhds_zero_iff.mp
  convert E₂Λ_sub_E₂p_tendsto using 1
  ext
  rw [← E₂Λ_sub_E₂p_eq]
  simp

lemma M_eq_f.sum_tendsto' :
    Tendsto (fun (N : ℕ) ↦ ∑ n ∈ range N, M_eq_f n) atTop (nhds (γ - M)) := by
  have : Tendsto (fun (N : ℕ) ↦ (∑ n ∈ Ioc 0 ⌊(N : ℝ)⌋₊, M_eq_f n)) atTop (nhds (γ - M)) := M_eq_f.sum_tendsto.comp tendsto_natCast_atTop_atTop
  simp_rw [Nat.floor_natCast] at this
  apply (this.comp (tendsto_sub_atTop_nat 1)).congr'
  filter_upwards [eventually_ge_atTop 1] with N hn
  rw [Nat.range_eq_Icc_zero_sub_one, ← add_sum_Ioc_eq_sum_Icc] <;> grind

lemma M_eq_f.HasSum :
    HasSum M_eq_f (γ - M) := by
  refine hasSum_iff_tendsto_nat_of_nonneg (fun n ↦ ?_) _|>.mpr M_eq_f.sum_tendsto'
  unfold M_eq_f
  split_ifs with hn
  · rfl
  · exact div_nonneg vonMangoldt_nonneg (by positivity)

lemma M_eq_f.sum_primes :
    ∑' (p : Nat.Primes), M_eq_f p = 0 := by
  convert! tsum_zero with p
  grind

lemma tsum_primes_eq_tsum_ite (f : ℕ → ℝ) :
    ∑' (n : Nat.Primes), f n = ∑' (n : ℕ), if n.Prime then f n else 0 := by
  convert! _root_.tsum_subtype Nat.Prime f using 2
  ext
  simp [Set.indicator]
  congr

lemma tsum_M_eq_f_eq_tsum :
    -∑' (n : ℕ), M_eq_f n = ∑' p : ℕ, if p.Prime then log (1 - 1 / p) + 1 / p else 0 := by
  rw [tsum_eq_tsum_primes_add_tsum_primes_of_support_subset_prime_powers M_eq_f.HasSum.summable
    (fun n hn ↦ (by simp_all [vonMangoldt_ne_zero_iff])), M_eq_f.sum_primes, zero_add,
    tsum_primes_eq_tsum_ite (fun p ↦ ∑' (k : ℕ), M_eq_f (p ^ (k + 2))), ← tsum_neg]
  refine tsum_congr fun n ↦ ?_
  split_ifs with hn
  · rw [← HasSum_log_one_sub_one_div_prime hn|>.tsum_eq, HasSum_log_one_sub_one_div_prime hn|>.summable.tsum_eq_zero_add]
    simp only [ite_not, Nat.cast_pow, log_pow, Nat.cast_add, Nat.cast_ofNat, CharP.cast_eq_zero,
      zero_add, pow_one, one_mul, Nat.cast_one, one_div]
    trans -∑' (k : ℕ), (1 : ℝ) / ((k + 2) * n ^ (k + 2))
    · congr
      ext k
      have : ¬(Nat.Prime (n ^ (k + 2))) := by exact Nat.Prime.not_prime_pow (by grind)
      simp only [this, ↓reduceIte, one_div, mul_inv_rev]
      rw [vonMangoldt_apply_pow (by grind), vonMangoldt_apply_prime hn]
      have : log n ≠ 0 := by simp; grind [hn.two_le]
      field
    · rw [← tsum_neg]
      ring_nf
      congr
      ext
      ring_nf
  · ring


theorem M.eq : M = γ + ∑' p : ℕ, if p.Prime then log (1 - 1 / p) + 1 / p else 0 := by
  rw [← tsum_M_eq_f_eq_tsum, M_eq_f.HasSum.tsum_eq]
  ring


noncomputable def E₃ (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, log (1 - (1:ℝ) / p) + log (log x) + eulerMascheroniConstant


theorem prod_one_minus_div_prime_eq {x : ℝ} (hx : 1 < x) :
    ∏ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 - (1 : ℝ) / p) =
      exp (-eulerMascheroniConstant) * exp (E₃ x) / log x := by
  have hlog : 0 < log x := log_pos hx
  have hpos : ∀ {p : ℕ}, p.Prime → (0 : ℝ) < 1 - 1 / p := fun {p} hp ↦ by
    have : (2 : ℝ) ≤ p := mod_cast hp.two_le
    grind [one_div_le_one_div_of_le two_pos this]
  rw [E₃, exp_add, exp_add, exp_sum, exp_log hlog, exp_neg,
    prod_congr rfl fun p hp ↦ exp_log (hpos (mem_filter.mp hp).2)]
  field_simp

noncomputable abbrev M_eq_summand (p : ℕ) := if p.Prime then log (1 - 1 / p) + 1 / p else 0

lemma M_eq_summand_bound (n : ℕ) :
    |M_eq_summand n| ≤ 2 / n ^ 2 := by
  unfold M_eq_summand
  split_ifs with h
  · trans 1 / n ^ 2 / (1 - 1 / n)
    · convert abs_log_sub_add_sum_range_le (x := 1 / n) _ 1 using 1
      · rw [add_comm]
        simp
      · rw [abs_of_nonneg (by simp)]
        ring
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast h.one_lt)
    rw [(by ring : (2 : ℝ) / n ^ 2 = 1 / n ^ 2 / (1 / 2))]
    gcongr
    suffices (1 : ℝ) / n ≤ 1 / 2 by linarith
    gcongr
    exact_mod_cast h.two_le
  · rw [abs_zero]
    positivity

lemma M_eq_summable : Summable M_eq_summand := by
  apply Summable.of_abs
  exact Summable.of_nonneg_of_le (by simp) M_eq_summand_bound (Summable.const_div (by simp) _)

lemma tsum_M_eq_summand_eq :
    ∑' (n : ℕ), M_eq_summand n = M - γ := by
  rw [M.eq]
  grind

lemma sum_one_div_sq_le {N : ℝ} (hN : 1 ≤ N) :
    ∑' (n : ℕ), (1 : ℝ) / (n + N) ^ 2 ≤ 2 / N := by
  grw [AntitoneOn.tsum_le_integral (f := (fun t ↦ 1 / (t + N) ^ 2))]
  · have hd : ∀ x ∈ Set.Ici 0, HasDerivAt (fun t ↦ -1 / (t + N)) (1 / (x + N) ^ 2) x := by
      intro t ht
      convert! HasDerivAt.fun_div (d' := (1 : ℝ)) (hasDerivAt_const ..) _ _ using 1
      · ring
      · simpa using hasDerivAt_id' t
      · simp at ht
        linarith
    have lim : Tendsto (fun t ↦ -1 / (t + N)) atTop (nhds 0) := by
      exact (tendsto_atTop_add_const_right atTop N tendsto_id).const_div_atTop _
    rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' hd (fun _ _ ↦ (by positivity)) lim]
    ring_nf
    rw [mul_two]
    gcongr
    field_simp
    exact hN
  · unfold AntitoneOn
    intro a ha b hb h
    beta_reduce
    simp at ha hb
    gcongr
  · convert! integrableOn_add_rpow_Ioi_of_lt (by norm_num : (-2 : ℝ) < -1) (by linarith : -N < 0) using 2
    simp
  · exact fun _ _ ↦ (by positivity)

lemma sum_M_eq_summand_le {N : ℕ} (hN : 0 < N) :
    |∑ n ∈ range N, M_eq_summand n - (M - γ)| ≤ 4 / N := by
  rw [← tsum_M_eq_summand_eq, ← M_eq_summable.sum_add_tsum_nat_add N]
  simp only [sub_add_cancel_left, abs_neg]
  rw [← norm_eq_abs]
  have summable := summable_nat_add_iff N|>.mpr M_eq_summable.norm
  apply norm_tsum_le_tsum_norm summable|>.trans
  apply Summable.tsum_le_tsum (fun _ ↦ M_eq_summand_bound _) summable _|>.trans
  · conv => lhs; arg 1; ext; rw [← mul_one_div]
    rw [tsum_mul_left]
    push_cast
    grw [sum_one_div_sq_le (mod_cast hN)]
    ring_nf
    rfl
  · exact (summable_nat_add_iff N|>.mpr (summable_one_div_nat_pow.mpr one_lt_two))|>.const_div _

lemma sum_M_eq_summand_le' {x : ℝ} (hx : 2 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, M_eq_summand n - (M - γ)| ≤ 4 / x := by
  have := sum_M_eq_summand_le (by grind : 0 < ⌊x⌋₊ + 1)
  rw [Nat.range_eq_Icc_zero_sub_one _ (by grind), ← add_sum_Ioc_eq_sum_Icc (by grind),
    (by simp : M_eq_summand 0 = 0), zero_add] at this
  simp only [add_tsub_cancel_right, Nat.cast_add, Nat.cast_one] at this
  grw [this]
  gcongr
  exact Nat.lt_floor_add_one _|>.le


theorem E₃.abs_le : ∃ C, ∀ x, 2 ≤ x → |E₃ x| ≤ C / log x := by
  unfold E₃
  refine ⟨4 + (log 4 + 6 + E₁), fun x hx ↦ ?_⟩
  calc
  _ = |(∑ n ∈ Ioc 0 ⌊x⌋₊, M_eq_summand n - (M - γ)) - E₂p x| := by
    unfold E₂p
    have (n : ℕ) : M_eq_summand n = (if n.Prime then log (1 - 1 / n) else 0) + (if n.Prime then (1 : ℝ) / n else 0) := by
      unfold M_eq_summand
      split_ifs
      · rfl
      · ring
    simp_rw [this]
    rw [sum_filter, sum_filter, sum_add_distrib, γ.eq_eulerMascheroni]
    ring_nf
  _ ≤ _ := by
    grw [abs_sub, E₂p.abs_le hx, sum_M_eq_summand_le' hx]
    have : 4 / x ≤ 4 / log x := by
      gcongr
      · exact log_pos (by linarith)
      · exact log_le_self (by linarith)
    grw [this]
    rw [← add_div]


theorem E₃.bound : E₃ =O[atTop] (fun x ↦ 1 / log x) := by
    simp only [isBigO_iff, norm_eq_abs, eventually_atTop]
    obtain ⟨ C, hC ⟩ := E₃.abs_le
    use C, 2
    convert hC using 3 with x hx
    have : 0 < log x := by apply log_pos; linarith
    have : 0 < 1 / log x := by positivity
    grind [abs_of_pos this]


theorem E₃.bound' : E₃ =o[atTop] (fun _ ↦ (1:ℝ)) := E₃.bound.trans_isLittleO inv_log_eq_o_one


theorem E₃.bound'' : (fun x ↦ ∏ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1 - (1:ℝ) / p)) ~[atTop] (fun x ↦ exp (-eulerMascheroniConstant) / log x) := by
   rw [isEquivalent_iff_tendsto_one]
   · convert Tendsto.congr' ?_ (Tendsto.rexp ((isLittleO_one_iff ℝ).mp E₃.bound')) using 2 with x
     · simp
     simp only [EventuallyEq.iff_eventually, Pi.div_apply, eventually_atTop]; use 2; intro x hx
     rw [prod_one_minus_div_prime_eq (by linarith)]
     have : 0 < log x := by apply log_pos; linarith
     field_simp
   simp only [ne_eq, div_eq_zero_iff, exp_ne_zero, log_eq_zero, eventually_atTop]; use 2
   grind


theorem E₃.bound''' : (fun x ↦ ∏ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1 - (1:ℝ) / p) - exp (-eulerMascheroniConstant) / log x) =O[atTop] (fun x ↦ 1 / (log x)^2) := by
  obtain ⟨c, hc⟩ := E₃.abs_le
  rw [isBigO_iff]
  refine ⟨exp (-eulerMascheroniConstant) * 2 * c, ?_⟩
  filter_upwards [eventually_ge_atTop 2, eventually_ge_atTop c.exp] with x hx hx2
  rw [prod_one_minus_div_prime_eq (by linarith)]
  specialize hc x hx
  rw [norm_eq_abs, norm_eq_abs]
  calc
  _ = |exp (-eulerMascheroniConstant) / log x * (exp (E₃ x) - 1)| := by ring_nf
  _ = |exp (-eulerMascheroniConstant) / log x| * |exp (E₃ x) - 1| := by rw [abs_mul]
  _ ≤ _ := by
    have : |E₃ x| ≤ 1 := by
      apply hc.trans
      have := log_le_log (exp_pos _) hx2
      rw [log_exp] at this
      apply div_le_one_iff.mpr <| Or.inl ⟨log_pos (by linarith), this⟩
    grw [abs_exp_sub_one_le this, hc]
    apply le_of_eq
    rw [abs_div, abs_div, abs_one, abs_of_nonneg (exp_nonneg _), abs_of_nonneg (log_nonneg (by linarith)), abs_of_nonneg (sq_nonneg _)]
    ring

end Mertens
end

/- BEGIN SOURCE: Erdos12/MertensBounds.lean -/
section
/-
# Mertens bounds in the forms used by the prefix argument

The analytic input is the attributed PrimeNumberTheoremAnd proof, supplied
through the pinned and locally checked source in `ChenTheorem/Analysis/PNT`.
-/

namespace Erdos12Proof

noncomputable def primeReciprocalSum (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime, (1 / p : ℝ)

noncomputable def primeLogReciprocalSum (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime, Real.log p / p

theorem prime_reciprocal_error_bound :
    ∃ C > (0 : ℝ), ∀ x : ℝ, 2 ≤ x →
      |primeReciprocalSum x - Real.log (Real.log x)| ≤ C := by
  obtain ⟨c, hc⟩ := Mertens.sum_prime_div_eq_log_log
  refine ⟨max 1 c, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro x hx
  exact (hc x hx).trans (le_max_right _ _)

theorem prime_reciprocal_window_bound :
    ∃ C > (0 : ℝ), ∀ x y : ℝ, 2 ≤ x → 2 ≤ y →
      primeReciprocalSum y - primeReciprocalSum x ≤
        C + Real.log (Real.log y) - Real.log (Real.log x) := by
  obtain ⟨c, hc0, hc⟩ := prime_reciprocal_error_bound
  refine ⟨2 * c, mul_pos (by norm_num) hc0, ?_⟩
  intro x y hx hy
  have hx' := (abs_le.mp (hc x hx)).1
  have hy' := (abs_le.mp (hc y hy)).2
  linarith

theorem prime_log_reciprocal_bound :
    ∃ C > (0 : ℝ), ∀ x : ℝ, 2 ≤ x → primeLogReciprocalSum x ≤ C * Real.log x := by
  obtain ⟨c, hc0, hc⟩ := Mertens.E₁p.bounded
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨1 + c / Real.log 2, by positivity, ?_⟩
  intro x hx
  have hlog : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have herror := (abs_le.mp (hc x (by linarith))).2
  have hexact := Mertens.sum_log_prime_div_eq x
  have hlinear : c ≤ c / Real.log 2 * Real.log x := by
    calc
      c = c / Real.log 2 * Real.log 2 := by field_simp
      _ ≤ c / Real.log 2 * Real.log x :=
        mul_le_mul_of_nonneg_left hlog (div_nonneg hc0.le hl2.le)
  change (∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime, Real.log p / p) ≤ _
  linarith

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/EulerProductBounds.lean -/
section
/- # Uniform two-sided Mertens product bounds for the sieve and prefix weights -/

namespace Erdos12Proof

noncomputable def primeEulerProduct (x : ℝ) : ℝ :=
  ∏ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime, (1 - (1 : ℝ) / p)

theorem primeEulerProduct_pos (x : ℝ) : 0 < primeEulerProduct x := by
  apply Finset.prod_pos
  intro p hp
  have hp' := (Finset.mem_filter.mp hp).2
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp'.one_lt
  exact sub_pos.mpr ((div_lt_one (lt_trans zero_lt_one hp1)).mpr hp1)

theorem primeEulerProduct_comparable :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ x : ℝ, 2 ≤ x →
      c / Real.log x ≤ primeEulerProduct x ∧ primeEulerProduct x ≤ C / Real.log x := by
  obtain ⟨d, hd⟩ := Mertens.E₃.abs_le
  let D : ℝ := |d| / Real.log 2
  let a : ℝ := Real.exp (-Real.eulerMascheroniConstant)
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨a * Real.exp (-D), mul_pos (Real.exp_pos _) (Real.exp_pos _),
    a * Real.exp D, mul_pos (Real.exp_pos _) (Real.exp_pos _), ?_⟩
  intro x hx
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hll : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have herror : |Mertens.E₃ x| ≤ D := by
    calc
      |Mertens.E₃ x| ≤ d / Real.log x := hd x hx
      _ ≤ |d| / Real.log x := (div_le_div_iff_of_pos_right hlx).mpr (le_abs_self d)
      _ ≤ |d| / Real.log 2 := div_le_div_of_nonneg_left (abs_nonneg d) hl2 hll
  have hlower := Real.exp_le_exp.mpr (abs_le.mp herror).1
  have hupper := Real.exp_le_exp.mpr (abs_le.mp herror).2
  have hprod : primeEulerProduct x = a * Real.exp (Mertens.E₃ x) / Real.log x := by
    exact Mertens.prod_one_minus_div_prime_eq (by linarith)
  rw [hprod]
  constructor
  · exact (div_le_div_iff_of_pos_right hlx).mpr
      (mul_le_mul_of_nonneg_left hlower (Real.exp_nonneg _))
  · exact (div_le_div_iff_of_pos_right hlx).mpr
      (mul_le_mul_of_nonneg_left hupper (Real.exp_nonneg _))

theorem inverse_primeEulerProduct_bound :
    ∃ C > (0 : ℝ), ∀ x : ℝ, 2 ≤ x → (primeEulerProduct x)⁻¹ ≤ C * Real.log x := by
  obtain ⟨c, hc, _, _, hbound⟩ := primeEulerProduct_comparable
  refine ⟨1 / c, one_div_pos.mpr hc, ?_⟩
  intro x hx
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have h := one_div_le_one_div_of_le (div_pos hc hlx) (hbound x hx).1
  calc
    (primeEulerProduct x)⁻¹ = 1 / primeEulerProduct x := (one_div _).symm
    _ ≤ 1 / (c / Real.log x) := h
    _ = (1 / c) * Real.log x := by field_simp

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/SmallPrimeRemoval.lean -/
section
/- # The logarithmic cost of removing the small primes -/

namespace Erdos12Proof

theorem one_add_sieveLocalWeight {p : ℕ} (hp : 1 < p) :
    1 + sieveLocalWeight p = (1 - (1 : ℝ) / p)⁻¹ := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp
    linarith
  unfold sieveLocalWeight
  field_simp
  ring

theorem small_prime_euler_product_bound {ι : Type*} [DecidableEq ι]
    (m : ι → ℕ) (R : Finset ι) (hinj : Set.InjOn m R)
    (hprime : ∀ i ∈ R, (m i).Prime) (x : ℝ) (hsmall : ∀ i ∈ R, (m i : ℝ) ≤ x) :
    (∏ i ∈ R, (1 + sieveLocalWeight (m i))) ≤ (primeEulerProduct x)⁻¹ := by
  let P := (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime
  have hsub : R.image m ⊆ P := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨(hprime i hi).pos, Nat.le_floor (hsmall i hi)⟩, hprime i hi⟩
  calc
    _ = ∏ p ∈ R.image m, (1 + sieveLocalWeight p) := by
      rw [Finset.prod_image]
      exact hinj
    _ ≤ ∏ p ∈ P, (1 + sieveLocalWeight p) := by
      apply Finset.prod_le_prod_of_subset_of_one_le₀ hsub
      · intro p hp
        have hp1 := (Finset.mem_filter.mp (hsub hp)).2.one_lt
        exact add_nonneg zero_le_one (sieveLocalWeight_pos hp1).le
      · intro p hp _
        exact le_add_of_nonneg_right (sieveLocalWeight_pos (Finset.mem_filter.mp hp).2.one_lt).le
    _ = (primeEulerProduct x)⁻¹ := by
      unfold primeEulerProduct
      rw [← Finset.prod_inv_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      exact one_add_sieveLocalWeight (Finset.mem_filter.mp hp).2.one_lt

noncomputable def primeRemovalConstant : ℝ := Classical.choose inverse_primeEulerProduct_bound

theorem primeRemovalConstant_pos : 0 < primeRemovalConstant :=
  (Classical.choose_spec inverse_primeEulerProduct_bound).1

theorem primeRemovalConstant_bound {x : ℝ} (hx : 2 ≤ x) :
    (primeEulerProduct x)⁻¹ ≤ primeRemovalConstant * Real.log x :=
  (Classical.choose_spec inverse_primeEulerProduct_bound).2 x hx

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sieveMass_small_prime_removal (m : ι → ℕ) (hm : ∀ i, 1 < m i)
    (R : Finset ι) (hinj : Set.InjOn m R) (hprime : ∀ i ∈ R, (m i).Prime)
    (x z : ℝ) (hx : 2 ≤ x) (hz : 1 < z) (hsmall : ∀ i ∈ R, (m i : ℝ) ≤ x) :
    sieveMass m z ≤ primeRemovalConstant * Real.log x *
      sieveMass (fun i : {i // i ∉ R} => m i) z := by
  have hG := sieveMass_pos (m := fun i : {i // i ∉ R} => m i) (fun i => hm i) hz
  calc
    _ ≤ sieveMass (fun i : {i // i ∉ R} => m i) z *
        ∏ i ∈ R, (1 + sieveLocalWeight (m i)) := sieveMass_remove_bound m hm z R
    _ ≤ sieveMass (fun i : {i // i ∉ R} => m i) z * (primeEulerProduct x)⁻¹ :=
      mul_le_mul_of_nonneg_left (small_prime_euler_product_bound m R hinj hprime x hsmall) hG.le
    _ ≤ sieveMass (fun i : {i // i ∉ R} => m i) z * (primeRemovalConstant * Real.log x) :=
      mul_le_mul_of_nonneg_left (primeRemovalConstant_bound hx) hG.le
    _ = _ := by ring

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/PrimeBandEuler.lean -/
section
/- # Mertens products on a band of primes -/

namespace Erdos12Proof

noncomputable def primesThrough (x : ℝ) : Finset ℕ :=
  (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime

theorem mem_primesThrough {x : ℝ} (hx : 0 ≤ x) {p : ℕ} :
    p ∈ primesThrough x ↔ p.Prime ∧ (p : ℝ) ≤ x := by
  constructor
  · intro hp
    obtain ⟨hinterval, hprime⟩ := Finset.mem_filter.mp hp
    refine ⟨hprime, ?_⟩
    have hfloor : (p : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast (Finset.mem_Ioc.mp hinterval).2
    exact hfloor.trans (Nat.floor_le hx)
  · rintro ⟨hp, hpx⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hp.pos, Nat.le_floor hpx⟩, hp⟩

theorem primesThrough_mono {x y : ℝ} (hxy : x ≤ y) : primesThrough x ⊆ primesThrough y := by
  intro p hp
  obtain ⟨hinterval, hprime⟩ := Finset.mem_filter.mp hp
  obtain ⟨hp0, hpx⟩ := Finset.mem_Ioc.mp hinterval
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Ioc.mpr ⟨hp0, hpx.trans (Nat.floor_mono hxy)⟩, hprime⟩

noncomputable def primeBand (y x : ℝ) : Finset ℕ :=
  (primesThrough x).filter (fun p => y < (p : ℝ))

noncomputable def primeBandEulerProduct (y x : ℝ) : ℝ :=
  ∏ p ∈ primeBand y x, (1 + sieveLocalWeight p)

theorem primeBand_eq_sdiff {x y : ℝ} (hy : 0 ≤ y) :
    primeBand y x = primesThrough x \ primesThrough y := by
  ext p
  simp only [primeBand, Finset.mem_filter, Finset.mem_sdiff]
  constructor
  · rintro ⟨hpx, hpy⟩
    refine ⟨hpx, fun h => ?_⟩
    exact (not_le_of_gt hpy) ((mem_primesThrough hy).mp h).2
  · rintro ⟨hpx, hpy⟩
    refine ⟨hpx, ?_⟩
    by_contra hnot
    apply hpy
    exact (mem_primesThrough hy).mpr ⟨(Finset.mem_filter.mp hpx).2, le_of_not_gt hnot⟩

theorem primeBandEulerProduct_ratio {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) :
    primeBandEulerProduct y x = primeEulerProduct y / primeEulerProduct x := by
  let f : ℕ → ℝ := fun p => 1 - 1 / p
  have hsplit := Finset.prod_sdiff (f := f) (primesThrough_mono hyx)
  rw [← primeBand_eq_sdiff hy] at hsplit
  change (∏ p ∈ primeBand y x, f p) * primeEulerProduct y = primeEulerProduct x at hsplit
  have hband : (∏ p ∈ primeBand y x, f p) ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hsplit
    exact (primeEulerProduct_pos x).ne' hsplit.symm
  have hinverse : primeBandEulerProduct y x = (∏ p ∈ primeBand y x, f p)⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    exact one_add_sieveLocalWeight (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.one_lt
  rw [hinverse, ← hsplit]
  have hyzero : primeEulerProduct y ≠ 0 := (primeEulerProduct_pos y).ne'
  field_simp

theorem primeBandEulerProduct_lower_bound :
    ∃ c > (0 : ℝ), ∀ x y : ℝ, 2 ≤ y → y ≤ x →
      c * Real.log x / Real.log y ≤ primeBandEulerProduct y x := by
  obtain ⟨c, hc, C, hC, hbound⟩ := primeEulerProduct_comparable
  refine ⟨c / C, div_pos hc hC, ?_⟩
  intro x y hy hyx
  have hx : 2 ≤ x := hy.trans hyx
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  calc
    _ = (c / Real.log y) / (C / Real.log x) := by field_simp
    _ ≤ primeEulerProduct y / (C / Real.log x) :=
      div_le_div_of_nonneg_right (hbound y hy).1 (div_pos hC hlx).le
    _ ≤ primeEulerProduct y / primeEulerProduct x :=
      div_le_div_of_nonneg_left (primeEulerProduct_pos y).le (primeEulerProduct_pos x) (hbound x hx).2
    _ = primeBandEulerProduct y x := (primeBandEulerProduct_ratio (by linarith) hyx).symm

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/FinitePrimeSamples.lean -/
section
/- # A finite prime-coordinate model for prefix events -/

namespace Erdos12Proof

abbrev PrimeSample (N : ℕ) := primesThrough (N : ℝ) → Fin (N + 2)

noncomputable def primeSampleWeight (N : ℕ) (ω : PrimeSample N) : ℝ :=
  finiteGeometricProductWeight (fun p : primesThrough (N : ℝ) => (p.val : ℝ)) (N + 1) ω

theorem primeSampleWeight_nonneg (N : ℕ) (ω : PrimeSample N) : 0 ≤ primeSampleWeight N ω := by
  apply finiteGeometricProductWeight_nonneg
  intro p
  have hp := ((mem_primesThrough (Nat.cast_nonneg N)).mp p.property).1
  exact_mod_cast hp.one_lt

theorem primeSampleWeight_mass (N : ℕ) : (∑ ω : PrimeSample N, primeSampleWeight N ω) = 1 :=
  finiteGeometricProductWeight_mass _ _

def primePrefixCondition (N g : ℕ) (ω : PrimeSample N) : Prop :=
  ∀ p : primesThrough (N : ℝ),
    (p.val < g.maxPrimeFac → (ω p).val = g.factorization p.val) ∧
    (p.val = g.maxPrimeFac → g.factorization p.val ≤ (ω p).val)

noncomputable def primePrefixConditionDecidable (N g : ℕ) (ω : PrimeSample N) :
    Decidable (primePrefixCondition N g ω) := by
  unfold primePrefixCondition
  infer_instance

noncomputable def primePrefixProbability (N g : ℕ) : ℝ :=
  weightedSum (primeSampleWeight N) (fun ω => if primePrefixCondition N g ω then 1 else 0)

theorem primePrefixProbability_product (N g : ℕ) :
    primePrefixProbability N g = ∏ p : primesThrough (N : ℝ),
      ∑ x : Fin (N + 2),
        if (p.val < g.maxPrimeFac → x.val = g.factorization p.val) ∧
          (p.val = g.maxPrimeFac → g.factorization p.val ≤ x.val)
        then truncatedGeometricWeight (p.val : ℝ) (N + 1) x else 0 := by
  classical
  have h := productWeight_restricted_sum
    (fun p : primesThrough (N : ℝ) => truncatedGeometricWeight (p.val : ℝ) (N + 1))
    (fun p x => (p.val < g.maxPrimeFac → x.val = g.factorization p.val) ∧
      (p.val = g.maxPrimeFac → g.factorization p.val ≤ x.val))
  calc
    primePrefixProbability N g =
        ∑ ω : PrimeSample N, if primePrefixCondition N g ω then
          productWeight (fun p : primesThrough (N : ℝ) =>
            truncatedGeometricWeight (p.val : ℝ) (N + 1)) ω else 0 := by
      unfold primePrefixProbability weightedSum primeSampleWeight finiteGeometricProductWeight
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hC : primePrefixCondition N g ω <;> simp [hC]
    _ = _ := by
      convert h using 1
      apply Finset.sum_congr rfl
      intro ω _
      dsimp only [primePrefixCondition]
      exact (ite_eq_ite _ _ _).mpr trivial

theorem factorization_zero_above_maxPrimeFac {g p : ℕ} (hg : g ≠ 0) (hp : p.Prime)
    (hpg : g.maxPrimeFac < p) : g.factorization p = 0 := by
  apply Nat.factorization_eq_zero_of_not_dvd
  intro hdiv
  exact (not_le_of_gt hpg) (Nat.le_maxPrimeFac hg hp hdiv)

theorem primePrefix_local_probability (N g : ℕ) (hg : g ≠ 0) (hgN : g ≤ N)
    (p : primesThrough (N : ℝ)) :
    (∑ x : Fin (N + 2),
      if (p.val < g.maxPrimeFac → x.val = g.factorization p.val) ∧
        (p.val = g.maxPrimeFac → g.factorization p.val ≤ x.val)
      then truncatedGeometricWeight (p.val : ℝ) (N + 1) x else 0) =
        (1 / (p.val : ℝ)) ^ g.factorization p.val *
          (if p.val < g.maxPrimeFac then 1 - 1 / (p.val : ℝ) else 1) := by
  have hcap : g.factorization p.val < N + 1 :=
    (Nat.factorization_lt p.val hg).trans_le (by omega)
  have hp := ((mem_primesThrough (Nat.cast_nonneg N)).mp p.property).1
  by_cases hlt : p.val < g.maxPrimeFac
  · have hne : p.val ≠ g.maxPrimeFac := Nat.ne_of_lt hlt
    simp only [hlt, hne, true_implies, false_implies, and_true, ite_true]
    rw [truncatedGeometricWeight_atom (p.val : ℝ) (N + 1) _ hcap]
    unfold geometricWeight
    ring
  · by_cases heq : p.val = g.maxPrimeFac
    · simpa [heq] using truncatedGeometricWeight_tail (p.val : ℝ) (N + 1) _ hcap.le
    · have hgt : g.maxPrimeFac < p.val := by omega
      have hz := factorization_zero_above_maxPrimeFac hg hp hgt
      simp only [hlt, heq, false_implies, and_self, ite_true, ite_false, hz, pow_zero, mul_one]
      exact truncatedGeometricWeight_sum (p.val : ℝ) (N + 1)

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/PrefixProbability.lean -/
section
/- # The exact prefix probability in the finite product model -/

namespace Erdos12Proof

theorem prime_power_product_on_bound (N g : ℕ) (hg : g ≠ 0) (hgN : g ≤ N) :
    (∏ p ∈ primesThrough (N : ℝ), p ^ g.factorization p) = g := by
  classical
  have hsub : g.primeFactors ⊆ primesThrough (N : ℝ) := by
    intro p hp
    have h := Nat.mem_primeFactors.mp hp
    apply (mem_primesThrough (Nat.cast_nonneg N)).mpr
    exact ⟨h.1, by exact_mod_cast (Nat.le_of_dvd (Nat.pos_of_ne_zero hg) h.2.1).trans hgN⟩
  calc
    _ = ∏ p ∈ g.primeFactors, p ^ g.factorization p := by
      symm
      apply Finset.prod_subset hsub
      intro p _ hp
      have hzero : g.factorization p = 0 := by
        apply Finsupp.notMem_support_iff.mp
        simpa only [Nat.support_factorization] using hp
      simp only [hzero, pow_zero]
    _ = g := Nat.prod_factorization_pow_eq_self hg

theorem prime_reciprocal_power_product (N g : ℕ) (hg : g ≠ 0) (hgN : g ≤ N) :
    (∏ p : primesThrough (N : ℝ), (1 / (p.val : ℝ)) ^ g.factorization p.val) = 1 / (g : ℝ) := by
  classical
  rw [Finset.prod_coe_sort (primesThrough (N : ℝ))
    (fun p : ℕ => (1 / (p : ℝ)) ^ g.factorization p)]
  simp only [one_div_pow, Finset.prod_div_distrib, Finset.prod_const_one]
  congr 1
  exact_mod_cast prime_power_product_on_bound N g hg hgN

noncomputable def prefixEulerProduct (N r : ℕ) : ℝ :=
  ∏ p : primesThrough (N : ℝ), if p.val < r then 1 - 1 / (p.val : ℝ) else 1

theorem primePrefixProbability_exact (N g : ℕ) (hg : g ≠ 0) (hgN : g ≤ N) :
    primePrefixProbability N g = (1 / (g : ℝ)) * prefixEulerProduct N g.maxPrimeFac := by
  rw [primePrefixProbability_product]
  simp_rw [primePrefix_local_probability N g hg hgN]
  rw [Finset.prod_mul_distrib, prime_reciprocal_power_product N g hg hgN]
  rfl

theorem prefixEulerProduct_eq (N r : ℕ) : prefixEulerProduct N r =
    ∏ p ∈ (primesThrough (N : ℝ)).filter (fun p => p < r), (1 - 1 / (p : ℝ)) := by
  classical
  unfold prefixEulerProduct
  rw [Finset.prod_coe_sort (primesThrough (N : ℝ))
    (fun p : ℕ => if p < r then 1 - 1 / (p : ℝ) else 1)]
  exact (Finset.prod_filter (fun p => p < r) _).symm

theorem prefixEulerProduct_lower (N r : ℕ) :
    primeEulerProduct (r : ℝ) ≤ prefixEulerProduct N r := by
  classical
  let P := (primesThrough (N : ℝ)).filter (fun p => p < r)
  have hsub : P ⊆ primesThrough (r : ℝ) := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hprime := ((mem_primesThrough (Nat.cast_nonneg N)).mp hp'.1).1
    exact (mem_primesThrough (Nat.cast_nonneg r)).mpr ⟨hprime, by exact_mod_cast hp'.2.le⟩
  have hnonneg : ∀ p ∈ primesThrough (r : ℝ), 0 ≤ 1 - 1 / (p : ℝ) := by
    intro p hp
    have hp' := ((mem_primesThrough (Nat.cast_nonneg r)).mp hp).1
    have hpos : (1 : ℝ) < p := by exact_mod_cast hp'.one_lt
    exact sub_nonneg.mpr ((div_le_one (by linarith)).mpr hpos.le)
  have hle := Finset.prod_le_prod_of_subset_of_le_one₀ hsub hnonneg
    (fun p _ _ => sub_le_self _ (by positivity : (0 : ℝ) ≤ 1 / p))
  rw [prefixEulerProduct_eq]
  exact hle

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/PrefixWeightBound.lean -/
section
/- # A uniform lower bound for the expected weight of each prefix -/

namespace Erdos12Proof

theorem exists_prefix_weight_constant : ∃ c : ℝ, 0 < c ∧ ∀ N g : ℕ, 1 < g → g ≤ N →
    c / g ≤ primePrefixProbability N g * Real.log (2 * (g.maxPrimeFac : ℝ)) := by
  obtain ⟨c, hc, C, _, hEuler⟩ := primeEulerProduct_comparable
  refine ⟨c, hc, ?_⟩
  intro N g hg hgN
  have hp := Nat.prime_maxPrimeFac_of_one_lt hg
  have hr : (2 : ℝ) ≤ g.maxPrimeFac := by exact_mod_cast hp.two_le
  have hr0 : (0 : ℝ) < g.maxPrimeFac := by linarith
  have hlog : 0 < Real.log (g.maxPrimeFac : ℝ) := Real.log_pos (by linarith)
  have hlower := (hEuler (g.maxPrimeFac : ℝ) hr).1
  have hpref := prefixEulerProduct_lower N g.maxPrimeFac
  have hpref0 : 0 < prefixEulerProduct N g.maxPrimeFac :=
    (div_pos hc hlog).trans_le (hlower.trans hpref)
  have hcprod : c ≤ prefixEulerProduct N g.maxPrimeFac * Real.log (g.maxPrimeFac : ℝ) :=
    (div_le_iff₀ hlog).mp (hlower.trans hpref)
  have hlogGrow : Real.log (g.maxPrimeFac : ℝ) ≤ Real.log (2 * (g.maxPrimeFac : ℝ)) :=
    Real.log_le_log hr0 (by linarith)
  have hcprod' : c ≤ prefixEulerProduct N g.maxPrimeFac * Real.log (2 * (g.maxPrimeFac : ℝ)) :=
    hcprod.trans (mul_le_mul_of_nonneg_left hlogGrow hpref0.le)
  calc
    c / g = (1 / (g : ℝ)) * c := by ring
    _ ≤ (1 / (g : ℝ)) * (prefixEulerProduct N g.maxPrimeFac * Real.log (2 * (g.maxPrimeFac : ℝ))) :=
      mul_le_mul_of_nonneg_left hcprod' (by positivity)
    _ = _ := by rw [primePrefixProbability_exact N g (by omega) hgN]; ring

noncomputable def prefixWeightConstant : ℝ := Classical.choose exists_prefix_weight_constant

theorem prefixWeightConstant_pos : 0 < prefixWeightConstant :=
  (Classical.choose_spec exists_prefix_weight_constant).1

theorem prefix_weight_lower (N g : ℕ) (hg : 1 < g) (hgN : g ≤ N) :
    prefixWeightConstant / g ≤ primePrefixProbability N g * Real.log (2 * (g.maxPrimeFac : ℝ)) :=
  (Classical.choose_spec exists_prefix_weight_constant).2 N g hg hgN

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/PrimitiveReduction.lean -/
section
/- # The divisibility-minimal reduction of the manuscript's final section -/

namespace Erdos12Proof

def minimalCore (B : Finset ℕ) : Finset ℕ :=
  B.filter (fun a => ∀ b ∈ B, b ∣ a → b = a)

noncomputable def coreDivisor (B : Finset ℕ) (a : ℕ) : ℕ :=
  if h : ∃ b, b ∈ B ∧ b ∣ a then Nat.find h else 0

theorem minimalCore_subset (B : Finset ℕ) : minimalCore B ⊆ B :=
  Finset.filter_subset _ _

theorem minimalCore_primitive (B : Finset ℕ) : Primitive (minimalCore B : Set ℕ) := by
  intro a ha b hb hab
  exact (Finset.mem_filter.mp hb).2 a ((minimalCore_subset B) ha) hab

theorem coreDivisor_spec {B : Finset ℕ} (hpos : Positive (B : Set ℕ))
    {a : ℕ} (ha : a ∈ B) :
    coreDivisor B a ∈ minimalCore B ∧ coreDivisor B a ∣ a := by
  have hex : ∃ b, b ∈ B ∧ b ∣ a := ⟨a, ha, dvd_refl a⟩
  have hs := Nat.find_spec hex
  have hmin : ∀ b ∈ B, b ∣ Nat.find hex → b = Nat.find hex := by
    intro b hb hbc
    have hba := dvd_trans hbc hs.2
    have hcb : Nat.find hex ≤ b := Nat.find_min' hex ⟨hb, hba⟩
    have hbc' : b ≤ Nat.find hex := Nat.le_of_dvd (hpos hs.1) hbc
    exact Nat.le_antisymm hbc' hcb
  have hcore : Nat.find hex ∈ minimalCore B := Finset.mem_filter.mpr ⟨hs.1, hmin⟩
  simpa only [coreDivisor, dite_eq_left hex] using And.intro hcore hs.2

theorem coreDivisor_lt {B : Finset ℕ} (hpos : Positive (B : Set ℕ))
    {a : ℕ} (ha : a ∈ B \ minimalCore B) : coreDivisor B a < a := by
  obtain ⟨haB, haC⟩ := Finset.mem_sdiff.mp ha
  obtain ⟨hc, hca⟩ := coreDivisor_spec hpos haB
  have hle := Nat.le_of_dvd (hpos haB) hca
  have hne : coreDivisor B a ≠ a := by
    intro heq
    exact haC (heq ▸ hc)
  exact lt_of_le_of_ne hle hne

theorem coreDivisor_injOn {B : Finset ℕ} (hpos : Positive (B : Set ℕ))
    (hP : PropertyP (B : Set ℕ)) :
    Set.InjOn (coreDivisor B) (B \ minimalCore B : Finset ℕ) := by
  intro a ha b hb heq
  obtain ⟨haB, _⟩ := Finset.mem_sdiff.mp ha
  obtain ⟨hbB, _⟩ := Finset.mem_sdiff.mp hb
  obtain ⟨hc, hca⟩ := coreDivisor_spec hpos haB
  obtain ⟨_, hcb⟩ := coreDivisor_spec hpos hbB
  rw [← heq] at hcb
  have hcb_lt : coreDivisor B a < b := heq ▸ coreDivisor_lt hpos hb
  exact hP ((minimalCore_subset B) hc) haB hbB
    (dvd_add hca hcb) (coreDivisor_lt hpos ha) hcb_lt

theorem twice_le_of_dvd_of_lt {a b : ℕ} (_ha : 0 < a) (hab : a ∣ b) (hlt : a < b) :
    2 * a ≤ b := by
  obtain ⟨k, rfl⟩ := hab
  have hk : 2 ≤ k := by
    by_contra h
    have hk' : k ≤ 1 := by omega
    have := Nat.mul_le_mul_left a hk'
    omega
  nlinarith

theorem reciprocal_le_half_of_dvd_of_lt {a b : ℕ}
    (ha : 0 < a) (hab : a ∣ b) (hlt : a < b) :
    (1 / b : ℝ) ≤ (1 / 2 : ℝ) * (1 / a : ℝ) := by
  have hbound : (2 : ℝ) * a ≤ b := by
    exact_mod_cast twice_le_of_dvd_of_lt ha hab hlt
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  calc
    (1 / b : ℝ) ≤ 1 / (2 * (a : ℝ)) :=
      one_div_le_one_div_of_le (by positivity) hbound
    _ = (1 / 2 : ℝ) * (1 / a : ℝ) := by ring

theorem harmonic_sdiff_le_half_core {B : Finset ℕ} (hpos : Positive (B : Set ℕ))
    (hP : PropertyP (B : Set ℕ)) :
    harmonic (B \ minimalCore B) ≤ (1 / 2 : ℝ) * harmonic (minimalCore B) := by
  unfold harmonic
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum_of_injOn (coreDivisor B) (coreDivisor_injOn hpos hP)
  · intro c hc
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
    exact (coreDivisor_spec hpos (Finset.mem_sdiff.mp ha).1).1
  · intro a ha
    obtain ⟨hc, hca⟩ := coreDivisor_spec hpos (Finset.mem_sdiff.mp ha).1
    exact reciprocal_le_half_of_dvd_of_lt
      (hpos ((minimalCore_subset B) hc)) hca (coreDivisor_lt hpos ha)
  · intro a _ _
    positivity

theorem harmonic_le_three_halves_core {B : Finset ℕ}
    (hpos : Positive (B : Set ℕ)) (hP : PropertyP (B : Set ℕ)) :
    harmonic B ≤ (3 / 2 : ℝ) * harmonic (minimalCore B) := by
  have hsplit : harmonic (B \ minimalCore B) + harmonic (minimalCore B) = harmonic B := by
    exact Finset.sum_sdiff (minimalCore_subset B)
  have hbound := harmonic_sdiff_le_half_core hpos hP
  linarith

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/PrimeFibres.lean -/
section
/-
# Prime fibres and inherited opposite-residue restrictions

These are deterministic parts of the manuscript's prefix argument. The
probability space, adaptive schedule, and analytic bounds are separate work.
-/

namespace Erdos12Proof

def primeFibre (A : Set ℕ) (g : ℕ) : Set ℕ :=
  {p | p.Prime ∧ (∀ q : ℕ, q.Prime → q ∣ g → q ≤ p) ∧ g * p ∈ A}

theorem primeFibre_propertyP {A : Set ℕ} (hA : PropertyP A) {g : ℕ} (hg : 0 < g) :
    PropertyP (primeFibre A g) := by
  apply PropertyP.of_dilate hg
  apply hA.mono
  rintro n ⟨p, hp, rfl⟩
  exact hp.2.2

theorem primeFibre_odd {A : Set ℕ} (hodd : ∀ n ∈ A, Odd n) {g p : ℕ}
    (hp : p ∈ primeFibre A g) : Odd p := by
  exact (Nat.odd_mul.mp (hodd (g * p) hp.2.2)).2

theorem primeFibre_positive {A : Set ℕ} {g : ℕ} : Positive (primeFibre A g) := by
  intro p hp
  exact hp.1.pos

theorem inherited_opposite_restriction {A : Set ℕ} (hA : PropertyP A)
    {h g r p q : ℕ} (hh : 0 < h) (hhg : h ∣ g) (hg : 0 < g)
    (hrA : h * r ∈ A) (hpA : g * p ∈ A) (hqA : g * q ∈ A)
    (hrp : r < p) (hrq : r < q) (hsum : r ∣ p + q) : p = q := by
  have hle : h ≤ g := Nat.le_of_dvd hg hhg
  have hltp : h * r < g * p :=
    (Nat.mul_lt_mul_left hh).mpr hrp |>.trans_le (Nat.mul_le_mul_right p hle)
  have hltq : h * r < g * q :=
    (Nat.mul_lt_mul_left hh).mpr hrq |>.trans_le (Nat.mul_le_mul_right q hle)
  have hdiv : h * r ∣ g * p + g * q := by
    simpa only [← Nat.mul_add] using Nat.mul_dvd_mul hhg hsum
  exact Nat.eq_of_mul_eq_mul_left hg (hA hrA hpA hqA hdiv hltp hltq)

theorem nested_terminal_distinct {A : Set ℕ} (hA : Primitive A)
    {h g p : ℕ} (hp : 0 < p) (hhg : h ∣ g) (hne : h ≠ g)
    (hhp : h * p ∈ A) (hgp : g * p ∈ A) : False := by
  have heq : h * p = g * p := hA hhp hgp (Nat.mul_dvd_mul_right hhg p)
  exact hne (Nat.eq_of_mul_eq_mul_right hp heq)

theorem terminal_not_dvd_quotient {A : Set ℕ} (hA : Primitive A)
    {h k r p : ℕ} (hh : 0 < h) (hk : 0 < k) (hrp : r < p)
    (hrA : h * r ∈ A) (hkpA : h * k * p ∈ A) : ¬r ∣ k := by
  intro hrk
  have hdiv : h * r ∣ h * k * p := dvd_mul_of_dvd_left (Nat.mul_dvd_mul_left h hrk) p
  have heq := hA hrA hkpA hdiv
  have hlt : h * r < h * k * p := by
    have hle : h * p ≤ h * k * p := by
      have : h ≤ h * k := Nat.le_mul_of_pos_right h hk
      exact Nat.mul_le_mul_right p this
    exact ((Nat.mul_lt_mul_left hh).mpr hrp).trans_le hle
  exact (Nat.ne_of_lt hlt) heq

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/FibreDecomposition.lean -/
section
/- # Unique largest-prime decomposition and its nonnegative sum identity -/

open scoped ENNReal

namespace Erdos12Proof

theorem maxPrimeFac_eq_of_fibre {A : Set ℕ} {g p : ℕ} (hg : 0 < g)
    (hp : p ∈ primeFibre A g) : (g * p).maxPrimeFac = p := by
  have hmax : g.maxPrimeFac ≤ p := by
    by_cases hg1 : g = 1
    · simpa only [hg1, Nat.maxPrimeFac_one] using hp.1.one_lt.le
    · exact (Nat.maxPrimeFac_le_iff (by omega)).mpr hp.2.1
  rw [Nat.maxPrimeFac_mul (Nat.ne_of_gt hg) hp.1.ne_zero,
    hp.1.maxPrimeFac_eq_self, max_eq_right hmax]

theorem quotient_maxPrimeFac_mem {A : Set ℕ} {n : ℕ} (hnA : n ∈ A) (hn : 1 < n) :
    n.maxPrimeFac ∈ primeFibre A (n / n.maxPrimeFac) := by
  have hp := Nat.prime_maxPrimeFac_of_one_lt hn
  have hfactor : (n / n.maxPrimeFac) * n.maxPrimeFac = n :=
    Nat.div_mul_cancel Nat.maxPrimeFac_dvd
  refine ⟨hp, ?_, ?_⟩
  swap
  · rwa [hfactor]
  intro q hq hqg
  apply Nat.le_maxPrimeFac (by omega) hq
  exact dvd_trans hqg (Nat.div_dvd_of_dvd Nat.maxPrimeFac_dvd)

theorem quotient_maxPrimeFac_pos {n : ℕ} (hn : 1 < n) :
    0 < n / n.maxPrimeFac := by
  exact Nat.div_pos Nat.maxPrimeFac_le (Nat.prime_maxPrimeFac_of_one_lt hn).pos

theorem primeFibre_representation_unique {A : Set ℕ} {g h p q : ℕ}
    (hg : 0 < g) (hh : 0 < h) (hp : p ∈ primeFibre A g)
    (hq : q ∈ primeFibre A h) (heq : g * p = h * q) : g = h ∧ p = q := by
  have hpq : p = q := by
    rw [← maxPrimeFac_eq_of_fibre hg hp, heq, maxPrimeFac_eq_of_fibre hh hq]
  refine ⟨?_, hpq⟩
  rw [← hpq] at heq
  exact Nat.eq_of_mul_eq_mul_right hp.1.pos heq

theorem primeFibre_prefix_pos {A : Set ℕ} (hA : ∀ n ∈ A, 1 < n)
    {g p : ℕ} (hp : p ∈ primeFibre A g) : 0 < g := by
  have hn := hA (g * p) hp.2.2
  by_contra hg
  have hg0 : g = 0 := by omega
  simp [hg0] at hn

noncomputable def fibreEquiv (A : Set ℕ) (hA : ∀ n ∈ A, 1 < n) :
    (Σ g : ℕ, primeFibre A g) ≃ A :=
  Equiv.ofBijective (fun gp => ⟨gp.1 * gp.2, gp.2.property.2.2⟩) (by
    constructor
    · intro x y hxy
      have heq : x.1 * x.2.val = y.1 * y.2.val := congrArg Subtype.val hxy
      obtain ⟨hg, hp⟩ := primeFibre_representation_unique
        (primeFibre_prefix_pos hA x.2.property) (primeFibre_prefix_pos hA y.2.property)
        x.2.property y.2.property heq
      cases x with
      | mk g p =>
        cases y with
        | mk h q =>
          dsimp only at hg hp
          subst h
          have hpq : p = q := Subtype.ext hp
          subst q
          rfl
    · intro n
      refine ⟨⟨n.val / n.val.maxPrimeFac,
        ⟨n.val.maxPrimeFac, quotient_maxPrimeFac_mem n.property (hA n n.property)⟩⟩, ?_⟩
      apply Subtype.ext
      exact Nat.div_mul_cancel Nat.maxPrimeFac_dvd)

theorem fibreEquiv_apply (A : Set ℕ) (hA : ∀ n ∈ A, 1 < n)
    (gp : Σ g : ℕ, primeFibre A g) :
    (fibreEquiv A hA gp).val = gp.1 * gp.2.val := rfl

theorem reciprocal_fibre_decomposition {A : Set ℕ} (hA : ∀ n ∈ A, 1 < n) :
    (∑' n : A, (1 : ℝ≥0∞) / n.val) =
      ∑' g : ℕ, (1 : ℝ≥0∞) / g * ∑' p : primeFibre A g, (1 : ℝ≥0∞) / p.val := by
  rw [← (fibreEquiv A hA).tsum_eq (fun n : A => (1 : ℝ≥0∞) / n.val)]
  simp only [fibreEquiv_apply, Nat.cast_mul]
  rw [ENNReal.tsum_sigma']
  apply tsum_congr
  intro g
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro p
  simp only [div_eq_mul_inv, one_mul]
  exact ENNReal.mul_inv (Or.inr (by simp))
    (Or.inr (by exact_mod_cast p.property.1.ne_zero))

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/SelbergCRT.lean -/
section
/- # Identifying the product-coordinate sieve with one full integer period -/

namespace Erdos12Proof

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def sievePeriod (m : ι → ℕ) : ℕ := ∏ i, m i

omit [DecidableEq ι] in
theorem residueCube_surjective {m : ι → ℕ} (hm : ∀ i, 0 < m i)
    (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j)) :
    Function.Surjective (fun n : Fin (sievePeriod m) => residueCube m hm n.val) := by
  intro x
  have hpair : Set.Pairwise (↑(Finset.univ : Finset ι)) (fun i j => (m i).Coprime (m j)) := by
    intro i _ j _ hij
    exact hcop i j hij
  let k := Nat.chineseRemainderOfFinset (fun i => (x i).val) m Finset.univ
    (fun i _ => Nat.ne_of_gt (hm i)) hpair
  have hk : k.val < sievePeriod m :=
    Nat.chineseRemainderOfFinset_lt_prod _ _ _ _
  refine ⟨⟨k.val, hk⟩, ?_⟩
  funext i
  apply Fin.ext
  change k.val % m i = (x i).val
  have hi : k.val % m i = (x i).val % m i := k.property i (Finset.mem_univ i)
  exact hi.trans (Nat.mod_eq_of_lt (x i).isLt)

noncomputable def residueCubeEquiv {m : ι → ℕ} (hm : ∀ i, 0 < m i)
    (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j)) :
    Fin (sievePeriod m) ≃ SieveCube m :=
  Equiv.ofBijective (fun n => residueCube m hm n.val)
    ((Fintype.bijective_iff_surjective_and_card _).mpr
      ⟨residueCube_surjective hm hcop, by
        change Fintype.card (Fin (sievePeriod m)) = Fintype.card (∀ i, Fin (m i))
        rw [Fintype.card_fin, Fintype.card_pi]
        simp only [Fintype.card_fin, sievePeriod]⟩)

theorem finiteMean_equiv {K α β : Type*} [Field K] [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → K) : finiteMean (fun x => f (e x)) = finiteMean f := by
  unfold finiteMean
  rw [Fintype.card_congr e, Equiv.sum_comp]

theorem sieveMajorant_period_mean {m : ι → ℕ} (hm : ∀ i, 1 < m i)
    (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j)) {z : ℝ} (hz : 1 < z) :
    finiteMean (fun n : Fin (sievePeriod m) =>
      sieveMajorant m z (residueCube m (fun i => Nat.zero_lt_of_lt (hm i)) n.val)) =
      1 / sieveMass m z := by
  have h := finiteMean_equiv
    (residueCubeEquiv (fun i => Nat.zero_lt_of_lt (hm i)) hcop) (sieveMajorant m z)
  exact h.trans (sieveMajorant_mean hm hz)

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/SelbergCoefficientCounting.lean -/
section
/-
# Counting the pairs contributing to a Fourier coefficient

Outside the frequency support, the two indexing subsets must coincide.
Encoding their common outside part and their two inside parts bounds the
number of extensions by `4 ^ card R`. This slightly larger constant than the
manuscript's `3 ^ card R` gives the same later square-root denominator decay.
-/

namespace Erdos12Proof

variable {ι : Type*} [DecidableEq ι]

theorem coefficient_pair_sum_bound (F : Finset (Finset ι)) (R : Finset ι)
    (hdown : ∀ s ∈ F, ∀ t : Finset ι, t ⊆ s → t ∈ F)
    (w : Finset ι → ℝ) (hw : ∀ s ∈ F, 0 ≤ w s)
    (v : Finset ι → Finset ι → ℝ)
    (hzero : ∀ s ∈ F, ∀ t ∈ F, s \ R ≠ t \ R → v s t = 0)
    (hbound : ∀ s ∈ F, ∀ t ∈ F, s \ R = t \ R → v s t ≤ w (s \ R)) :
    (∑ s ∈ F, ∑ t ∈ F, v s t) ≤ (4 : ℝ) ^ R.card * ∑ c ∈ F, w c := by
  let D := (F ×ˢ F).filter (fun st => st.1 \ R = st.2 \ R)
  let T := F ×ˢ (R.powerset ×ˢ R.powerset)
  let code : Finset ι × Finset ι → Finset ι × (Finset ι × Finset ι) :=
    fun st => (st.1 \ R, (st.1 ∩ R, st.2 ∩ R))
  have hrestrict : (∑ s ∈ F, ∑ t ∈ F, v s t) = ∑ st ∈ D, v st.1 st.2 := by
    rw [← Finset.sum_product' F F v]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro st hst hnot
    obtain ⟨hs, ht⟩ := Finset.mem_product.mp hst
    apply hzero st.1 hs st.2 ht
    intro heq
    exact hnot (Finset.mem_filter.mpr ⟨hst, heq⟩)
  have hinj : Set.InjOn code D := by
    intro x hx y hy hxy
    have hxout := (Finset.mem_filter.mp hx).2
    have hyout := (Finset.mem_filter.mp hy).2
    have hout := congrArg Prod.fst hxy
    have hleft := congrArg (fun t => t.2.1) hxy
    have hright := congrArg (fun t => t.2.2) hxy
    dsimp only [code] at hout hleft hright
    apply Prod.ext
    · calc
        x.1 = x.1 \ R ∪ x.1 ∩ R := (Finset.sdiff_union_inter _ _).symm
        _ = y.1 \ R ∪ y.1 ∩ R := by rw [hout, hleft]
        _ = y.1 := Finset.sdiff_union_inter _ _
    · calc
        x.2 = x.2 \ R ∪ x.2 ∩ R := (Finset.sdiff_union_inter _ _).symm
        _ = y.2 \ R ∪ y.2 ∩ R := by rw [← hxout, ← hyout, hout, hright]
        _ = y.2 := Finset.sdiff_union_inter _ _
  have hcode : D.image code ⊆ T := by
    intro z hz
    obtain ⟨st, hst, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hs, _⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hst).1
    refine Finset.mem_product.mpr ⟨hdown st.1 hs _ Finset.sdiff_subset, ?_⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr (Finset.inter_subset_right),
      Finset.mem_powerset.mpr (Finset.inter_subset_right)⟩
  have hsum : (∑ st ∈ D, v st.1 st.2) ≤ ∑ z ∈ T, w z.1 := by
    apply Finset.sum_le_sum_of_injOn code hinj hcode
    · intro st hst
      obtain ⟨hs, ht⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hst).1
      exact hbound st.1 hs st.2 ht (Finset.mem_filter.mp hst).2
    · intro z hz _
      exact hw z.1 (Finset.mem_product.mp hz).1
  have hcard : ((R.powerset ×ˢ R.powerset).card : ℝ) = (4 : ℝ) ^ R.card := by
    simp only [Finset.card_product, Finset.card_powerset, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat, ← mul_pow]
    norm_num
  calc
    _ = ∑ st ∈ D, v st.1 st.2 := hrestrict
    _ ≤ ∑ z ∈ T, w z.1 := hsum
    _ = (4 : ℝ) ^ R.card * ∑ c ∈ F, w c := by
      dsimp only [T]
      rw [Finset.sum_product]
      simp only [Finset.sum_const, nsmul_eq_mul, hcard, ← Finset.mul_sum]

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/SelbergCoefficientBounds.lean -/
section
/- # Bounds for the tensor Fourier coefficients of the Selberg majorant -/

namespace Erdos12Proof

def localSieveCoefficient (w : ℝ) (a b r : Bool) : ℝ :=
  if r then
    if a then (if b then w * (1 - w) else -w) else (if b then -w else 0)
  else
    if a then (if b then w else 0) else (if b then 0 else 1)

theorem localSieveCoefficient_abs_le {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (a b r : Bool) :
    |localSieveCoefficient w a b r| ≤ if r then w else if a then w else 1 := by
  cases a <;> cases b <;> cases r <;>
    simp [localSieveCoefficient, abs_of_nonneg hw0,
      abs_of_nonneg (mul_nonneg hw0 (sub_nonneg.mpr hw1))]
  all_goals nlinarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def tensorSieveCoefficient (w : ι → ℝ) (R s t : Finset ι) : ℝ :=
  ∏ i, localSieveCoefficient (w i) (decide (i ∈ s)) (decide (i ∈ t)) (decide (i ∈ R))

theorem tensorSieveCoefficient_zero (w : ι → ℝ) (R s t : Finset ι)
    (hne : s \ R ≠ t \ R) : tensorSieveCoefficient w R s t = 0 := by
  have hnot : ¬∀ i, i ∈ s \ R ↔ i ∈ t \ R := by
    intro h
    exact hne (Finset.ext h)
  obtain ⟨i, hi⟩ := not_forall.mp hnot
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> by_cases hR : i ∈ R <;>
    simp_all [localSieveCoefficient]

theorem tensorSieveCoefficient_abs_le (w : ι → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1) (R s t : Finset ι) :
    |tensorSieveCoefficient w R s t| ≤ tensorWeight w R * tensorWeight w (s \ R) := by
  unfold tensorSieveCoefficient
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ i, if i ∈ R then w i else if i ∈ s then w i else 1 := by
      apply Finset.prod_le_prod₀ (fun i _ => abs_nonneg _)
      intro i _
      simpa only [decide_eq_true_eq] using
        localSieveCoefficient_abs_le (hw0 i) (hw1 i)
          (decide (i ∈ s)) (decide (i ∈ t)) (decide (i ∈ R))
    _ = (∏ i, if i ∈ R then w i else 1) * (∏ i, if i ∈ s \ R then w i else 1) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      by_cases hR : i ∈ R <;> by_cases hs : i ∈ s <;> simp [hR, hs]
    _ = tensorWeight w R * tensorWeight w (s \ R) := by
      simp only [Fintype.prod_ite_mem, tensorWeight]

theorem tensorSieveCoefficient_sum_bound (w : ι → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1)
    (F : Finset (Finset ι)) (hdown : ∀ s ∈ F, ∀ t : Finset ι, t ⊆ s → t ∈ F)
    (R : Finset ι) :
    (∑ s ∈ F, ∑ t ∈ F, |tensorSieveCoefficient w R s t|) ≤
      (4 : ℝ) ^ R.card * tensorWeight w R * selbergMass w F := by
  have h := coefficient_pair_sum_bound F R hdown
    (fun c => tensorWeight w R * tensorWeight w c)
    (fun c _ => mul_nonneg (Finset.prod_nonneg (fun i _ => hw0 i))
      (Finset.prod_nonneg (fun i _ => hw0 i)))
    (fun s t => |tensorSieveCoefficient w R s t|)
    (fun s _ t _ hne => by rw [tensorSieveCoefficient_zero w R s t hne, abs_zero])
    (fun s _ t _ _ => tensorSieveCoefficient_abs_le w hw0 hw1 R s t)
  simpa only [← Finset.mul_sum, selbergMass, mul_assoc] using h

noncomputable def normalizedSieveCoefficient (w : ι → ℝ)
    (F : Finset (Finset ι)) (R : Finset ι) : ℝ :=
  (∑ s ∈ F, ∑ t ∈ F, tensorSieveCoefficient w R s t) / selbergMass w F ^ 2

theorem normalizedSieveCoefficient_bound (w : ι → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1)
    (F : Finset (Finset ι)) (hF : ∅ ∈ F)
    (hdown : ∀ s ∈ F, ∀ t : Finset ι, t ⊆ s → t ∈ F) (R : Finset ι) :
    |normalizedSieveCoefficient w F R| ≤
      (4 : ℝ) ^ R.card * tensorWeight w R / selbergMass w F := by
  have hG := selbergMass_pos w hw0 F hF
  have habs : |∑ s ∈ F, ∑ t ∈ F, tensorSieveCoefficient w R s t| ≤
      ∑ s ∈ F, ∑ t ∈ F, |tensorSieveCoefficient w R s t| := by
    calc
      _ ≤ ∑ s ∈ F, |∑ t ∈ F, tensorSieveCoefficient w R s t| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := Finset.sum_le_sum (fun s _ => Finset.abs_sum_le_sum_abs _ _)
  unfold normalizedSieveCoefficient
  rw [abs_div, abs_of_pos (sq_pos_of_pos hG)]
  calc
    _ ≤ ((4 : ℝ) ^ R.card * tensorWeight w R * selbergMass w F) /
        selbergMass w F ^ 2 :=
      (div_le_div_iff_of_pos_right (sq_pos_of_pos hG)).mpr
        (habs.trans (tensorSieveCoefficient_sum_bound w hw0 hw1 F hdown R))
    _ = _ := by field_simp

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/SelbergFourierLocal.lean -/
section
/- # The exact one-prime Fourier coefficients of the Selberg function -/

namespace Erdos12Proof

variable {p : ℕ} [NeZero p]

noncomputable def localAdditiveChar (k x : ZMod p) : ℂ :=
  ZMod.stdAddChar ((-k) * x)

noncomputable def complexSieveLocal (p : ℕ) (x : ZMod p) : ℂ :=
  if x = 0 then -1 else 1 / ((p : ℂ) - 1)

theorem localAdditiveChar_zero (k : ZMod p) : localAdditiveChar k 0 = 1 := by
  simp [localAdditiveChar, AddChar.map_zero_eq_one]

theorem complexSieveLocal_fin (x : Fin p) :
    complexSieveLocal p (ZMod.finEquiv p x) = (sieveLocal p x : ℂ) := by
  by_cases hx : x.val = 0
  · have hx0 : x = 0 := Fin.ext hx
    simp [hx0, complexSieveLocal, sieveLocal]
  · have hx0 : x ≠ 0 := by
      intro h
      exact hx (by simp [h])
    have heq : ZMod.finEquiv p x ≠ 0 := by
      intro h
      apply hx0
      apply (ZMod.finEquiv p).injective
      simpa using h
    simp [complexSieveLocal, sieveLocal, sieveLocalWeight, hx, heq]

theorem localAdditiveChar_sum (k : ZMod p) :
    ∑ x : ZMod p, localAdditiveChar k x = if k = 0 then (p : ℂ) else 0 := by
  by_cases hk : k = 0
  · simp [localAdditiveChar, hk, AddChar.map_zero_eq_one, ZMod.card]
  · rw [ite_eq_right hk]
    have hsum := AddChar.sum_eq_zero_of_ne_one
      (ZMod.isPrimitive_stdAddChar p (neg_ne_zero.mpr hk))
    exact hsum

theorem localAdditiveChar_mean (k : ZMod p) :
    finiteMean (localAdditiveChar k) = if k = 0 then (1 : ℂ) else 0 := by
  unfold finiteMean
  rw [localAdditiveChar_sum, ZMod.card]
  split_ifs
  · exact div_self (by exact_mod_cast (NeZero.ne p))
  · exact zero_div _

theorem complexSieveLocal_fourier (hp : 1 < p) (k : ZMod p) :
    finiteMean (fun x => complexSieveLocal p x * localAdditiveChar k x) =
      if k = 0 then 0 else -(1 / ((p : ℂ) - 1)) := by
  classical
  have hform : (fun x : ZMod p => complexSieveLocal p x * localAdditiveChar k x) =
      fun x => (1 / ((p : ℂ) - 1)) * localAdditiveChar k x +
        if x = 0 then (-1 - 1 / ((p : ℂ) - 1)) else 0 := by
    funext x
    by_cases hx : x = 0
    · simp [hx, complexSieveLocal, localAdditiveChar_zero]
    · simp [hx, complexSieveLocal]
  rw [hform, finiteMean_add, finiteMean_const_mul, localAdditiveChar_mean]
  have hdelta : finiteMean (fun x : ZMod p =>
      if x = 0 then (-1 - 1 / ((p : ℂ) - 1)) else 0) =
      (-1 - 1 / ((p : ℂ) - 1)) / p := by
    simp [finiteMean, ZMod.card]
  rw [hdelta]
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
  have hp1 : (p : ℂ) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast (ne_of_gt hp)
  split_ifs
  · field_simp
    ring
  · field_simp
    ring

theorem complexSieveLocal_square (p : ℕ) (x : ZMod p) :
    complexSieveLocal p x ^ 2 = 1 / ((p : ℂ) - 1) +
      (1 / ((p : ℂ) - 1) - 1) * complexSieveLocal p x := by
  unfold complexSieveLocal
  split_ifs <;> ring

theorem complexSieveLocal_square_fourier (hp : 1 < p) (k : ZMod p) :
    finiteMean (fun x => complexSieveLocal p x ^ 2 * localAdditiveChar k x) =
      if k = 0 then 1 / ((p : ℂ) - 1) else
        (1 / ((p : ℂ) - 1)) * (1 - 1 / ((p : ℂ) - 1)) := by
  have hfun : (fun x => complexSieveLocal p x ^ 2 * localAdditiveChar k x) =
      fun x => (1 / ((p : ℂ) - 1)) * localAdditiveChar k x +
        (1 / ((p : ℂ) - 1) - 1) * (complexSieveLocal p x * localAdditiveChar k x) := by
    funext x
    rw [complexSieveLocal_square]
    ring
  rw [hfun, finiteMean_add, finiteMean_const_mul, finiteMean_const_mul,
    localAdditiveChar_mean, complexSieveLocal_fourier hp]
  split_ifs <;> ring

theorem complexSieveLocal_product_fourier (hp : 1 < p) (k : ZMod p) (a b : Bool) :
    finiteMean (fun x => (if a then complexSieveLocal p x else 1) *
      (if b then complexSieveLocal p x else 1) * localAdditiveChar k x) =
      (localSieveCoefficient (sieveLocalWeight p) a b (decide (k ≠ 0)) : ℂ) := by
  have hcast : ((sieveLocalWeight p : ℝ) : ℂ) = 1 / ((p : ℂ) - 1) := by
    simp [sieveLocalWeight]
  cases a <;> cases b
  · change finiteMean (fun x => (1 : ℂ) * 1 * localAdditiveChar k x) = _
    simp only [one_mul]
    rw [localAdditiveChar_mean]
    by_cases hk : k = 0 <;> simp [localSieveCoefficient, hk]
  · change finiteMean (fun x => 1 * complexSieveLocal p x * localAdditiveChar k x) = _
    simp only [one_mul]
    rw [complexSieveLocal_fourier hp]
    by_cases hk : k = 0 <;> simp [localSieveCoefficient, hk, hcast]
  · change finiteMean (fun x => complexSieveLocal p x * 1 * localAdditiveChar k x) = _
    simp only [mul_one]
    rw [complexSieveLocal_fourier hp]
    by_cases hk : k = 0 <;> simp [localSieveCoefficient, hk, hcast]
  · change finiteMean (fun x => complexSieveLocal p x * complexSieveLocal p x *
      localAdditiveChar k x) = _
    simp_rw [← pow_two]
    rw [complexSieveLocal_square_fourier hp]
    by_cases hk : k = 0 <;> simp [localSieveCoefficient, hk, hcast]

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/SelbergCoefficientDecay.lean -/
section
/- # Square-root decay after removing the small primes -/

namespace Erdos12Proof

theorem four_sieveLocalWeight_le {p : ℕ} (hp : 25 ≤ p) :
    4 * sieveLocalWeight p ≤ 1 / Real.sqrt (p : ℝ) := by
  have hpR : (25 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
  have hs : 5 ≤ Real.sqrt (p : ℝ) := Real.le_sqrt_of_sq_le (by norm_num; linarith)
  have hs0 : 0 < Real.sqrt (p : ℝ) := by linarith
  have hsq := Real.sq_sqrt hp0
  have hmul : 0 ≤ (Real.sqrt (p : ℝ) - 5) * Real.sqrt (p : ℝ) :=
    mul_nonneg (by linarith) hs0.le
  have hbound : 4 * Real.sqrt (p : ℝ) ≤ (p : ℝ) - 1 := by nlinarith
  unfold sieveLocalWeight
  rw [mul_one_div]
  apply (div_le_div_iff₀ (by linarith : 0 < (p : ℝ) - 1) hs0).mpr
  simpa only [one_mul] using hbound

theorem four_pow_tensorWeight_le {ι : Type*} [DecidableEq ι]
    (m : ι → ℕ) (R : Finset ι) (hm : ∀ i ∈ R, 25 ≤ m i) :
    (4 : ℝ) ^ R.card * tensorWeight (fun i => sieveLocalWeight (m i)) R ≤
      1 / Real.sqrt ((∏ i ∈ R, m i : ℕ) : ℝ) := by
  calc
    _ = ∏ i ∈ R, 4 * sieveLocalWeight (m i) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const]
      rfl
    _ ≤ ∏ i ∈ R, 1 / Real.sqrt (m i : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact mul_nonneg (by norm_num) (sieveLocalWeight_pos (by have := hm i hi; omega)).le
      · intro i hi
        exact four_sieveLocalWeight_le (hm i hi)
    _ = 1 / Real.sqrt ((∏ i ∈ R, m i : ℕ) : ℝ) := by
      simp only [one_div, Finset.prod_inv_distrib, Nat.cast_prod]
      rw [Real.sqrt_prod R (fun i _ => Nat.cast_nonneg (m i))]

theorem normalizedSieveCoefficient_decay {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) (hm : ∀ i, 25 ≤ m i) (z : ℝ) (hz : 1 < z) (R : Finset ι) :
    |normalizedSieveCoefficient (fun i => sieveLocalWeight (m i)) (sieveSupport m z) R| ≤
      1 / (sieveMass m z * Real.sqrt ((∏ i ∈ R, m i : ℕ) : ℝ)) := by
  have hm1 : ∀ i, 1 < m i := by intro i; have := hm i; omega
  have hG := sieveMass_pos hm1 hz
  have hbase := normalizedSieveCoefficient_bound (fun i => sieveLocalWeight (m i))
    (fun i => (sieveLocalWeight_pos (hm1 i)).le)
    (fun i => sieveLocalWeight_le_one (hm1 i)) (sieveSupport m z)
    (sieveSupport_empty hz) (sieveSupport_downwardClosed (fun i => (hm1 i).le) z) R
  calc
    _ ≤ ((4 : ℝ) ^ R.card * tensorWeight (fun i => sieveLocalWeight (m i)) R) /
        sieveMass m z := hbase
    _ ≤ (1 / Real.sqrt ((∏ i ∈ R, m i : ℕ) : ℝ)) / sieveMass m z :=
      (div_le_div_iff_of_pos_right hG).mpr (four_pow_tensorWeight_le m R (fun i _ => hm i))
    _ = _ := by ring

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/SelbergSpectrumSupport.lean -/
section
/- # The denominator support of the Selberg Fourier expansion -/

namespace Erdos12Proof

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem tensorSieveCoefficient_zero_of_not_subset (w : ι → ℝ) (R s t : Finset ι)
    (hR : ¬R ⊆ s ∪ t) : tensorSieveCoefficient w R s t = 0 := by
  obtain ⟨i, hiR, hist⟩ := Finset.not_subset.mp hR
  have his : i ∉ s := fun hi => hist (Finset.mem_union_left _ hi)
  have hit : i ∉ t := fun hi => hist (Finset.mem_union_right _ hi)
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [localSieveCoefficient, hiR, his, hit]

omit [Fintype ι] in
theorem product_subset_union_le (m : ι → ℕ) (hm : ∀ i, 1 ≤ m i)
    {R s t : Finset ι} (hR : R ⊆ s ∪ t) :
    (∏ i ∈ R, m i) ≤ (∏ i ∈ s, m i) * ∏ i ∈ t, m i := by
  have hsub : (∏ i ∈ R, m i) ≤ ∏ i ∈ s ∪ t, m i :=
    Finset.prod_le_prod_of_subset_of_one_le hR (fun i _ _ => hm i)
  have hi : 1 ≤ ∏ i ∈ s ∩ t, m i := Finset.one_le_prod (fun i _ => hm i)
  have hu : (∏ i ∈ s ∪ t, m i) ≤
      (∏ i ∈ s ∪ t, m i) * ∏ i ∈ s ∩ t, m i := by
    exact Nat.le_mul_of_pos_right _ (by omega)
  exact hsub.trans (hu.trans_eq Finset.prod_union_inter)

theorem normalizedSieveCoefficient_zero_of_large_support (m : ι → ℕ)
    (hm : ∀ i, 1 ≤ m i) (z : ℝ) (hz : 0 < z) (R : Finset ι)
    (hR : z ^ 2 ≤ ((∏ i ∈ R, m i : ℕ) : ℝ)) :
    normalizedSieveCoefficient (fun i => sieveLocalWeight (m i)) (sieveSupport m z) R = 0 := by
  have hzero : ∀ s ∈ sieveSupport m z, ∀ t ∈ sieveSupport m z,
      tensorSieveCoefficient (fun i => sieveLocalWeight (m i)) R s t = 0 := by
    intro s hs t ht
    apply tensorSieveCoefficient_zero_of_not_subset
    intro hsub
    have hprod : ((∏ i ∈ R, m i : ℕ) : ℝ) ≤
        ((∏ i ∈ s, m i : ℕ) : ℝ) * ((∏ i ∈ t, m i : ℕ) : ℝ) := by
      exact_mod_cast product_subset_union_le m hm hsub
    have hs' := (Finset.mem_filter.mp hs).2
    have ht' := (Finset.mem_filter.mp ht).2
    have htpos : 0 < ((∏ i ∈ t, m i : ℕ) : ℝ) := by
      exact_mod_cast Finset.prod_pos (fun i _ => lt_of_lt_of_le Nat.zero_lt_one (hm i))
    have hmul : ((∏ i ∈ s, m i : ℕ) : ℝ) * ((∏ i ∈ t, m i : ℕ) : ℝ) < z * z :=
      (mul_lt_mul_of_pos_right hs' htpos).trans (mul_lt_mul_of_pos_left ht' hz)
    nlinarith
  unfold normalizedSieveCoefficient
  rw [Finset.sum_eq_zero (fun s hs => Finset.sum_eq_zero (fun t ht => hzero s hs t ht))]
  exact zero_div _

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/SelbergFourier.lean -/
section
/- # Fourier coefficients of the finite Selberg majorant on product groups -/

namespace Erdos12Proof

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → ℕ)
variable [∀ i, NeZero (m i)]

abbrev ComplexSieveCube := ∀ i, ZMod (m i)

noncomputable def complexTensorBasis (s : Finset ι) (x : ComplexSieveCube m) : ℂ :=
  ∏ i, if i ∈ s then complexSieveLocal (m i) (x i) else 1

noncomputable def tensorAdditiveChar (k x : ComplexSieveCube m) : ℂ :=
  ∏ i, localAdditiveChar (k i) (x i)

noncomputable def tensorFourier (f : ComplexSieveCube m → ℂ) (k : ComplexSieveCube m) : ℂ :=
  finiteMean (fun x => f x * tensorAdditiveChar m k x)

noncomputable def frequencySupport (k : ComplexSieveCube m) : Finset ι :=
  Finset.univ.filter (fun i => k i ≠ 0)

noncomputable def sieveCubeToZMod : SieveCube m ≃ ComplexSieveCube m :=
  Equiv.piCongrRight (fun i => (ZMod.finEquiv (m i)).toEquiv)

theorem complexTensorBasis_equiv (s : Finset ι) (x : SieveCube m) :
    complexTensorBasis m s (sieveCubeToZMod m x) =
      (tensorBasis (fun i => sieveLocal (m i)) s x : ℂ) := by
  unfold complexTensorBasis tensorBasis
  push_cast
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ s
  · simp only [ite_eq_left hi]
    change complexSieveLocal (m i) (ZMod.finEquiv (m i) (x i)) = _
    exact complexSieveLocal_fin (x i)
  · simp [hi]

theorem tensorFourier_basis_product (hm : ∀ i, 1 < m i)
    (s t : Finset ι) (k : ComplexSieveCube m) :
    tensorFourier m (fun x => complexTensorBasis m s x * complexTensorBasis m t x) k =
      (tensorSieveCoefficient (fun i => sieveLocalWeight (m i)) (frequencySupport m k) s t : ℂ) := by
  have hfactor : tensorFourier m
      (fun x => complexTensorBasis m s x * complexTensorBasis m t x) k =
      ∏ i, finiteMean (fun x : ZMod (m i) =>
        (if i ∈ s then complexSieveLocal (m i) x else 1) *
        (if i ∈ t then complexSieveLocal (m i) x else 1) * localAdditiveChar (k i) x) := by
    simpa only [tensorFourier, complexTensorBasis, tensorAdditiveChar,
      Finset.prod_mul_distrib] using finiteMean_prod (fun i x =>
        (if i ∈ s then complexSieveLocal (m i) x else 1) *
        (if i ∈ t then complexSieveLocal (m i) x else 1) * localAdditiveChar (k i) x)
  rw [hfactor]
  unfold tensorSieveCoefficient
  push_cast
  apply Finset.prod_congr rfl
  intro i _
  simpa only [frequencySupport, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] using
    complexSieveLocal_product_fourier (hm i) (k i) (decide (i ∈ s)) (decide (i ∈ t))

theorem tensorFourier_sum {κ : Type*} (F : Finset κ) (f : κ → ComplexSieveCube m → ℂ)
    (k : ComplexSieveCube m) :
    tensorFourier m (fun x => ∑ s ∈ F, f s x) k = ∑ s ∈ F, tensorFourier m (f s) k := by
  unfold tensorFourier
  simp only [Finset.sum_mul]
  exact finiteMean_sum F _

theorem tensorFourier_div_const (f : ComplexSieveCube m → ℂ) (c : ℂ)
    (k : ComplexSieveCube m) :
    tensorFourier m (fun x => f x / c) k = tensorFourier m f k / c := by
  unfold tensorFourier
  simp only [div_eq_mul_inv]
  calc
    _ = finiteMean (fun x => (f x * tensorAdditiveChar m k x) * c⁻¹) := by
      congr 1
      funext x
      ring
    _ = _ := finiteMean_mul_const _ _

noncomputable def complexSelbergSum (z : ℝ) (x : ComplexSieveCube m) : ℂ :=
  ∑ s ∈ sieveSupport m z, complexTensorBasis m s x

noncomputable def complexSelbergMajorant (z : ℝ) (x : ComplexSieveCube m) : ℂ :=
  complexSelbergSum m z x ^ 2 / (sieveMass m z : ℂ) ^ 2

theorem complexSelbergMajorant_equiv (z : ℝ) (x : SieveCube m) :
    complexSelbergMajorant m z (sieveCubeToZMod m x) = (sieveMajorant m z x : ℂ) := by
  have hsum : complexSelbergSum m z (sieveCubeToZMod m x) =
      (selbergSum (fun i => sieveLocal (m i)) (sieveSupport m z) x : ℂ) := by
    unfold complexSelbergSum selbergSum
    simp only [Complex.ofReal_sum, complexTensorBasis_equiv]
  unfold complexSelbergMajorant
  rw [hsum]
  unfold sieveMajorant selbergMajorant sieveMass
  push_cast
  rfl

theorem complexSelbergMajorant_fourier (hm : ∀ i, 1 < m i)
    (z : ℝ) (k : ComplexSieveCube m) :
    tensorFourier m (complexSelbergMajorant m z) k =
      (normalizedSieveCoefficient (fun i => sieveLocalWeight (m i))
        (sieveSupport m z) (frequencySupport m k) : ℂ) := by
  change tensorFourier m (fun x => complexSelbergSum m z x ^ 2 / (sieveMass m z : ℂ) ^ 2) k = _
  rw [tensorFourier_div_const]
  have hsum : (fun x => complexSelbergSum m z x ^ 2) =
      fun x => ∑ s ∈ sieveSupport m z, ∑ t ∈ sieveSupport m z,
        complexTensorBasis m s x * complexTensorBasis m t x := by
    funext x
    simp only [complexSelbergSum, pow_two, Finset.sum_mul_sum]
  rw [hsum, tensorFourier_sum]
  simp_rw [tensorFourier_sum, tensorFourier_basis_product m hm]
  unfold normalizedSieveCoefficient sieveMass
  push_cast
  rfl

theorem complexSelbergMajorant_fourier_decay (hm : ∀ i, 25 ≤ m i)
    (z : ℝ) (hz : 1 < z) (k : ComplexSieveCube m) :
    ‖tensorFourier m (complexSelbergMajorant m z) k‖ ≤
      1 / (sieveMass m z *
        Real.sqrt ((∏ i ∈ frequencySupport m k, m i : ℕ) : ℝ)) := by
  rw [complexSelbergMajorant_fourier m (by intro i; have := hm i; omega),
    Complex.norm_real, Real.norm_eq_abs]
  exact normalizedSieveCoefficient_decay m hm z hz (frequencySupport m k)

theorem complexSelbergMajorant_fourier_zero_of_large_support (hm : ∀ i, 1 < m i)
    (z : ℝ) (hz : 0 < z) (k : ComplexSieveCube m)
    (hk : z ^ 2 ≤ ((∏ i ∈ frequencySupport m k, m i : ℕ) : ℝ)) :
    tensorFourier m (complexSelbergMajorant m z) k = 0 := by
  rw [complexSelbergMajorant_fourier m hm]
  rw [normalizedSieveCoefficient_zero_of_large_support m (fun i => (hm i).le) z hz _ hk]
  rfl

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/SelbergFourierInversion.lean -/
section
/- # Fourier inversion and the finite spectral expansion of the majorant -/

namespace Erdos12Proof

theorem localAdditiveChar_mul_neg {p : ℕ} [NeZero p] (k x y : ZMod p) :
    localAdditiveChar k x * localAdditiveChar (-k) y = localAdditiveChar k (x - y) := by
  unfold localAdditiveChar
  rw [← AddChar.map_add_eq_mul]
  congr 1
  ring

theorem localAdditiveChar_symm {p : ℕ} [NeZero p] (k x : ZMod p) :
    localAdditiveChar k x = localAdditiveChar x k := by
  unfold localAdditiveChar
  congr 1
  ring

theorem localAdditiveChar_orthogonality {p : ℕ} [NeZero p] (x y : ZMod p) :
    (∑ k : ZMod p, localAdditiveChar k x * localAdditiveChar (-k) y) =
      if x = y then (p : ℂ) else 0 := by
  calc
    _ = ∑ k : ZMod p, localAdditiveChar (x - y) k := by
      apply Finset.sum_congr rfl
      intro k _
      rw [localAdditiveChar_mul_neg, localAdditiveChar_symm]
    _ = _ := by rw [localAdditiveChar_sum]; simp only [sub_eq_zero]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → ℕ)
variable [∀ i, NeZero (m i)]

theorem tensorAdditiveChar_orthogonality (x y : ComplexSieveCube m) :
    (∑ k : ComplexSieveCube m, tensorAdditiveChar m k x * tensorAdditiveChar m (-k) y) =
      if x = y then (Fintype.card (ComplexSieveCube m) : ℂ) else 0 := by
  have hprod : (∑ k : ComplexSieveCube m,
      tensorAdditiveChar m k x * tensorAdditiveChar m (-k) y) =
      ∏ i, ∑ k : ZMod (m i), localAdditiveChar k (x i) * localAdditiveChar (-k) (y i) := by
    simpa only [tensorAdditiveChar, Pi.neg_apply, Finset.prod_mul_distrib] using
      (Fintype.prod_sum (fun i k => localAdditiveChar k (x i) * localAdditiveChar (-k) (y i))).symm
  rw [hprod]
  simp_rw [localAdditiveChar_orthogonality]
  by_cases hxy : x = y
  · subst y
    simp [ComplexSieveCube, Fintype.card_pi, ZMod.card, Nat.cast_prod]
  · rw [ite_eq_right hxy]
    have hnot : ¬∀ i, x i = y i := fun h => hxy (funext h)
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

theorem tensorFourier_inversion (f : ComplexSieveCube m → ℂ) (y : ComplexSieveCube m) :
    (∑ k : ComplexSieveCube m, tensorFourier m f k * tensorAdditiveChar m (-k) y) = f y := by
  calc
    _ = finiteMean (fun x => ∑ k : ComplexSieveCube m,
        (f x * tensorAdditiveChar m k x) * tensorAdditiveChar m (-k) y) := by
      simp only [finiteMean_sum, finiteMean_mul_const, tensorFourier]
    _ = finiteMean (fun x => f x * ∑ k : ComplexSieveCube m,
        tensorAdditiveChar m k x * tensorAdditiveChar m (-k) y) := by
      congr 1
      funext x
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = finiteMean (fun x => f x *
        if x = y then (Fintype.card (ComplexSieveCube m) : ℂ) else 0) := by
      simp only [tensorAdditiveChar_orthogonality]
    _ = f y := by
      unfold finiteMean
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      exact mul_div_cancel_right₀ _ (by exact_mod_cast Fintype.card_ne_zero)

theorem complexSelbergMajorant_spectral_expansion (hm : ∀ i, 1 < m i)
    (z : ℝ) (hz : 0 < z) (x : ComplexSieveCube m) :
    complexSelbergMajorant m z x =
      ∑ k : ComplexSieveCube m with
        ((∏ i ∈ frequencySupport m k, m i : ℕ) : ℝ) < z ^ 2,
        tensorFourier m (complexSelbergMajorant m z) k * tensorAdditiveChar m (-k) x := by
  rw [← tensorFourier_inversion m (complexSelbergMajorant m z) x]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro k _ hk
  have hlarge : z ^ 2 ≤ ((∏ i ∈ frequencySupport m k, m i : ℕ) : ℝ) := by
    by_contra h
    exact hk (Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge h⟩)
  rw [complexSelbergMajorant_fourier_zero_of_large_support m hm z hz k hlarge, zero_mul]

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/SelbergCharacters.lean -/
section
/- # The cyclic generator of the product of the prime residue groups -/

namespace Erdos12Proof

noncomputable def unitExp (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

theorem unitExp_add (s t : ℝ) : unitExp (s + t) = unitExp s * unitExp t := by
  unfold unitExp
  push_cast
  rw [mul_add, Complex.exp_add]

theorem unitExp_int (n : ℤ) : unitExp n = 1 := by
  unfold unitExp
  apply Complex.exp_eq_one_iff.mpr
  exact ⟨n, by push_cast; ring⟩

theorem unitExp_nat_mul (t : ℝ) (n : ℕ) : unitExp (n * t) = unitExp t ^ n := by
  unfold unitExp
  push_cast
  rw [show 2 * Real.pi * Complex.I * ((n : ℂ) * t) =
    (n : ℂ) * (2 * Real.pi * Complex.I * t) by ring]
  exact Complex.exp_nat_mul _ _

theorem unitExp_int_mul (t : ℝ) (n : ℤ) : unitExp (n * t) = unitExp t ^ n := by
  unfold unitExp
  push_cast
  rw [show 2 * Real.pi * Complex.I * ((n : ℂ) * t) =
    (n : ℂ) * (2 * Real.pi * Complex.I * t) by ring]
  exact Complex.exp_int_mul _ _

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → ℕ)
variable [∀ i, NeZero (m i)]

noncomputable def integerCube (n : ℕ) : ComplexSieveCube m := fun i => (n : ZMod (m i))

noncomputable def integerCubeZ (n : ℤ) : ComplexSieveCube m := fun i => (n : ZMod (m i))

noncomputable def generatorCharacter (k : ComplexSieveCube m) : ℂ :=
  tensorAdditiveChar m (-k) (fun _ => 1)

omit [DecidableEq ι] in
theorem tensorAdditiveChar_symm (x y : ComplexSieveCube m) :
    tensorAdditiveChar m x y = tensorAdditiveChar m y x := by
  unfold tensorAdditiveChar
  apply Finset.prod_congr rfl
  intro i _
  exact localAdditiveChar_symm _ _

omit [DecidableEq ι] in
theorem tensorCharacter_nat (k : ComplexSieveCube m) (n : ℕ) :
    tensorAdditiveChar m (-k) (integerCube m n) = generatorCharacter m k ^ n := by
  simp only [generatorCharacter, tensorAdditiveChar, integerCube]
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Pi.neg_apply, localAdditiveChar, neg_neg, mul_one]
  calc
    ZMod.stdAddChar (k i * (n : ZMod (m i))) = ZMod.stdAddChar (n • k i) := by
      congr 1
      simp only [nsmul_eq_mul, mul_comm]
    _ = ZMod.stdAddChar (k i) ^ n := AddChar.map_nsmul_eq_pow _ _ _

omit [DecidableEq ι] in
theorem tensorCharacter_int (k : ComplexSieveCube m) (n : ℤ) :
    tensorAdditiveChar m (-k) (integerCubeZ m n) = generatorCharacter m k ^ n := by
  simp only [generatorCharacter, tensorAdditiveChar, integerCubeZ]
  rw [← Finset.prod_zpow]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Pi.neg_apply, localAdditiveChar, neg_neg, mul_one]
  calc
    ZMod.stdAddChar (k i * (n : ZMod (m i))) = ZMod.stdAddChar (n • k i) := by
      congr 1
      simp only [zsmul_eq_mul, mul_comm]
    _ = ZMod.stdAddChar (k i) ^ n := AddChar.map_zsmul_eq_zpow _ _ _

omit [DecidableEq ι] in
theorem integerCube_surjective (hm : ∀ i, 0 < m i)
    (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j)) : Function.Surjective (integerCube m) := by
  intro x
  have hpair : Set.Pairwise (↑(Finset.univ : Finset ι)) (fun i j => (m i).Coprime (m j)) := by
    intro i _ j _ hij
    exact hcop i j hij
  let n := Nat.chineseRemainderOfFinset (fun i => (x i).val) m Finset.univ
    (fun i _ => Nat.ne_of_gt (hm i)) hpair
  refine ⟨n.val, ?_⟩
  funext i
  have hi : n.val % m i = (x i).val % m i := n.property i (Finset.mem_univ i)
  have hmod : n.val % m i = (x i).val := hi.trans (Nat.mod_eq_of_lt (ZMod.val_lt _))
  change (n.val : ZMod (m i)) = x i
  rw [← ZMod.natCast_mod n.val (m i), hmod, ZMod.natCast_zmod_val]

theorem tensorCharacter_injective (k l : ComplexSieveCube m)
    (h : ∀ x, tensorAdditiveChar m k x = tensorAdditiveChar m l x) : k = l := by
  by_contra hkl
  have hsum : (∑ x : ComplexSieveCube m,
      tensorAdditiveChar m x k * tensorAdditiveChar m (-x) l) =
      ∑ x : ComplexSieveCube m, tensorAdditiveChar m x k * tensorAdditiveChar m (-x) k := by
    apply Finset.sum_congr rfl
    intro x _
    rw [tensorAdditiveChar_symm m (-x) l, ← h (-x), tensorAdditiveChar_symm m k (-x)]
  have hz : (Fintype.card (ComplexSieveCube m) : ℂ) = 0 := by
    calc
      _ = ∑ x : ComplexSieveCube m,
          tensorAdditiveChar m x k * tensorAdditiveChar m (-x) k := by
        simpa using (tensorAdditiveChar_orthogonality m k k).symm
      _ = ∑ x : ComplexSieveCube m,
          tensorAdditiveChar m x k * tensorAdditiveChar m (-x) l := hsum.symm
      _ = 0 := by simpa [hkl] using tensorAdditiveChar_orthogonality m k l
  exact (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) hz

theorem generatorCharacter_injective (hm : ∀ i, 0 < m i)
    (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j)) :
    Function.Injective (generatorCharacter m) := by
  intro k l hkl
  have hneg : -k = -l := by
    apply tensorCharacter_injective m
    intro x
    obtain ⟨n, rfl⟩ := integerCube_surjective m hm hcop x
    rw [tensorCharacter_nat, tensorCharacter_nat, hkl]
  exact neg_injective hneg

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/SelbergRationalFrequencies.lean -/
section
/- # Rational frequencies associated with the product-group characters -/

namespace Erdos12Proof

theorem unitExp_sum {α : Type*} (S : Finset α) (f : α → ℝ) :
    unitExp (∑ i ∈ S, f i) = ∏ i ∈ S, unitExp (f i) := by
  unfold unitExp
  push_cast
  rw [Finset.mul_sum, Complex.exp_sum]

theorem local_generator_unitExp {p : ℕ} [NeZero p] (k : ZMod p) :
    localAdditiveChar (-k) 1 = unitExp ((k.val : ℝ) / p) := by
  simp only [localAdditiveChar, neg_neg, mul_one]
  calc
    ZMod.stdAddChar k = Complex.exp (2 * Real.pi * Complex.I * (k.val : ℂ) / p) := by
      simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using
        (ZMod.stdAddChar_coe (N := p) (k.val : ℤ))
    _ = unitExp ((k.val : ℝ) / p) := by
      unfold unitExp
      push_cast
      congr 1
      ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → ℕ)
variable [∀ i, NeZero (m i)]

noncomputable def sieveFrequency (k : ComplexSieveCube m) : ℝ :=
  ∑ i, (k i).val / (m i : ℝ)

omit [DecidableEq ι] in
theorem generatorCharacter_unitExp (k : ComplexSieveCube m) :
    generatorCharacter m k = unitExp (sieveFrequency m k) := by
  unfold generatorCharacter tensorAdditiveChar sieveFrequency
  simp only [Pi.neg_apply, local_generator_unitExp]
  exact (unitExp_sum Finset.univ (fun i => (k i).val / (m i : ℝ))).symm

omit [DecidableEq ι] in
theorem integer_character_unitExp (k : ComplexSieveCube m) (n : ℕ) :
    tensorAdditiveChar m (-k) (integerCube m n) = unitExp (n * sieveFrequency m k) := by
  rw [tensorCharacter_nat, generatorCharacter_unitExp, unitExp_nat_mul]

omit [DecidableEq ι] in
theorem integer_character_unitExp_int (k : ComplexSieveCube m) (n : ℤ) :
    tensorAdditiveChar m (-k) (integerCubeZ m n) = unitExp (n * sieveFrequency m k) := by
  rw [tensorCharacter_int, generatorCharacter_unitExp, unitExp_int_mul]

theorem frequency_exponential_injective (hm : ∀ i, 0 < m i)
    (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j)) :
    Function.Injective (fun k => unitExp (sieveFrequency m k)) := by
  intro k l h
  apply generatorCharacter_injective m hm hcop
  simpa only [generatorCharacter_unitExp] using h

theorem frequency_difference_not_int (hm : ∀ i, 0 < m i)
    (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    {k l : ComplexSieveCube m} (hkl : k ≠ l) (n : ℤ) :
    sieveFrequency m k - sieveFrequency m l ≠ (n : ℝ) := by
  intro h
  have heq : sieveFrequency m k = sieveFrequency m l + n := by linarith
  apply hkl
  apply frequency_exponential_injective m hm hcop
  change unitExp (sieveFrequency m k) = unitExp (sieveFrequency m l)
  rw [heq, unitExp_add, unitExp_int, mul_one]

noncomputable def spectralDenominator (k : ComplexSieveCube m) : ℕ :=
  ∏ i ∈ frequencySupport m k, m i

noncomputable def spectralNumerator (k : ComplexSieveCube m) : ℕ :=
  ∑ i, (k i).val * (spectralDenominator m k / m i)

omit [DecidableEq ι] in
theorem spectralDenominator_pos (k : ComplexSieveCube m) : 0 < spectralDenominator m k :=
  Finset.prod_pos (fun i _ => Nat.pos_of_ne_zero (NeZero.ne (m i)))

omit [DecidableEq ι] in
theorem sieveFrequency_eq_fraction (k : ComplexSieveCube m) :
    sieveFrequency m k = (spectralNumerator m k : ℝ) / spectralDenominator m k := by
  have hD : (spectralDenominator m k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (spectralDenominator_pos m k))
  apply (eq_div_iff hD).mpr
  unfold sieveFrequency spectralNumerator
  rw [Finset.sum_mul, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hk : k i = 0
  · simp [hk]
  · have hi : i ∈ frequencySupport m k := by simp [frequencySupport, hk]
    have hdiv : m i ∣ spectralDenominator m k := Finset.dvd_prod_of_mem m hi
    have hfactor : ((spectralDenominator m k / m i : ℕ) : ℝ) * (m i : ℝ) =
        spectralDenominator m k := by exact_mod_cast Nat.div_mul_cancel hdiv
    have hm0 : (m i : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne (m i))
    rw [Nat.cast_mul]
    calc
      ((k i).val / (m i : ℝ)) * spectralDenominator m k =
          ((k i).val / (m i : ℝ)) * (((spectralDenominator m k / m i : ℕ) : ℝ) * m i) :=
        by rw [hfactor]
      _ = _ := by field_simp

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/SelbergFrequencySpacing.lean -/
section
/- # Uniform separation of the rational frequencies in the Selberg spectrum -/

namespace Erdos12Proof

theorem fraction_integer_separation (a b d e : ℕ) (hd : 0 < d) (he : 0 < e) (n : ℤ)
    (hne : (a : ℝ) / d - (b : ℝ) / e ≠ (n : ℝ)) :
    1 / ((d : ℝ) * e) ≤ |(a : ℝ) / d - (b : ℝ) / e - n| := by
  let z : ℤ := (a : ℤ) * e - (b : ℤ) * d - n * d * e
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have he0 : (e : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt he)
  have hprod : 0 < (d : ℝ) * e := mul_pos (by exact_mod_cast hd) (by exact_mod_cast he)
  have hratio : (a : ℝ) / d - (b : ℝ) / e - n = (z : ℝ) / ((d : ℝ) * e) := by
    dsimp only [z]
    push_cast
    field_simp
  have hz : z ≠ 0 := by
    intro hz0
    have hzero : (a : ℝ) / d - (b : ℝ) / e - n = 0 := by rw [hratio, hz0]; simp
    exact hne (sub_eq_zero.mp hzero)
  have hzR : (1 : ℝ) ≤ |(z : ℝ)| := by exact_mod_cast Int.one_le_abs hz
  rw [hratio, abs_div, abs_of_pos hprod]
  exact div_le_div_of_nonneg_right hzR hprod.le

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → ℕ)
variable [∀ i, NeZero (m i)]

theorem sieveFrequency_integer_separation (hm : ∀ i, 0 < m i)
    (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    {k l : ComplexSieveCube m} (hkl : k ≠ l) (n : ℤ) :
    1 / ((spectralDenominator m k : ℝ) * spectralDenominator m l) ≤
      |sieveFrequency m k - sieveFrequency m l - n| := by
  rw [sieveFrequency_eq_fraction m k, sieveFrequency_eq_fraction m l]
  apply fraction_integer_separation _ _ _ _
    (spectralDenominator_pos m k) (spectralDenominator_pos m l) n
  simpa only [← sieveFrequency_eq_fraction m k, ← sieveFrequency_eq_fraction m l] using
    frequency_difference_not_int m hm hcop hkl n

theorem sieveFrequency_separated (hm : ∀ i, 0 < m i)
    (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j)) {Z : ℝ} (_hZ : 0 < Z)
    {k l : ComplexSieveCube m} (hkl : k ≠ l)
    (hk : (spectralDenominator m k : ℝ) < Z ^ 2)
    (hl : (spectralDenominator m l : ℝ) < Z ^ 2) (n : ℤ) :
    1 / Z ^ 4 ≤ |sieveFrequency m k - sieveFrequency m l - n| := by
  have hD : 0 < (spectralDenominator m k : ℝ) * spectralDenominator m l :=
    mul_pos (by exact_mod_cast spectralDenominator_pos m k)
      (by exact_mod_cast spectralDenominator_pos m l)
  have hupper : (spectralDenominator m k : ℝ) * spectralDenominator m l ≤ Z ^ 4 := by
    calc
      _ ≤ Z ^ 2 * Z ^ 2 := mul_le_mul hk.le hl.le
        (by exact_mod_cast (spectralDenominator_pos m l).le) (sq_nonneg Z)
      _ = Z ^ 4 := by ring
  exact (one_div_le_one_div_of_le hD hupper).trans
    (sieveFrequency_integer_separation m hm hcop hkl n)

theorem sieveFrequency_circle_separated (hm : ∀ i, 0 < m i)
    (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j)) {Z : ℝ} (hZ : 0 < Z)
    {k l : ComplexSieveCube m} (hkl : k ≠ l)
    (hk : (spectralDenominator m k : ℝ) < Z ^ 2)
    (hl : (spectralDenominator m l : ℝ) < Z ^ 2) :
    1 / Z ^ 4 ≤ dist (sieveFrequency m k : UnitAddCircle) (sieveFrequency m l : UnitAddCircle) := by
  rw [dist_eq_norm, ← AddCircle.coe_sub, UnitAddCircle.norm_eq]
  exact sieveFrequency_separated m hm hcop hZ hkl hk hl _

theorem sieveFrequency_unique_near (hm : ∀ i, 0 < m i)
    (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j)) {Z η : ℝ} (hZ : 0 < Z)
    (hη : 2 * η < 1 / Z ^ 4) (x : UnitAddCircle) {k l : ComplexSieveCube m}
    (hk : (spectralDenominator m k : ℝ) < Z ^ 2)
    (hl : (spectralDenominator m l : ℝ) < Z ^ 2)
    (hkx : dist (sieveFrequency m k : UnitAddCircle) x ≤ η)
    (hlx : dist x (sieveFrequency m l : UnitAddCircle) ≤ η) : k = l := by
  by_contra hkl
  have hsep := sieveFrequency_circle_separated m hm hcop hZ hkl hk hl
  have htri := dist_triangle (sieveFrequency m k : UnitAddCircle) x
    (sieveFrequency m l : UnitAddCircle)
  linarith

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/SelbergIntegerExpansion.lean -/
section
/- # The rational-frequency expansion of the integer Selberg majorant -/

namespace Erdos12Proof

theorem finiteMean_complexCast {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) :
    finiteMean (fun x => (f x : ℂ)) = ((finiteMean f : ℝ) : ℂ) := by
  unfold finiteMean
  push_cast
  rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → ℕ)
variable [∀ i, NeZero (m i)]

omit [∀ i, NeZero (m i)] in
theorem complexTensorBasis_on_survivor (s : Finset ι) (x : ComplexSieveCube m)
    (hx : ∀ i, x i ≠ 0) :
    complexTensorBasis m s x = (tensorWeight (fun i => sieveLocalWeight (m i)) s : ℂ) := by
  unfold complexTensorBasis
  simp only [complexSieveLocal, ite_eq_right (hx _)]
  rw [Fintype.prod_ite_mem]
  unfold tensorWeight sieveLocalWeight
  push_cast
  rfl

omit [∀ i, NeZero (m i)] in
theorem complexSelbergMajorant_on_survivor (hm : ∀ i, 1 < m i) (z : ℝ) (hz : 1 < z)
    (x : ComplexSieveCube m) (hx : ∀ i, x i ≠ 0) : complexSelbergMajorant m z x = 1 := by
  have hsum : complexSelbergSum m z x = (sieveMass m z : ℂ) := by
    unfold complexSelbergSum sieveMass selbergMass
    simp only [complexTensorBasis_on_survivor m _ x hx, Complex.ofReal_sum]
  unfold complexSelbergMajorant
  rw [hsum]
  exact div_self (pow_ne_zero _ (by exact_mod_cast (ne_of_gt (sieveMass_pos hm hz))))

theorem tensorFourier_zero (f : ComplexSieveCube m → ℂ) : tensorFourier m f 0 = finiteMean f := by
  unfold tensorFourier tensorAdditiveChar
  simp only [Pi.zero_apply, localAdditiveChar, neg_zero, zero_mul,
    AddChar.map_zero_eq_one, Finset.prod_const_one, mul_one]

theorem complexSelbergMajorant_zero_coefficient (hm : ∀ i, 1 < m i)
    (z : ℝ) (hz : 1 < z) :
    tensorFourier m (complexSelbergMajorant m z) 0 = (1 / sieveMass m z : ℂ) := by
  rw [tensorFourier_zero]
  have hmean := finiteMean_equiv (sieveCubeToZMod m) (complexSelbergMajorant m z)
  rw [← hmean]
  simp only [complexSelbergMajorant_equiv, finiteMean_complexCast, sieveMajorant_mean hm hz]
  push_cast
  rfl

noncomputable def integerSieveMajorant (z : ℝ) (n : ℤ) : ℝ :=
  sieveMajorant m z ((sieveCubeToZMod m).symm (integerCubeZ m n))

noncomputable def integerSieveCoefficient (z : ℝ) (k : ComplexSieveCube m) : ℝ :=
  normalizedSieveCoefficient (fun i => sieveLocalWeight (m i)) (sieveSupport m z)
    (frequencySupport m k)

theorem integerSieveMajorant_nonneg (z : ℝ) (n : ℤ) : 0 ≤ integerSieveMajorant m z n :=
  sieveMajorant_nonneg _ _ _

theorem integerSieveMajorant_complex (z : ℝ) (n : ℤ) :
    (integerSieveMajorant m z n : ℂ) = complexSelbergMajorant m z (integerCubeZ m n) := by
  have h := complexSelbergMajorant_equiv m z ((sieveCubeToZMod m).symm (integerCubeZ m n))
  simpa only [integerSieveMajorant, Equiv.apply_symm_apply] using h.symm

theorem integerSieveMajorant_eq_one (hm : ∀ i, 1 < m i) (z : ℝ) (hz : 1 < z)
    (n : ℤ) (hn : ∀ i, (n : ZMod (m i)) ≠ 0) : integerSieveMajorant m z n = 1 := by
  apply Complex.ofReal_injective
  rw [integerSieveMajorant_complex]
  exact complexSelbergMajorant_on_survivor m hm z hz (integerCubeZ m n) hn

theorem integerSieveMajorant_expansion (hm : ∀ i, 1 < m i) (z : ℝ) (hz : 0 < z) (n : ℤ) :
    (integerSieveMajorant m z n : ℂ) =
      ∑ k : ComplexSieveCube m with (spectralDenominator m k : ℝ) < z ^ 2,
        (integerSieveCoefficient m z k : ℂ) * unitExp (n * sieveFrequency m k) := by
  rw [integerSieveMajorant_complex, complexSelbergMajorant_spectral_expansion m hm z hz]
  simp only [spectralDenominator, integer_character_unitExp_int,
    complexSelbergMajorant_fourier m hm z, integerSieveCoefficient]
  rfl

theorem integerSieveCoefficient_zero (hm : ∀ i, 1 < m i) (z : ℝ) (hz : 1 < z) :
    integerSieveCoefficient m z 0 = 1 / sieveMass m z := by
  apply Complex.ofReal_injective
  have h := complexSelbergMajorant_zero_coefficient m hm z hz
  rw [complexSelbergMajorant_fourier m hm z] at h
  simpa only [integerSieveCoefficient, Complex.ofReal_div, Complex.ofReal_one] using h

omit [∀ i, NeZero (m i)] in
theorem integerSieveCoefficient_bound (hm : ∀ i, 25 ≤ m i) (z : ℝ) (hz : 1 < z)
    (k : ComplexSieveCube m) :
    |integerSieveCoefficient m z k| ≤
      1 / (sieveMass m z * Real.sqrt (spectralDenominator m k : ℝ)) :=
  normalizedSieveCoefficient_decay m hm z hz (frequencySupport m k)

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/CyclicFourier.lean -/
section
/- # Normalized Fourier analysis on a finite cyclic group -/

open scoped ComplexConjugate

namespace Erdos12Proof

variable {M : ℕ} [NeZero M]

noncomputable def cyclicFourier (f : ZMod M → ℂ) (k : ZMod M) : ℂ :=
  (M : ℂ)⁻¹ * ZMod.dft f k

theorem cyclicFourier_unscaled (f : ZMod M → ℂ) (k : ZMod M) :
    (∑ x : ZMod M, f x * ZMod.stdAddChar (-(x * k))) = (M : ℂ) * cyclicFourier f k := by
  unfold cyclicFourier
  rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast (NeZero.ne M)), one_mul, ZMod.dft_apply]
  simp only [smul_eq_mul, mul_comm]

theorem cyclicFourier_zero (f : ZMod M → ℂ) : cyclicFourier f 0 = finiteMean f := by
  unfold cyclicFourier finiteMean
  rw [ZMod.dft_apply_zero]
  simp only [ZMod.card]
  ring

theorem cyclicFourier_inversion (f : ZMod M → ℂ) (x : ZMod M) :
    (∑ k : ZMod M, cyclicFourier f k * ZMod.stdAddChar (k * x)) = f x := by
  have h := congrFun (ZMod.dft.symm_apply_apply f) x
  rw [ZMod.invDFT_apply] at h
  calc
    _ = (M : ℂ)⁻¹ * ∑ k : ZMod M, ZMod.stdAddChar (k * x) * ZMod.dft f k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      unfold cyclicFourier
      ring
    _ = f x := by simpa only [smul_eq_mul] using h

theorem cyclicFourier_inner (f g : ZMod M → ℂ) :
    (∑ k : ZMod M, cyclicFourier f k * conj (cyclicFourier g k)) =
      finiteMean (fun x => f x * conj (g x)) := by
  have hsum : (∑ x : ZMod M, f x * conj (g x)) =
      (M : ℂ) * ∑ k : ZMod M, cyclicFourier f k * conj (cyclicFourier g k) := by
    calc
      _ = ∑ x : ZMod M, ∑ k : ZMod M,
          f x * (conj (cyclicFourier g k) * conj (ZMod.stdAddChar (k * x))) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [← cyclicFourier_inversion g x, map_sum, Finset.mul_sum]
        simp only [map_mul]
      _ = ∑ k : ZMod M, conj (cyclicFourier g k) *
          ∑ x : ZMod M, f x * ZMod.stdAddChar (-(x * k)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        rw [← AddChar.map_neg_eq_conj, mul_comm k x]
        ring
      _ = _ := by
        simp only [cyclicFourier_unscaled]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
  symm
  unfold finiteMean
  rw [ZMod.card, hsum]
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne M)
  field_simp

theorem cyclicFourier_parseval (f : ZMod M → ℂ) :
    (∑ k : ZMod M, ‖cyclicFourier f k‖ ^ 2) = finiteMean (fun x => ‖f x‖ ^ 2) := by
  have h := cyclicFourier_inner f f
  simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq, finiteMean_complexCast] at h
  exact_mod_cast h

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/CyclicCorrelation.lean -/
section
/- # The Fourier identity for additive correlations -/

namespace Erdos12Proof

variable {M : ℕ} [NeZero M]

theorem cyclicFourier_asMean (f : ZMod M → ℂ) (k : ZMod M) :
    cyclicFourier f k = finiteMean (fun x => f x * ZMod.stdAddChar (-(x * k))) := by
  symm
  unfold finiteMean
  rw [ZMod.card, cyclicFourier_unscaled]
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne M)
  field_simp

theorem cyclicFourier_positiveMean (f : ZMod M → ℂ) (k : ZMod M) :
    finiteMean (fun x => f x * ZMod.stdAddChar (k * x)) = cyclicFourier f (-k) := by
  rw [cyclicFourier_asMean]
  congr 1
  funext x
  rw [mul_neg, neg_neg, mul_comm x k]

noncomputable def cyclicCorrelation (f g h : ZMod M → ℂ) : ℂ :=
  finiteMean (fun x => finiteMean (fun y => f x * g y * h (x + y)))

theorem cyclicCorrelation_fourier (f g h : ZMod M → ℂ) :
    cyclicCorrelation f g h = ∑ k : ZMod M,
      cyclicFourier h k * cyclicFourier f (-k) * cyclicFourier g (-k) := by
  have hpoint (x y : ZMod M) : f x * g y * h (x + y) =
      ∑ k : ZMod M, cyclicFourier h k *
        (f x * ZMod.stdAddChar (k * x)) * (g y * ZMod.stdAddChar (k * y)) := by
    rw [← cyclicFourier_inversion h (x + y), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_add, AddChar.map_add_eq_mul]
    ring
  unfold cyclicCorrelation
  simp_rw [hpoint, finiteMean_sum, finiteMean_const_mul, finiteMean_mul_const,
    cyclicFourier_positiveMean]
  simp_rw [finiteMean_const_mul, cyclicFourier_positiveMean]

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/CyclicDilations.lean -/
section
/- # Weighted images and averages of cyclic dilations -/

namespace Erdos12Proof

noncomputable def finitePushforward {α β : Type*} [Fintype α] [DecidableEq β]
    (u : α → β) (f : α → ℂ) (y : β) : ℂ :=
  ∑ x : α with u x = y, f x

theorem finitePushforward_weighted_sum {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (u : α → β) (f : α → ℂ) (w : β → ℂ) :
    (∑ y : β, w y * finitePushforward u f y) = ∑ x : α, w (u x) * f x := by
  classical
  simp only [finitePushforward, Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp

variable {M : ℕ} [NeZero M]

theorem cyclicFourier_const_mul (c : ℂ) (f : ZMod M → ℂ) (k : ZMod M) :
    cyclicFourier (fun x => c * f x) k = c * cyclicFourier f k := by
  unfold cyclicFourier
  rw [ZMod.dft_const_mul]
  ring

theorem cyclicFourier_sum {κ : Type*} (S : Finset κ) (f : κ → ZMod M → ℂ) (k : ZMod M) :
    cyclicFourier (fun x => ∑ i ∈ S, f i x) k = ∑ i ∈ S, cyclicFourier (f i) k := by
  simp only [cyclicFourier_asMean, Finset.sum_mul, finiteMean_sum]

theorem cyclicFourier_push_dilate (d : ZMod M) (f : ZMod M → ℂ) (k : ZMod M) :
    cyclicFourier (finitePushforward (fun x => d * x) f) k = cyclicFourier f (d * k) := by
  unfold cyclicFourier
  rw [ZMod.dft_apply, ZMod.dft_apply]
  simp only [smul_eq_mul]
  rw [finitePushforward_weighted_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [show -(d * x * k) = -(x * (d * k)) by ring]

noncomputable def cyclicDilateAverage (J : Finset ℕ) (f : ZMod M → ℂ) (x : ZMod M) : ℂ :=
  (J.card : ℂ)⁻¹ * ∑ j ∈ J, finitePushforward (fun y => (2 * j : ZMod M) * y) f x

theorem cyclicDilateAverage_fourier (J : Finset ℕ) (f : ZMod M → ℂ) (k : ZMod M) :
    cyclicFourier (cyclicDilateAverage J f) k =
      (J.card : ℂ)⁻¹ * ∑ j ∈ J, cyclicFourier f ((2 * j : ZMod M) * k) := by
  change cyclicFourier (fun x => (J.card : ℂ)⁻¹ *
    ∑ j ∈ J, finitePushforward (fun y => (2 * j : ZMod M) * y) f x) k = _
  rw [cyclicFourier_const_mul, cyclicFourier_sum]
  simp only [cyclicFourier_push_dilate]

theorem cyclicDilateAverage_mean (J : Finset ℕ) (hJ : J.Nonempty) (f : ZMod M → ℂ) :
    finiteMean (cyclicDilateAverage J f) = finiteMean f := by
  rw [← cyclicFourier_zero, cyclicDilateAverage_fourier]
  simp only [mul_zero, cyclicFourier_zero, Finset.sum_const, nsmul_eq_mul]
  have hcard : (J.card : ℂ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hJ
  rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/BandlimitedKernel.lean -/
section
/- # A nonnegative Schwartz kernel with compact Fourier support -/

open MeasureTheory FourierTransform
open scoped SchwartzMap Convolution ComplexConjugate

namespace Erdos12Proof

noncomputable def reflectedConjugate (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  ((SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (LinearIsometryEquiv.neg ℝ).toContinuousLinearEquiv) f).postcompCLM
      Complex.conjCLE.toContinuousLinearMap

theorem reflectedConjugate_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    reflectedConjugate f x = conj (f (-x)) := rfl

theorem fourier_conjugate (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (fun x => conj (f x)) ξ = conj (𝓕 f (-ξ)) := by
  simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul, ← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  simp only [map_mul, map_neg, ← Complex.exp_conj, Complex.conj_ofReal,
    Complex.conj_I, Complex.ofReal_mul, Complex.ofReal_neg]
  congr 2
  ring

theorem fourier_reflectedConjugate (f : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    𝓕 (reflectedConjugate f) ξ = conj (𝓕 f ξ) := by
  rw [SchwartzMap.fourier_coe]
  change 𝓕 (fun x => conj (f (-x))) ξ = conj (𝓕 f ξ)
  rw [fourier_conjugate]
  change conj (𝓕 ((f : ℝ → ℂ) ∘ LinearIsometryEquiv.neg ℝ) (-ξ)) = _
  rw [Real.fourier_comp_linearIsometry]
  change conj (𝓕 (f : ℝ → ℂ) (- -ξ)) = conj (𝓕 (f : ℝ → ℂ) ξ)
  rw [neg_neg]

noncomputable def schwartzAutocorrelation (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) f (reflectedConjugate f)

noncomputable def bandlimitedKernel (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  𝓕 (schwartzAutocorrelation f)

theorem bandlimitedKernel_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    bandlimitedKernel f x = (Complex.normSq (𝓕 f x) : ℂ) := by
  unfold bandlimitedKernel schwartzAutocorrelation
  rw [SchwartzMap.fourier_convolution, SchwartzMap.pairing_apply_apply,
    ContinuousLinearMap.mul_apply', fourier_reflectedConjugate]
  exact Complex.mul_conj _

theorem bandlimitedKernel_real (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (bandlimitedKernel f x).im = 0 := by
  rw [bandlimitedKernel_apply]
  rfl

theorem bandlimitedKernel_nonneg (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    0 ≤ (bandlimitedKernel f x).re := by
  rw [bandlimitedKernel_apply, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

theorem fourier_twice_schwartz (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    𝓕 (𝓕 f) x = f (-x) := by
  have hinv : (𝓕⁻ (𝓕 f) : 𝓢(ℝ, ℂ)) = f := fourierInv_fourier_eq f
  have h := congrArg (fun g : 𝓢(ℝ, ℂ) => g (-x)) hinv
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, neg_neg] at h
  exact h

theorem fourier_bandlimitedKernel (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    𝓕 (bandlimitedKernel f) x = schwartzAutocorrelation f (-x) :=
  fourier_twice_schwartz _ _

theorem schwartzAutocorrelation_zero (f : 𝓢(ℝ, ℂ)) {a x : ℝ}
    (hf : ∀ y, a < |y| → f y = 0) (hx : 2 * a < |x|) :
    schwartzAutocorrelation f x = 0 := by
  rw [schwartzAutocorrelation, SchwartzMap.convolution_apply]
  rw [convolution_def]
  apply integral_eq_zero_of_ae
  filter_upwards with y
  change f y * conj (f (-(x - y))) = 0
  by_cases hy : a < |y|
  · rw [hf y hy, zero_mul]
  · have hxy : a < |-(x - y)| := by
      have htriangle := abs_add_le y (x - y)
      rw [add_sub_cancel] at htriangle
      rw [abs_neg]
      linarith
    rw [hf (-(x - y)) hxy, map_zero, mul_zero]

theorem bandlimitedKernel_fourier_support (f : 𝓢(ℝ, ℂ)) {a : ℝ}
    (hf : ∀ y, a < |y| → f y = 0) {ξ : ℝ} (hξ : 2 * a < |ξ|) :
    𝓕 (bandlimitedKernel f) ξ = 0 := by
  rw [fourier_bandlimitedKernel]
  exact schwartzAutocorrelation_zero f hf (by simpa only [abs_neg] using hξ)

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/BandlimitedAffine.lean -/
section
/- # Dilation and translation of band-limited Schwartz functions -/

open MeasureTheory FourierTransform
open scoped SchwartzMap

namespace Erdos12Proof

noncomputable def schwartzDilate (f : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : a ≠ 0) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (g := fun x : ℝ => a * x)
    (by fun_prop) (antilipschitzWith_mul_left ha) f

theorem schwartzDilate_apply (f : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : a ≠ 0) (x : ℝ) :
    schwartzDilate f a ha x = f (a * x) := rfl

theorem fourier_comp_mul (f : ℝ → ℂ) (a : ℝ) (ha : a ≠ 0) (ξ : ℝ) :
    𝓕 (fun x => f (a * x)) ξ = |a⁻¹| • 𝓕 f (ξ / a) := by
  simp only [Real.fourier_real_eq_integral_exp_smul]
  calc
    _ = ∫ x : ℝ, Complex.exp (↑(-2 * Real.pi * (a * x) * (ξ / a)) * Complex.I) •
        f (a * x) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [show -2 * Real.pi * (a * x) * (ξ / a) = -2 * Real.pi * x * ξ by
        field_simp]
    _ = _ := Measure.integral_comp_mul_left
      (fun y : ℝ => Complex.exp (↑(-2 * Real.pi * y * (ξ / a)) * Complex.I) • f y) a

theorem fourier_translate (f : ℝ → ℂ) (b ξ : ℝ) :
    𝓕 (fun x => f (x - b)) ξ = Real.fourierChar (-b * ξ) • 𝓕 f ξ := by
  have h := congrFun
    (Fourier.fourierIntegral_comp_add_right Real.fourierChar volume f (-b)) ξ
  simpa only [Fourier.fourierIntegral_def, Function.comp_apply, Real.fourier_real_eq,
    sub_eq_add_neg] using h

noncomputable def schwartzAffine (f : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : a ≠ 0) (b : ℝ) :
    𝓢(ℝ, ℂ) :=
  schwartzDilate (f.compSubConstCLM ℂ b) a ha

theorem schwartzAffine_apply (f : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : a ≠ 0) (b x : ℝ) :
    schwartzAffine f a ha b x = f (a * x - b) := rfl

theorem schwartzAffine_fourier (f : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : a ≠ 0) (b ξ : ℝ) :
    𝓕 (schwartzAffine f a ha b) ξ =
      |a⁻¹| • (Real.fourierChar (-b * (ξ / a)) • 𝓕 f (ξ / a)) := by
  rw [SchwartzMap.fourier_coe]
  change 𝓕 (fun x => f (a * x - b)) ξ = _
  rw [fourier_comp_mul (fun x => f (x - b)) a ha, fourier_translate]
  rfl

theorem schwartzAffine_fourier_support (f : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 0 < a)
    (b : ℝ) (hf : ∀ ξ, 1 < |ξ| → 𝓕 f ξ = 0) {ξ : ℝ} (hξ : a < |ξ|) :
    𝓕 (schwartzAffine f a ha.ne' b) ξ = 0 := by
  rw [schwartzAffine_fourier, hf, smul_zero, smul_zero]
  rw [abs_div, abs_of_pos ha]
  exact (lt_div_iff₀ ha).mpr (by simpa only [one_mul] using hξ)

theorem schwartzAffine_integral (f : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : a ≠ 0) (b : ℝ) :
    (∫ x, schwartzAffine f a ha b x) = |a⁻¹| • ∫ x, f x := by
  change (∫ x, (fun y => f (y - b)) (a * x)) = _
  rw [Measure.integral_comp_mul_left (fun y : ℝ => f (y - b)) a,
    integral_sub_right_eq_self]

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/BandlimitedBump.lean -/
section
/- # Existence of a positive band-limited Schwartz kernel -/

open MeasureTheory FourierTransform
open scoped SchwartzMap Topology ContDiff

namespace Erdos12Proof

theorem schwartz_fourier_zero (f : 𝓢(ℝ, ℂ)) :
    𝓕 f 0 = ∫ x, f x := by
  rw [SchwartzMap.fourier_coe, Real.fourier_eq]
  simp only [inner_zero_right, neg_zero, AddChar.map_zero_eq_one, one_smul]

theorem exists_positive_bandlimited_kernel :
    ∃ K : 𝓢(ℝ, ℂ),
      (∀ x, (K x).im = 0) ∧
      (∀ x, 0 ≤ (K x).re) ∧
      0 < (K 0).re ∧
      (∀ ξ, 1 < |ξ| → 𝓕 K ξ = 0) := by
  obtain ⟨φ, hsupport, hcompact, hsmooth, hrange, hzero⟩ :=
    exists_contDiff_tsupport_subset
      (n := ⊤) (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2))
  let f : 𝓢(ℝ, ℂ) :=
    (hcompact.toSchwartzMap hsmooth).postcompCLM Complex.ofRealCLM
  have hnonneg : ∀ x, 0 ≤ φ x := fun x => (hrange ⟨x, rfl⟩).1
  have hintegral : 0 < ∫ x, φ x :=
    hsmooth.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      hcompact hnonneg (by rw [hzero]; norm_num)
  have hfzero : 𝓕 f 0 ≠ 0 := by
    rw [schwartz_fourier_zero]
    change (∫ x, (φ x : ℂ)) ≠ 0
    rw [integral_complex_ofReal]
    exact_mod_cast ne_of_gt hintegral
  have hfsupport : ∀ y, (1 / 2 : ℝ) < |y| → f y = 0 := by
    intro y hy
    change (φ y : ℂ) = 0
    apply Complex.ofReal_eq_zero.mpr
    by_contra hφ
    have hmem := hsupport (subset_tsupport φ (show y ∈ Function.support φ from hφ))
    have hbound : |y| < (1 / 2 : ℝ) := by
      simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hmem
    exact (not_lt_of_ge hy.le) hbound
  refine ⟨bandlimitedKernel f, bandlimitedKernel_real f, bandlimitedKernel_nonneg f, ?_, ?_⟩
  · rw [bandlimitedKernel_apply, Complex.ofReal_re]
    exact Complex.normSq_pos.mpr hfzero
  · intro ξ hξ
    exact bandlimitedKernel_fourier_support f hfsupport (by norm_num; exact hξ)

theorem positive_schwartz_window (K : 𝓢(ℝ, ℂ)) (hK : 0 < (K 0).re) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ x, |x| ≤ r → (K 0).re / 2 ≤ (K x).re := by
  have hcont : ContinuousAt (fun x => (K x).re) 0 :=
    (Complex.continuous_re.comp K.continuous).continuousAt
  have hevent : ∀ᶠ x in 𝓝 (0 : ℝ), (K 0).re / 2 < (K x).re :=
    hcont.eventually (lt_mem_nhds (by linarith))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨min (ε / 2) 1, lt_min (half_pos hε) zero_lt_one, min_le_right _ _, ?_⟩
  intro x hx
  apply le_of_lt (hball ?_)
  rw [dist_zero_right, Real.norm_eq_abs]
  exact hx.trans_lt ((min_le_left _ _).trans_lt (half_lt_self hε))

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/IntervalMajorant.lean -/
section
/- # A band-limited majorant on a finite interval -/

open MeasureTheory FourierTransform
open scoped SchwartzMap BigOperators

namespace Erdos12Proof

theorem interval_grid_covers (r η N t : ℝ) (hr : 0 < r) (hη : 0 < η)
    (ht : 0 ≤ t) (htN : t ≤ N) :
    ∃ j ∈ Finset.range (⌊N * η / r⌋₊ + 1), |η * t - r * j| ≤ r := by
  refine ⟨⌊η * t / r⌋₊, ?_, ?_⟩
  · rw [Finset.mem_range, Nat.lt_add_one_iff]
    apply Nat.floor_le_floor
    apply div_le_div_of_nonneg_right _ hr.le
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left htN hη.le
  · have hu : 0 ≤ η * t / r := div_nonneg (mul_nonneg hη.le ht) hr.le
    have habs := Nat.abs_sub_floor_le hu
    calc
      |η * t - r * (⌊η * t / r⌋₊ : ℝ)| =
          |r * (η * t / r - (⌊η * t / r⌋₊ : ℝ))| := by
        congr 1
        field_simp
      _ = r * |η * t / r - (⌊η * t / r⌋₊ : ℝ)| := by
        rw [abs_mul, abs_of_pos hr]
      _ ≤ r * 1 := mul_le_mul_of_nonneg_left habs hr.le
      _ = r := mul_one r

noncomputable def intervalMajorant (K : 𝓢(ℝ, ℂ)) (r η : ℝ) (hη : η ≠ 0) (N : ℝ) :
    𝓢(ℝ, ℂ) :=
  (2 / (K 0).re : ℝ) •
    ∑ j ∈ Finset.range (⌊N * η / r⌋₊ + 1), schwartzAffine K η hη (r * j)

theorem intervalMajorant_re (K : 𝓢(ℝ, ℂ)) (r η : ℝ) (hη : η ≠ 0) (N t : ℝ) :
    (intervalMajorant K r η hη N t).re = (2 / (K 0).re) *
      ∑ j ∈ Finset.range (⌊N * η / r⌋₊ + 1), (K (η * t - r * j)).re := by
  simp [intervalMajorant, sum_apply, smul_apply, schwartzAffine_apply]

theorem intervalMajorant_real (K : 𝓢(ℝ, ℂ)) (r η : ℝ) (hη : η ≠ 0) (N : ℝ)
    (hK : ∀ x, (K x).im = 0) (t : ℝ) :
    (intervalMajorant K r η hη N t).im = 0 := by
  simp [intervalMajorant, sum_apply, smul_apply, schwartzAffine_apply, hK]

theorem intervalMajorant_nonneg (K : 𝓢(ℝ, ℂ)) (r η : ℝ) (hη : η ≠ 0) (N : ℝ)
    (hK : ∀ x, 0 ≤ (K x).re) (t : ℝ) :
    0 ≤ (intervalMajorant K r η hη N t).re := by
  rw [intervalMajorant_re]
  exact mul_nonneg (div_nonneg (by norm_num) (hK 0)) (Finset.sum_nonneg fun j _ => hK _)

theorem intervalMajorant_ge_one (K : 𝓢(ℝ, ℂ)) (r η N : ℝ) (hr : 0 < r) (hη : 0 < η)
    (hK : ∀ x, 0 ≤ (K x).re) (hK0 : 0 < (K 0).re)
    (hwindow : ∀ x, |x| ≤ r → (K 0).re / 2 ≤ (K x).re)
    {t : ℝ} (ht : 0 ≤ t) (htN : t ≤ N) :
    1 ≤ (intervalMajorant K r η hη.ne' N t).re := by
  obtain ⟨j, hj, hjclose⟩ := interval_grid_covers r η N t hr hη ht htN
  rw [intervalMajorant_re]
  have hsum := (hwindow _ hjclose).trans
    (Finset.single_le_sum (fun (k : ℕ) _ => hK (η * t - r * k)) hj)
  have h := mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ 2 / (K 0).re from div_nonneg (by norm_num) hK0.le)
  have hnorm : (2 / (K 0).re) * ((K 0).re / 2) = 1 := by field_simp
  rwa [hnorm] at h

theorem intervalMajorant_fourier_support (K : 𝓢(ℝ, ℂ)) (r η N : ℝ) (hη : 0 < η)
    (hK : ∀ ξ, 1 < |ξ| → 𝓕 K ξ = 0) {ξ : ℝ} (hξ : η < |ξ|) :
    𝓕 (intervalMajorant K r η hη.ne' N) ξ = 0 := by
  simp only [intervalMajorant, fourier_smul, fourier_sum, smul_apply, sum_apply]
  have hsum : ∑ j ∈ Finset.range (⌊N * η / r⌋₊ + 1),
      𝓕 (schwartzAffine K η hη.ne' (r * j)) ξ = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    exact schwartzAffine_fourier_support K η hη (r * j) hK hξ
  rw [hsum, smul_zero]

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/IntervalMajorantMass.lean -/
section
/- # The uniform integral bound for the interval majorant -/

open MeasureTheory FourierTransform
open scoped SchwartzMap BigOperators

namespace Erdos12Proof

theorem schwartzAffine_integral_re (f : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : a ≠ 0) (b : ℝ) :
    (∫ x, (schwartzAffine f a ha b x).re) = |a⁻¹| * ∫ x, (f x).re := by
  calc
    _ = (∫ x, schwartzAffine f a ha b x).re :=
      integral_re (schwartzAffine f a ha b).integrable
    _ = (|a⁻¹| • ∫ x, f x).re := congrArg Complex.re (schwartzAffine_integral f a ha b)
    _ = |a⁻¹| * (∫ x, f x).re := by rw [Complex.smul_re, smul_eq_mul]
    _ = |a⁻¹| * ∫ x, (f x).re :=
      congrArg (fun v : ℝ => |a⁻¹| * v) (integral_re f.integrable).symm

theorem intervalMajorant_integral (K : 𝓢(ℝ, ℂ)) (r η : ℝ) (hη : η ≠ 0) (N : ℝ) :
    (∫ x, (intervalMajorant K r η hη N x).re) =
      (2 / (K 0).re) * ((⌊N * η / r⌋₊ + 1 : ℕ) : ℝ) * |η⁻¹| * ∫ x, (K x).re := by
  simp_rw [intervalMajorant_re]
  rw [integral_const_mul, integral_finsetSum]
  · change (2 / (K 0).re) *
      (∑ j ∈ Finset.range (⌊N * η / r⌋₊ + 1),
        ∫ x, (schwartzAffine K η hη (r * j) x).re) = _
    simp_rw [schwartzAffine_integral_re]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  · intro j _
    exact (schwartzAffine K η hη (r * j)).integrable.re

theorem intervalMajorant_integral_bound (K : 𝓢(ℝ, ℂ)) (r η N : ℝ)
    (hr : 0 < r) (hη : 0 < η) (hN : 0 ≤ N) (hK : ∀ x, 0 ≤ (K x).re) :
    (∫ x, (intervalMajorant K r η hη.ne' N x).re) ≤
      ((2 / (K 0).re) * (∫ x, (K x).re) * (r⁻¹ + 1) + 1) * (N + η⁻¹) := by
  have hI : 0 ≤ ∫ x, (K x).re := integral_nonneg hK
  have hc : 0 ≤ 2 / (K 0).re := div_nonneg (by norm_num) (hK 0)
  have hfloor := Nat.floor_le (div_nonneg (mul_nonneg hN hη.le) hr.le)
  have hmass :
      (∫ x, (intervalMajorant K r η hη.ne' N x).re) ≤
        (2 / (K 0).re) * (∫ x, (K x).re) * (N / r + η⁻¹) := by
    rw [intervalMajorant_integral, abs_of_pos (inv_pos.mpr hη)]
    calc
      _ ≤ (2 / (K 0).re) * (N * η / r + 1) * η⁻¹ * ∫ x, (K x).re := by
        gcongr
        simp only [Nat.cast_add, Nat.cast_one]
        linarith
      _ = _ := by field_simp
  have hfactor : N / r + η⁻¹ ≤ (r⁻¹ + 1) * (N + η⁻¹) := by
    have hcross : 0 ≤ r⁻¹ * η⁻¹ := mul_nonneg (inv_nonneg.mpr hr.le) (inv_nonneg.mpr hη.le)
    rw [div_eq_mul_inv]
    nlinarith
  calc
    _ ≤ (2 / (K 0).re) * (∫ x, (K x).re) * (N / r + η⁻¹) := hmass
    _ ≤ (2 / (K 0).re) * (∫ x, (K x).re) * ((r⁻¹ + 1) * (N + η⁻¹)) :=
      mul_le_mul_of_nonneg_left hfactor (mul_nonneg hc hI)
    _ ≤ _ := by
      have : 0 ≤ N + η⁻¹ := add_nonneg hN (inv_nonneg.mpr hη.le)
      nlinarith

theorem exists_interval_majorant :
    ∃ C : ℝ, 0 < C ∧ ∀ N η : ℝ, 0 ≤ N → 0 < η →
      ∃ ψ : 𝓢(ℝ, ℂ),
        (∀ x, (ψ x).im = 0) ∧
        (∀ x, 0 ≤ (ψ x).re) ∧
        (∀ x, 0 ≤ x → x ≤ N → 1 ≤ (ψ x).re) ∧
        (∀ ξ, η < |ξ| → 𝓕 ψ ξ = 0) ∧
        (∫ x, (ψ x).re) ≤ C * (N + η⁻¹) := by
  obtain ⟨K, hreal, hnonneg, hzero, hsupport⟩ := exists_positive_bandlimited_kernel
  obtain ⟨r, hr, _, hwindow⟩ := positive_schwartz_window K hzero
  refine ⟨(2 / (K 0).re) * (∫ x, (K x).re) * (r⁻¹ + 1) + 1, ?_, ?_⟩
  · have hI : 0 ≤ ∫ x, (K x).re := integral_nonneg hnonneg
    positivity
  · intro N η hN hη
    refine ⟨intervalMajorant K r η hη.ne' N,
      intervalMajorant_real K r η hη.ne' N hreal,
      intervalMajorant_nonneg K r η hη.ne' N hnonneg,
      ?_, (fun ξ hξ => intervalMajorant_fourier_support K r η N hη hsupport hξ), ?_⟩
    · intro x hx hxN
      exact intervalMajorant_ge_one K r η N hr hη hnonneg hzero hwindow hx hxN
    · exact intervalMajorant_integral_bound K r η N hr hη hN hnonneg

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/BandlimitedPoisson.lean -/
section
/- # Poisson summation for the band-limited majorant -/

open MeasureTheory FourierTransform
open scoped SchwartzMap

namespace Erdos12Proof

noncomputable def schwartzModulate (f : 𝓢(ℝ, ℂ)) (a : ℝ) : 𝓢(ℝ, ℂ) :=
  𝓕⁻ ((𝓕 f).compSubConstCLM ℂ a)

theorem schwartzModulate_fourier (f : 𝓢(ℝ, ℂ)) (a ξ : ℝ) :
    𝓕 (schwartzModulate f a) ξ = 𝓕 f (ξ - a) := by
  simp [schwartzModulate]

theorem schwartzModulate_apply (f : 𝓢(ℝ, ℂ)) (a x : ℝ) :
    schwartzModulate f a x = Real.fourierChar (a * x) • f x := by
  rw [schwartzModulate, SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg]
  change 𝓕 (fun y => 𝓕 f (y - a)) (-x) = _
  rw [fourier_translate]
  have hdouble : 𝓕 (fun y => 𝓕 f y) (-x) = f x := by
    rw [← SchwartzMap.fourier_coe, fourier_twice_schwartz, neg_neg]
  rw [hdouble]
  congr 2
  ring

theorem schwartz_twisted_poisson (f : 𝓢(ℝ, ℂ)) (a : ℝ) :
    (∑' n : ℤ, (Real.fourierChar (a * n) : ℂ) * f n) =
      ∑' m : ℤ, 𝓕 f (m - a) := by
  have h := (schwartzModulate f a).tsum_eq_tsum_fourier 0
  simpa [schwartzModulate_apply, Circle.smul_def, schwartzModulate_fourier] using h

theorem norm_eq_re_of_real_nonneg (z : ℂ) (hz : z.im = 0) (hpos : 0 ≤ z.re) :
    ‖z‖ = z.re := by
  have hreal : z = (z.re : ℂ) := Complex.ext rfl hz
  exact (congrArg norm hreal).trans (Complex.norm_of_nonneg hpos)

theorem nonnegative_schwartz_fourier_bound (f : 𝓢(ℝ, ℂ))
    (hreal : ∀ x, (f x).im = 0) (hpos : ∀ x, 0 ≤ (f x).re) (ξ : ℝ) :
    ‖𝓕 f ξ‖ ≤ ∫ x, (f x).re := by
  rw [SchwartzMap.fourier_coe, Real.fourier_eq]
  calc
    _ ≤ ∫ x, ‖Real.fourierChar (-inner ℝ x ξ) • f x‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ x, (f x).re := by
      apply integral_congr_ae
      filter_upwards with x
      rw [Circle.norm_smul, norm_eq_re_of_real_nonneg (f x) (hreal x) (hpos x)]

theorem integer_away_from_round (a : ℝ) {m : ℤ} (hm : m ≠ round a) :
    (1 / 2 : ℝ) ≤ |m - a| := by
  by_contra h
  have habs := abs_lt.mp (lt_of_not_ge h)
  apply hm
  symm
  apply round_eq_iff.mpr
  exact ⟨by linarith [habs.2], by linarith [habs.1]⟩

theorem bandlimited_poisson_single (f : 𝓢(ℝ, ℂ)) (a η : ℝ) (hη : η < 1 / 2)
    (hsupport : ∀ ξ, η < |ξ| → 𝓕 f ξ = 0) :
    (∑' n : ℤ, (Real.fourierChar (a * n) : ℂ) * f n) =
      𝓕 f ((round a : ℤ) - a) := by
  rw [schwartz_twisted_poisson]
  apply tsum_eq_single (round a)
  intro m hm
  exact hsupport _ (hη.trans_le (integer_away_from_round a hm))

theorem bandlimited_poisson_bound (f : 𝓢(ℝ, ℂ)) (a η : ℝ) (hη : η < 1 / 2)
    (hsupport : ∀ ξ, η < |ξ| → 𝓕 f ξ = 0)
    (hreal : ∀ x, (f x).im = 0) (hpos : ∀ x, 0 ≤ (f x).re) :
    ‖∑' n : ℤ, (Real.fourierChar (a * n) : ℂ) * f n‖ ≤ ∫ x, (f x).re := by
  rw [bandlimited_poisson_single f a η hη hsupport]
  exact nonnegative_schwartz_fourier_bound f hreal hpos _

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/IntegerFourier.lean -/
section
/- # Integer Fourier sums of Schwartz majorants -/

open MeasureTheory FourierTransform
open scoped SchwartzMap

namespace Erdos12Proof

theorem unitExp_eq_fourierChar (t : ℝ) : unitExp t = (Real.fourierChar t : ℂ) := by
  unfold unitExp
  rw [Real.fourierChar_apply]
  congr 1
  push_cast
  ring

theorem schwartz_summable_int (f : 𝓢(ℝ, ℂ)) : Summable (fun n : ℤ => f n) := by
  exact summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2))
    ((f.isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)

theorem schwartz_twist_summable (f : 𝓢(ℝ, ℂ)) (a : ℝ) :
    Summable (fun n : ℤ => unitExp (a * n) * f n) := by
  have h := schwartz_summable_int (schwartzModulate f a)
  simpa only [schwartzModulate_apply, unitExp_eq_fourierChar, Circle.smul_def,
    smul_eq_mul] using h

noncomputable def integerFourierSum (f : 𝓢(ℝ, ℂ)) (a : ℝ) : ℂ :=
  ∑' n : ℤ, unitExp (a * n) * f n

theorem integerFourierSum_poisson (f : 𝓢(ℝ, ℂ)) (a η : ℝ) (hη : η < 1 / 2)
    (hsupport : ∀ ξ, η < |ξ| → 𝓕 f ξ = 0) :
    integerFourierSum f a = 𝓕 f ((round a : ℤ) - a) := by
  simpa only [integerFourierSum, unitExp_eq_fourierChar] using
    bandlimited_poisson_single f a η hη hsupport

theorem integerFourierSum_bound (f : 𝓢(ℝ, ℂ)) (a η : ℝ) (hη : η < 1 / 2)
    (hsupport : ∀ ξ, η < |ξ| → 𝓕 f ξ = 0)
    (hreal : ∀ x, (f x).im = 0) (hpos : ∀ x, 0 ≤ (f x).re) :
    ‖integerFourierSum f a‖ ≤ ∫ x, (f x).re := by
  simpa only [integerFourierSum, unitExp_eq_fourierChar] using
    bandlimited_poisson_bound f a η hη hsupport hreal hpos

theorem integerFourierSum_zero (f : 𝓢(ℝ, ℂ)) (η : ℝ) (hη : η < 1 / 2)
    (hsupport : ∀ ξ, η < |ξ| → 𝓕 f ξ = 0) :
    integerFourierSum f 0 = ∫ x, f x := by
  rw [integerFourierSum_poisson f 0 η hη hsupport]
  simpa only [round_zero, Int.cast_zero, sub_zero] using schwartz_fourier_zero f

theorem integerFourierSum_vanish (f : 𝓢(ℝ, ℂ)) (a η : ℝ) (hη : η < 1 / 2)
    (hsupport : ∀ ξ, η < |ξ| → 𝓕 f ξ = 0) (ha : η < ‖(a : UnitAddCircle)‖) :
    integerFourierSum f a = 0 := by
  rw [integerFourierSum_poisson f a η hη hsupport]
  apply hsupport
  rw [UnitAddCircle.norm_eq, abs_sub_comm] at ha
  exact ha

theorem integerFourierSum_finite_expansion {κ : Type*} (S : Finset κ)
    (c : κ → ℂ) (r : κ → ℝ) (f : 𝓢(ℝ, ℂ)) (a : ℝ) :
    (∑' n : ℤ, (∑ k ∈ S, c k * unitExp (n * r k)) * unitExp (a * n) * f n) =
      ∑ k ∈ S, c k * integerFourierSum f (a + r k) := by
  have hpoint (n : ℤ) :
      (∑ k ∈ S, c k * unitExp (n * r k)) * unitExp (a * n) * f n =
        ∑ k ∈ S, c k * (unitExp ((a + r k) * n) * f n) := by
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [add_mul, unitExp_add, mul_comm (r k) (n : ℝ)]
    ring
  simp_rw [hpoint]
  rw [Summable.tsum_finsetSum (fun k _ => (schwartz_twist_summable f (a + r k)).mul_left (c k))]
  simp only [tsum_mul_left, integerFourierSum]

end Erdos12Proof
end

/- BEGIN SOURCE: AnalyticNumberTheory/LargeSieve/GeomSum.lean -/
section
/- # AnalyticNumberTheory.LargeSieve.GeomSum

## Geometric-sum bound

The first analytic step in Montgomery's additive large-sieve argument:
for `e(x) = exp(2πix)` and `‖x‖`, the distance to the nearest integer
(expressed using `Int.fract`), the bound for nonintegral `x` is

  |Σ_{n<N} e(nx)| ≤ min(N, 1/(2‖x‖)).

This module proves the trivial bound `≤ N` for every `x` (each summand has
norm 1) and the nontrivial bound `≤ 1/(2‖x‖)` for nonintegral `x`, using
the geometric-series formula, `|e(x)−1| = 2|sin(πx)|`, and
`|sin(πt)| ≥ 2·min(t,1−t)` for `t ∈ [0,1]`.

References: Iwaniec--Kowalski, "Analytic Number Theory" (2004), Ch. 7 Lemma 7.6;
Davenport, "Multiplicative Number Theory", Ch. 27.
-/

namespace AnalyticNumberTheory.LargeSieve

open scoped BigOperators

noncomputable section

/- ## 1. Distance to the nearest integer -/

/-- The fractional part `x − ⌊x⌋ ∈ [0,1)` is nonnegative. -/
theorem fract_nonneg (x : ℝ) : 0 ≤ Int.fract x :=
  Int.fract_nonneg x

/-- The fractional part is less than 1. -/
theorem fract_lt_one (x : ℝ) : Int.fract x < 1 :=
  Int.fract_lt_one x

/-- Distance to the nearest integer:
`‖x‖ = min(x − ⌊x⌋, 1 − (x − ⌊x⌋))`. -/
noncomputable def distToInt (x : ℝ) : ℝ := min (Int.fract x) (1 - Int.fract x)


theorem distToInt_le_half (x : ℝ) : distToInt x ≤ 1 / 2 := by
  dsimp [distToInt]
  by_cases h : Int.fract x ≤ 1 / 2
  · exact le_trans (min_le_left _ _) h
  · have h' : 1 - Int.fract x ≤ 1 / 2 := by linarith
    exact le_trans (min_le_right _ _) h'

/- ## 2. Additive characters and geometric series -/

/-- `e(x) = exp(2πix)`: the additive character parametrized by `ℝ`. -/
noncomputable def charReal (x : ℝ) : ℂ :=
  Complex.exp ((2 * Real.pi * (x : ℂ)) * Complex.I)

/-- The additive character has unit norm. -/
private lemma norm_charReal (x : ℝ) : ‖charReal x‖ = 1 := by
  dsimp [charReal]
  simpa using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)

/-- `e(nx) = e(x)^n` (`n : ℕ`), by `Complex.exp_nsmul`. -/
theorem charReal_nat_mul (n : ℕ) (x : ℝ) : charReal (n * x) = (charReal x) ^ n := by
  dsimp [charReal]
  rw [show (2 * Real.pi * ((n * x : ℝ) : ℂ)) * Complex.I =
      n • ((2 * Real.pi * (x : ℂ)) * Complex.I) by
        rw [nsmul_eq_mul]
        norm_num [Complex.ofReal_mul]
        ring]
  rw [Complex.exp_nsmul]


/-- `e(a + b) = e(a)·e(b)`: the character maps addition in `ℝ`
to multiplication in `ℂ`. -/
theorem charReal_add (a b : ℝ) : charReal (a + b) = charReal a * charReal b := by
  dsimp [charReal]
  rw [show (2 * Real.pi * ((a + b : ℝ) : ℂ)) * Complex.I =
      (2 * Real.pi * (a : ℂ)) * Complex.I + (2 * Real.pi * (b : ℂ)) * Complex.I by
        rw [Complex.ofReal_add]
        ring]
  rw [Complex.exp_add]

/-- Rearrangement of the argument: `(2π·c)·I = c·(2π·I)`, a polynomial
identity for every complex `c` (in particular, for every real `c`). -/
theorem mul_charReal_arg (c : ℂ) :
    (2 * Real.pi * c) * Complex.I = c * (2 * Real.pi * Complex.I) := by
  ring

/-- The character depends only on the class modulo 1: `e(x) = e(fract x)`. -/
theorem charReal_eq_charReal_fract (x : ℝ) : charReal x = charReal (Int.fract x) := by
  have hx : x = Int.fract x + (⌊x⌋ : ℝ) := (Int.fract_add_floor x).symm
  conv_lhs => rw [hx]
  rw [charReal_add]
  have he : charReal ((⌊x⌋ : ℝ)) = 1 := by
    dsimp [charReal]
    rw [show (2 * Real.pi * (⌊x⌋ : ℂ)) * Complex.I =
        (⌊x⌋ : ℂ) * (2 * Real.pi * Complex.I) by
          exact mul_charReal_arg (⌊x⌋ : ℂ)]
    rw [Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]
  rw [he, mul_one]

/-- Geometric-series identity:
`Σ_{n<N} e(nx) = (e(Nx)−1)/(e(x)−1)` when `e(x) ≠ 1`. -/
theorem geomSum_exp_eq_geomSeries (N : ℕ) {x : ℝ} (hz : charReal x ≠ 1) :
    (∑ n ∈ Finset.range N, charReal (n * x)) = (charReal (N * x) - 1) / (charReal x - 1) := by
  rw [Finset.sum_congr rfl (fun n hn => charReal_nat_mul n x)]
  rw [charReal_nat_mul N x]
  exact geom_sum_eq hz N

/-- **Trivial bound**: `|Σ_{n<N} e(nx)| ≤ N`, since every term has norm 1. -/
theorem geomSum_exp_bound_trivial (N : ℕ) (x : ℝ) :
    ‖∑ n ∈ Finset.range N, charReal (n * x)‖ ≤ N := by
  calc
    ‖∑ n ∈ Finset.range N, charReal (n * x)‖ ≤ ∑ n ∈ Finset.range N, ‖charReal (n * x)‖ :=
      norm_sum_le _ _
    _ = N := by simp only [norm_charReal, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

/- ## 3. Trigonometric identities -/

/-- `|e(x) − 1| = 2|sin(πx)|`, combining `e(x) = exp(πix)²` and
`exp(πix) − exp(−πix) = 2i·sin(πx)`. -/
theorem abs_charReal_sub_one (x : ℝ) :
    ‖charReal x - 1‖ = 2 * |Real.sin (Real.pi * x)| := by
  have h1 : charReal x = (Complex.exp (Real.pi * (x : ℂ) * Complex.I)) ^ 2 := by
    dsimp [charReal]
    rw [pow_two, ← Complex.exp_add]
    congr 1
    ring
  have h2 : (1 : ℂ) = Complex.exp (Real.pi * (x : ℂ) * Complex.I) *
      Complex.exp (-(Real.pi * (x : ℂ) * Complex.I)) := by
    rw [← Complex.exp_add]
    simp
  have hsq : charReal x - 1 = Complex.exp (Real.pi * (x : ℂ) * Complex.I) *
      (Complex.exp (Real.pi * (x : ℂ) * Complex.I) -
        Complex.exp (-(Real.pi * (x : ℂ) * Complex.I))) := by
    rw [h1, h2]
    ring
  have hsub : Complex.exp (Real.pi * (x : ℂ) * Complex.I) -
      Complex.exp (-(Real.pi * (x : ℂ) * Complex.I)) =
      2 * Complex.I * Complex.sin (Real.pi * (x : ℂ)) := by
    rw [Complex.exp_mul_I]
    rw [show -(Real.pi * (x : ℂ) * Complex.I) = -(Real.pi * (x : ℂ)) * Complex.I by ring]
    rw [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    ring
  calc
    ‖charReal x - 1‖ = ‖Complex.exp (Real.pi * (x : ℂ) * Complex.I) *
        (Complex.exp (Real.pi * (x : ℂ) * Complex.I) -
          Complex.exp (-(Real.pi * (x : ℂ) * Complex.I)))‖ := by rw [hsq]
    _ = ‖Complex.exp (Real.pi * (x : ℂ) * Complex.I)‖ *
          ‖Complex.exp (Real.pi * (x : ℂ) * Complex.I) -
            Complex.exp (-(Real.pi * (x : ℂ) * Complex.I))‖ := by rw [norm_mul]
    _ = 1 * ‖2 * Complex.I * Complex.sin (Real.pi * (x : ℂ))‖ := by
          rw [hsub]
          congr 1
          simpa using Complex.norm_exp_ofReal_mul_I (Real.pi * x)
    _ = 2 * |Real.sin (Real.pi * x)| := by
          have hsin : Complex.sin (Real.pi * (x : ℂ)) = (Real.sin (Real.pi * x) : ℂ) := by
            have harg : Real.pi * (x : ℂ) = ((Real.pi * x : ℝ) : ℂ) := by
              rw [Complex.ofReal_mul]
            rw [harg, ← Complex.ofReal_sin]
          rw [norm_mul, norm_mul, Complex.norm_I, hsin, Complex.norm_real]
          norm_num

/-- `|sin(πt)| ≥ 2·min(t, 1−t)` for `t ∈ [0,1]`: use
`sin(πt) ≥ 2t` on `[0,1/2]`, and reflection
`sin(πt) = sin(π(1−t))` on `[1/2,1]`. -/
theorem abs_sin_pi_mul_ge_two_min (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    2 * min t (1 - t) ≤ |Real.sin (Real.pi * t)| := by
  -- Prove the chord bound on the first half, then reflect the second half.
  have hsmall (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
      2 * u ≤ Real.sin (Real.pi * u) := by
    have hangle0 : 0 ≤ Real.pi * u := mul_nonneg Real.pi_pos.le hu0
    have hangle1 : Real.pi * u ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
    have hsin := Real.mul_le_sin hangle0 hangle1
    field_simp [Real.pi_ne_zero] at hsin ⊢
    exact hsin
  by_cases ht : t ≤ 1 / 2
  · rw [min_eq_left (by linarith : t ≤ 1 - t)]
    exact (hsmall t ht0 ht).trans (le_abs_self _)
  · rw [min_eq_right (by linarith : 1 - t ≤ t)]
    have hreflect : Real.sin (Real.pi * t) = Real.sin (Real.pi * (1 - t)) := by
      rw [show Real.pi * t = Real.pi - Real.pi * (1 - t) by ring, Real.sin_pi_sub]
    rw [hreflect]
    exact (hsmall (1 - t) (sub_nonneg.mpr ht1) (by linarith)).trans (le_abs_self _)

/- ## 4. Nontrivial bound -/

/-- `e(x) ≠ 1` for `x ∉ ℤ`, since
`|e(x)−1| = 2|sin(π·fract x)| > 0`. -/
theorem charReal_ne_one_of_not_int {x : ℝ} (hx : ¬ ∃ k : ℤ, (k : ℝ) = x) :
    charReal x ≠ 1 := by
  have hx' : Int.fract x ≠ 0 := Int.fract_ne_zero_iff.mpr hx
  have hpos : 0 < ‖charReal x - 1‖ := by
    rw [charReal_eq_charReal_fract, abs_charReal_sub_one]
    have ht0 : 0 < Int.fract x := lt_of_le_of_ne (fract_nonneg x) (Ne.symm hx')
    have hs : 0 < Real.sin (Real.pi * Int.fract x) :=
      Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos ht0)
        (by nlinarith [fract_lt_one x, Real.pi_pos])
    have hsinabs : 0 < |Real.sin (Real.pi * Int.fract x)| := abs_pos.mpr (ne_of_gt hs)
    nlinarith [hsinabs]
  intro h
  have hzero : ‖charReal x - 1‖ = 0 := by simp [h]
  exact (ne_of_gt hpos) hzero

/-- **Geometric-sum bound (nontrivial part)**: for `x ∉ ℤ`,
  |Σ_{n<N} e(nx)| ≤ 1/(2‖x‖).
Combine the geometric-series formula, `|e(x)−1| = 2|sin(π·fract x)|`,
and `|sin(πt)| ≥ 2·min(t,1−t)`. -/
theorem geomSum_exp_bound_far (N : ℕ) {x : ℝ} (hx : ¬ ∃ k : ℤ, (k : ℝ) = x) :
    ‖∑ n ∈ Finset.range N, charReal (n * x)‖ ≤ 1 / (2 * distToInt x) := by
  have hz : charReal x ≠ 1 := charReal_ne_one_of_not_int hx
  have hx' : Int.fract x ≠ 0 := Int.fract_ne_zero_iff.mpr hx
  have hd : 0 < 2 * distToInt x := by
    have hd0 : 0 < distToInt x := by
      dsimp [distToInt]
      exact lt_min (lt_of_le_of_ne (fract_nonneg x) (Ne.symm hx'))
        (by linarith [fract_lt_one x])
    nlinarith
  have hsin : 2 * distToInt x ≤ |Real.sin (Real.pi * Int.fract x)| := by
    dsimp [distToInt]
    exact abs_sin_pi_mul_ge_two_min (Int.fract x) (fract_nonneg x) (le_of_lt (fract_lt_one x))
  have hs : 0 < |Real.sin (Real.pi * Int.fract x)| := hd.trans_le hsin
  calc
    ‖∑ n ∈ Finset.range N, charReal (n * x)‖
        = ‖(charReal (N * x) - 1) / (charReal x - 1)‖ := by
          rw [geomSum_exp_eq_geomSeries N hz]
    _ = ‖charReal (N * x) - 1‖ / ‖charReal x - 1‖ := by rw [norm_div]
    _ ≤ 2 / ‖charReal x - 1‖ := by
          have htop : ‖charReal (N * x) - 1‖ ≤ 2 := by
            simpa only [norm_charReal, norm_one, one_add_one_eq_two] using
              norm_sub_le (charReal (N * x)) (1 : ℂ)
          exact div_le_div_of_nonneg_right htop (norm_nonneg _)
    _ = 1 / |Real.sin (Real.pi * Int.fract x)| := by
          have hz1' : ‖charReal x - 1‖ = 2 * |Real.sin (Real.pi * Int.fract x)| := by
            rw [charReal_eq_charReal_fract x, abs_charReal_sub_one]
          rw [hz1']
          field_simp [hs]
    _ ≤ 1 / (2 * distToInt x) := by
          exact one_div_le_one_div_of_le hd hsin


/- ## 5. Interval geometric-sum bound -/

/-- The character at a negative argument: `e(−x) = star(e(x))`,
by `exp(conj z) = conj(exp z)`. -/
theorem charReal_neg (x : ℝ) : charReal (-x) = star (charReal x) := by
  dsimp [charReal]
  rw [show (2 * Real.pi * ((-x : ℝ) : ℂ)) * Complex.I =
      -((2 * Real.pi * (x : ℂ)) * Complex.I) by
        rw [Complex.ofReal_neg]
        ring]
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul (starRingEnd ℂ)]
  rw [map_mul (starRingEnd ℂ)]
  rw [map_mul (starRingEnd ℂ)]
  rw [Complex.conj_ofNat]
  rw [Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- Character identity: `e(a − b) = e(a)·star(e(b))`,
using the homomorphism property and conjugation. -/
theorem charReal_sub (a b : ℝ) : charReal (a - b) = charReal a * star (charReal b) := by
  rw [sub_eq_add_neg, charReal_add, charReal_neg]

/-- The exponential sum `Σ_{M<n≤M+N} e(nx)` over the shifted interval
`(M, M+N]` (`n : ℤ`). -/
noncomputable def charRealSubIcc (M : ℤ) (N : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc (M + 1) (M + N), charReal ((n : ℝ) * x)

lemma charRealSubIcc_succ (M : ℤ) (N : ℕ) (x : ℝ) :
    charRealSubIcc M (N + 1) x =
      charRealSubIcc M N x + charReal (((M + N + 1 : ℤ) : ℝ) * x) := by
  dsimp [charRealSubIcc]
  have hIcc : Finset.Icc (M + 1) (M + (N + 1) : ℤ) =
      insert (M + N + 1) (Finset.Icc (M + 1) (M + N)) := by
    ext n
    simp [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hmem : M + N + 1 ∉ Finset.Icc (M + 1) (M + N) := by
    rw [Finset.mem_Icc]
    omega
  rw [hIcc, Finset.sum_insert hmem]
  simp [add_comm]

/-- **Interval exponential-sum factorization**:
`Σ_{M<n≤M+N} e(nx) = e((M+1)x)·Σ_{k<N} e(kx)`. -/
theorem charRealSubIcc_eq_shift (M : ℤ) (N : ℕ) (x : ℝ) :
    charRealSubIcc M N x =
      charReal (((M + 1 : ℤ) : ℝ) * x) * ∑ k ∈ Finset.range N, charReal ((k : ℝ) * x) := by
  induction N with
  | zero =>
      dsimp [charRealSubIcc]
      simp
  | succ N ih =>
      rw [charRealSubIcc_succ, ih]
      rw [Finset.sum_range_succ]
      have htop : charReal (((M + N + 1 : ℤ) : ℝ) * x) =
          charReal (((M + 1 : ℤ) : ℝ) * x) * charReal ((N : ℝ) * x) := by
        have hz : (((M + N + 1 : ℤ) : ℝ) * x) =
            (((M + 1 : ℤ) : ℝ) * x) + ((N : ℝ) * x) := by
          have hzℤ : (M + N + 1 : ℤ) = (M + 1) + (N : ℤ) := by omega
          rw [hzℤ]
          push_cast
          ring
        rw [hz, charReal_add]
      rw [htop]
      ring

/-- **Interval exponential sum (trivial bound)**:
`|Σ_{M<n≤M+N} e(nx)| ≤ N`. -/
theorem geomSum_exp_bound_Icc_trivial (M : ℤ) (N : ℕ) (x : ℝ) :
    ‖charRealSubIcc M N x‖ ≤ N := by
  rw [charRealSubIcc_eq_shift, norm_mul, norm_charReal, one_mul]
  exact geomSum_exp_bound_trivial N x

/-- **Interval exponential sum (nontrivial bound)**: for `x ∉ ℤ`,
  `|Σ_{M<n≤M+N} e(nx)| ≤ 1/(2‖x‖)`. -/
theorem geomSum_exp_bound_Icc_far (M : ℤ) (N : ℕ) {x : ℝ}
    (hx : ¬ ∃ k : ℤ, (k : ℝ) = x) :
    ‖charRealSubIcc M N x‖ ≤ 1 / (2 * distToInt x) := by
  rw [charRealSubIcc_eq_shift, norm_mul, norm_charReal, one_mul]
  exact geomSum_exp_bound_far N hx

/-- **Interval geometric-sum bound**: the two components of
`|Σ_{M<n≤M+N} e(nx)| ≤ min(N, 1/(2‖x‖))`, with the nontrivial
component conditional on `x ∉ ℤ`. -/
theorem geomSum_exp_bound_Icc (M : ℤ) (N : ℕ) (x : ℝ) :
    ‖charRealSubIcc M N x‖ ≤ N ∧
      ((¬ ∃ k : ℤ, (k : ℝ) = x) →
        ‖charRealSubIcc M N x‖ ≤ 1 / (2 * distToInt x)) := by
  constructor
  · exact geomSum_exp_bound_Icc_trivial M N x
  · intro hx
    exact geomSum_exp_bound_Icc_far M N hx

end

end AnalyticNumberTheory.LargeSieve
end

/- BEGIN SOURCE: Erdos12/ExponentialSums.lean -/
section
/- # Geometric sums and phase variation in the rough-block comparison -/

namespace Erdos12Proof

theorem unitExp_norm (t : ℝ) : ‖unitExp t‖ = 1 := by
  simp [unitExp_eq_fourierChar]

theorem unitExp_eq_charReal (t : ℝ) : unitExp t = AnalyticNumberTheory.LargeSieve.charReal t := by
  unfold unitExp AnalyticNumberTheory.LargeSieve.charReal
  congr 1
  ring

theorem unitExp_sub_one_bound (t : ℝ) : ‖unitExp t - 1‖ ≤ 2 * Real.pi * |t| := by
  have hexp : unitExp t = Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ)) := by
    unfold unitExp
    push_cast
    congr 1
    ring
  rw [hexp]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * t)
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos,
    abs_of_pos (show (0 : ℝ) < 2 by norm_num)] using h

theorem unitExp_difference_bound (s t : ℝ) : ‖unitExp s - unitExp t‖ ≤ 2 * Real.pi * |s - t| := by
  have hfactor : unitExp s - unitExp t = unitExp t * (unitExp (s - t) - 1) := by
    have hs : s = t + (s - t) := by ring
    conv_lhs => rw [hs, unitExp_add]
    ring
  rw [hfactor, norm_mul, unitExp_norm, one_mul]
  exact unitExp_sub_one_bound _

theorem distToInt_eq_circle_norm (t : ℝ) :
    AnalyticNumberTheory.LargeSieve.distToInt t = ‖(t : UnitAddCircle)‖ := by
  rw [UnitAddCircle.norm_eq, abs_sub_round_eq_min]
  rfl

noncomputable def exponentialSumInterval (a : ℤ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc (a + 1) (a + N), unitExp ((n : ℝ) * t)

theorem exponentialSumInterval_trivial (a : ℤ) (N : ℕ) (t : ℝ) :
    ‖exponentialSumInterval a N t‖ ≤ N := by
  simpa only [exponentialSumInterval, AnalyticNumberTheory.LargeSieve.charRealSubIcc,
    ← unitExp_eq_charReal] using AnalyticNumberTheory.LargeSieve.geomSum_exp_bound_Icc_trivial a N t

theorem exponentialSumInterval_far (a : ℤ) (N : ℕ) (t : ℝ) (ht : 0 < ‖(t : UnitAddCircle)‖) :
    ‖exponentialSumInterval a N t‖ ≤ 1 / (2 * ‖(t : UnitAddCircle)‖) := by
  have hnot : ¬∃ n : ℤ, (n : ℝ) = t := by
    rintro ⟨n, hn⟩
    have hdist : 0 < AnalyticNumberTheory.LargeSieve.distToInt t := by
      simpa only [distToInt_eq_circle_norm] using ht
    rw [← hn] at hdist
    simp [AnalyticNumberTheory.LargeSieve.distToInt] at hdist
  simpa only [exponentialSumInterval, AnalyticNumberTheory.LargeSieve.charRealSubIcc,
    ← unitExp_eq_charReal, distToInt_eq_circle_norm] using
      AnalyticNumberTheory.LargeSieve.geomSum_exp_bound_Icc_far a N hnot

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/RationalOrbitSpacing.lean -/
section
/- # Separation of a perturbed rational orbit on the circle -/

namespace Erdos12Proof

theorem circle_norm_nat_fraction {a d : ℕ} (hd : 0 < d) (hnot : ¬d ∣ a) :
    1 / (d : ℝ) ≤ ‖(((a : ℝ) / d : ℝ) : UnitAddCircle)‖ := by
  have hmod : 0 < a % d := Nat.pos_of_ne_zero (fun h => hnot (Nat.dvd_of_mod_eq_zero h))
  have hmodlt := Nat.mod_lt a hd
  have hmin : 1 ≤ min (a % d) (d - a % d) := by omega
  have hnorm := AddCircle.norm_div_natCast (p := 1) (m := a) (n := d)
  simp only [mul_one, one_mul] at hnorm
  rw [hnorm]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg d)
  exact_mod_cast hmin

theorem circle_norm_perturbation (x y : ℝ) :
    ‖(x : UnitAddCircle)‖ ≤ ‖((x + y : ℝ) : UnitAddCircle)‖ + |y| := by
  have hy : ‖(y : UnitAddCircle)‖ ≤ |y| := by
    have h : ‖(y : UnitAddCircle)‖ ≤ ‖y‖ := QuotientAddGroup.norm_mk_le_norm
    simpa only [Real.norm_eq_abs] using h
  calc
    _ = ‖((x + y : ℝ) : UnitAddCircle) - (y : UnitAddCircle)‖ := by
      rw [← AddCircle.coe_sub]
      congr 1
      ring
    _ ≤ ‖((x + y : ℝ) : UnitAddCircle)‖ + ‖(y : UnitAddCircle)‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add_right hy _

theorem coprime_rational_orbit_spacing {r d h : ℕ} (hd : 0 < d) (hrd : r.Coprime d)
    (hh : 0 < h) (hhd : h < d) {β : ℝ} (hβ : |β| ≤ 1 / (2 * (d : ℝ) ^ 2)) :
    1 / (2 * (d : ℝ)) ≤ ‖(((h : ℝ) * ((r : ℝ) / d + β) : ℝ) : UnitAddCircle)‖ := by
  have hnot : ¬d ∣ h * r := by
    intro hdiv
    have hdh := hrd.symm.dvd_of_dvd_mul_right hdiv
    exact (Nat.not_dvd_of_pos_of_lt hh hhd) hdh
  have hbase := circle_norm_nat_fraction hd hnot
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have herror : |(h : ℝ) * β| ≤ 1 / (2 * (d : ℝ)) := by
    calc
      _ = (h : ℝ) * |β| := by rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg h)]
      _ ≤ (d : ℝ) * (1 / (2 * (d : ℝ) ^ 2)) :=
        mul_le_mul (by exact_mod_cast hhd.le) hβ (abs_nonneg _) hdR.le
      _ = _ := by field_simp
  have htri := circle_norm_perturbation ((h * r : ℕ) / (d : ℝ)) ((h : ℝ) * β)
  have hphase : (h * r : ℕ) / (d : ℝ) + (h : ℝ) * β = (h : ℝ) * ((r : ℝ) / d + β) := by
    push_cast
    ring
  rw [hphase] at htri
  have hhalf : (1 / (d : ℝ)) = 2 * (1 / (2 * (d : ℝ))) := by ring
  rw [hhalf] at hbase
  linarith

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/TrigPolynomials.lean -/
section
/- # Finite trigonometric polynomials and their squared norms -/

open scoped ComplexConjugate

namespace Erdos12Proof

theorem unitExp_conj (t : ℝ) : conj (unitExp t) = unitExp (-t) := by
  unfold unitExp
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  ring

noncomputable def trigPolynomial {κ : Type*} (S : Finset κ)
    (c : κ → ℂ) (a : κ → ℝ) (x : ℝ) : ℂ :=
  ∑ i ∈ S, c i * unitExp (a i * x)

theorem trigPolynomial_norm_sq {κ : Type*} (S : Finset κ)
    (c : κ → ℂ) (a : κ → ℝ) (x : ℝ) :
    ((‖trigPolynomial S c a x‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, c i * conj (c j) * unitExp ((a i - a j) * x) := by
  have hnorm := Complex.mul_conj (trigPolynomial S c a x)
  rw [Complex.normSq_eq_norm_sq] at hnorm
  rw [← hnorm]
  unfold trigPolynomial
  simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [unitExp_conj, sub_mul, sub_eq_add_neg, unitExp_add]
  ring

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/SchwartzPolynomials.lean -/
section
/- # Products of Schwartz functions with finite exponential polynomials -/

open scoped SchwartzMap ComplexConjugate

namespace Erdos12Proof

noncomputable def schwartzTrigProduct {κ : Type*} (S : Finset κ)
    (c : κ → ℂ) (a : κ → ℝ) (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  ∑ i ∈ S, c i • schwartzModulate f (a i)

theorem schwartzTrigProduct_apply {κ : Type*} (S : Finset κ)
    (c : κ → ℂ) (a : κ → ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    schwartzTrigProduct S c a f x = trigPolynomial S c a x * f x := by
  simp only [schwartzTrigProduct, sum_apply, smul_apply, schwartzModulate_apply,
    Circle.smul_def, smul_eq_mul, ← unitExp_eq_fourierChar, trigPolynomial, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem schwartz_sum_integer {κ : Type*} (S : Finset κ) (g : κ → 𝓢(ℝ, ℂ)) :
    (∑' n : ℤ, (∑ i ∈ S, g i) n) = ∑ i ∈ S, ∑' n : ℤ, g i n := by
  simp only [sum_apply]
  exact Summable.tsum_finsetSum (fun i _ => schwartz_summable_int (g i))

theorem schwartz_smul_modulate_integer (f : 𝓢(ℝ, ℂ)) (c : ℂ) (a : ℝ) :
    (∑' n : ℤ, (c • schwartzModulate f a) n) = c * integerFourierSum f a := by
  simp only [smul_apply, schwartzModulate_apply, Circle.smul_def, smul_eq_mul,
    ← unitExp_eq_fourierChar, tsum_mul_left, integerFourierSum]

noncomputable def schwartzSquareProduct {κ : Type*} (S : Finset κ)
    (c : κ → ℂ) (a : κ → ℝ) (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  ∑ i ∈ S, ∑ j ∈ S, (c i * conj (c j)) • schwartzModulate f (a i - a j)

theorem schwartzSquareProduct_apply {κ : Type*} (S : Finset κ)
    (c : κ → ℂ) (a : κ → ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    schwartzSquareProduct S c a f x = ((‖trigPolynomial S c a x‖ ^ 2 : ℝ) : ℂ) * f x := by
  simp only [schwartzSquareProduct, sum_apply, smul_apply, schwartzModulate_apply,
    Circle.smul_def, smul_eq_mul, ← unitExp_eq_fourierChar,
    trigPolynomial_norm_sq, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem schwartzSquareProduct_integer_sum {κ : Type*} (S : Finset κ)
    (c : κ → ℂ) (a : κ → ℝ) (f : 𝓢(ℝ, ℂ)) :
    (∑' n : ℤ, schwartzSquareProduct S c a f n) =
      ∑ i ∈ S, ∑ j ∈ S, c i * conj (c j) * integerFourierSum f (a i - a j) := by
  unfold schwartzSquareProduct
  rw [schwartz_sum_integer]
  apply Finset.sum_congr rfl
  intro i _
  rw [schwartz_sum_integer]
  simp only [schwartz_smul_modulate_integer]

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/SelbergPoisson.lean -/
section
/- # The sparse Poisson expansion of the weighted Selberg majorant -/

open MeasureTheory FourierTransform
open scoped SchwartzMap

namespace Erdos12Proof

theorem norm_sum_le_of_unique_nonzero {κ : Type*} [DecidableEq κ]
    (S : Finset κ) (g : κ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ i ∈ S, ‖g i‖ ≤ B)
    (hunique : ∀ i ∈ S, ∀ j ∈ S, g i ≠ 0 → g j ≠ 0 → i = j) :
    ‖∑ i ∈ S, g i‖ ≤ B := by
  classical
  by_cases hex : ∃ i ∈ S, g i ≠ 0
  · obtain ⟨i, hi, hgi⟩ := hex
    have hsum : ∑ j ∈ S, g j = g i := by
      apply Finset.sum_eq_single i
      · intro j hj hji
        by_contra hgj
        exact hji (hunique j hj i hi hgj hgi)
      · intro hnot
        exact (hnot hi).elim
    rw [hsum]
    exact hbound i hi
  · have hsum : ∑ i ∈ S, g i = 0 := Finset.sum_eq_zero (by
      intro i hi
      by_contra hgi
      exact hex ⟨i, hi, hgi⟩)
    rw [hsum, norm_zero]
    exact hB

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → ℕ)
variable [∀ i, NeZero (m i)]

noncomputable def selbergSpectrum (z : ℝ) : Finset (ComplexSieveCube m) :=
  Finset.univ.filter (fun k => (spectralDenominator m k : ℝ) < z ^ 2)

noncomputable def weightedSelbergSum (z : ℝ) (f : 𝓢(ℝ, ℂ)) (a : ℝ) : ℂ :=
  ∑' n : ℤ, (integerSieveMajorant m z n : ℂ) * unitExp (a * n) * f n

theorem weightedSelbergSum_expansion (hm : ∀ i, 1 < m i) (z : ℝ) (hz : 0 < z)
    (f : 𝓢(ℝ, ℂ)) (a : ℝ) :
    weightedSelbergSum m z f a =
      ∑ k ∈ selbergSpectrum m z, (integerSieveCoefficient m z k : ℂ) *
        integerFourierSum f (a + sieveFrequency m k) := by
  unfold weightedSelbergSum
  simp_rw [integerSieveMajorant_expansion m hm z hz]
  exact integerFourierSum_finite_expansion (selbergSpectrum m z)
    (fun k => (integerSieveCoefficient m z k : ℂ)) (sieveFrequency m) f a

theorem selberg_twist_unique_active (hm : ∀ i, 0 < m i)
    (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    (z η : ℝ) (hz : 0 < z) (hη : η < 1 / 2) (hspacing : 2 * η < 1 / z ^ 4)
    (f : 𝓢(ℝ, ℂ)) (hband : ∀ ξ, η < |ξ| → 𝓕 f ξ = 0) (a : ℝ)
    {k l : ComplexSieveCube m} (hk : k ∈ selbergSpectrum m z)
    (hl : l ∈ selbergSpectrum m z)
    (hkNZ : integerFourierSum f (a + sieveFrequency m k) ≠ 0)
    (hlNZ : integerFourierSum f (a + sieveFrequency m l) ≠ 0) : k = l := by
  have hnear (j : ComplexSieveCube m)
      (hjNZ : integerFourierSum f (a + sieveFrequency m j) ≠ 0) :
      dist (sieveFrequency m j : UnitAddCircle) ((-a : ℝ) : UnitAddCircle) ≤ η := by
    have hnorm : ‖((a + sieveFrequency m j : ℝ) : UnitAddCircle)‖ ≤ η := by
      by_contra h
      exact hjNZ (integerFourierSum_vanish f _ η hη hband (lt_of_not_ge h))
    rw [dist_eq_norm, ← AddCircle.coe_sub, sub_neg_eq_add, add_comm]
    exact hnorm
  apply sieveFrequency_unique_near m hm hcop hz hspacing ((-a : ℝ) : UnitAddCircle)
  · exact (Finset.mem_filter.mp hk).2
  · exact (Finset.mem_filter.mp hl).2
  · exact hnear k hkNZ
  · simpa only [dist_comm] using hnear l hlNZ

theorem weightedSelbergSum_bound (hm : ∀ i, 1 < m i)
    (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    (z η : ℝ) (hz : 0 < z) (hη : η < 1 / 2) (hspacing : 2 * η < 1 / z ^ 4)
    (f : 𝓢(ℝ, ℂ)) (hband : ∀ ξ, η < |ξ| → 𝓕 f ξ = 0)
    (hreal : ∀ x, (f x).im = 0) (hpos : ∀ x, 0 ≤ (f x).re)
    (a B : ℝ) (hB : 0 ≤ B)
    (hcoeff : ∀ k ∈ selbergSpectrum m z,
      integerFourierSum f (a + sieveFrequency m k) ≠ 0 →
        |integerSieveCoefficient m z k| ≤ B) :
    ‖weightedSelbergSum m z f a‖ ≤ B * ∫ x, (f x).re := by
  rw [weightedSelbergSum_expansion m hm z hz]
  apply norm_sum_le_of_unique_nonzero
  · exact mul_nonneg hB (integral_nonneg hpos)
  · intro k hk
    by_cases hzero : integerFourierSum f (a + sieveFrequency m k) = 0
    · rw [hzero, mul_zero, norm_zero]
      exact mul_nonneg hB (integral_nonneg hpos)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (hcoeff k hk hzero)
        (integerFourierSum_bound f _ η hη hband hreal hpos) (norm_nonneg _) hB
  · intro k hk l hl hkNZ hlNZ
    apply selberg_twist_unique_active m (fun i => lt_trans Nat.zero_lt_one (hm i))
      hcop z η hz hη hspacing f hband a hk hl
    · intro hzero
      exact hkNZ (by rw [hzero, mul_zero])
    · intro hzero
      exact hlNZ (by rw [hzero, mul_zero])

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/SelbergCorrelationBounds.lean -/
section
/- # Diagonal and off-diagonal Selberg correlation bounds -/

open MeasureTheory FourierTransform
open scoped SchwartzMap

namespace Erdos12Proof

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → ℕ)
variable [∀ i, NeZero (m i)]

omit [DecidableEq ι] [∀ i, NeZero (m i)] in
theorem sieveFrequency_zero : sieveFrequency m 0 = 0 := by
  simp [sieveFrequency]

omit [DecidableEq ι] [∀ i, NeZero (m i)] in
theorem spectralDenominator_zero : spectralDenominator m 0 = 1 := by
  simp [spectralDenominator, frequencySupport]

theorem zero_mem_selbergSpectrum (z : ℝ) (hz : 1 < z) :
    0 ∈ selbergSpectrum m z := by
  simp only [selbergSpectrum, Finset.mem_filter, Finset.mem_univ, true_and,
    spectralDenominator_zero, Nat.cast_one]
  nlinarith

omit [DecidableEq ι] in
theorem spectralDenominator_contains (k : ComplexSieveCube m) (i : ι) (hi : k i ≠ 0) :
    m i ≤ spectralDenominator m k := by
  apply Nat.le_of_dvd (spectralDenominator_pos m k)
  apply Finset.dvd_prod_of_mem
  simp [frequencySupport, hi]

omit [DecidableEq ι] in
theorem nonzero_spectralDenominator_lower_bound (q : ℝ) (hm : ∀ i, q ^ 2 ≤ (m i : ℝ))
    (k : ComplexSieveCube m) (hk : k ≠ 0) : q ^ 2 ≤ (spectralDenominator m k : ℝ) := by
  have hex : ∃ i, k i ≠ 0 := by
    by_contra h
    push Not at h
    exact hk (funext h)
  obtain ⟨i, hi⟩ := hex
  exact (hm i).trans (by exact_mod_cast spectralDenominator_contains m k i hi)

theorem integerSieveCoefficient_uniform (hm : ∀ i, 25 ≤ m i) (z : ℝ) (hz : 1 < z)
    (k : ComplexSieveCube m) : |integerSieveCoefficient m z k| ≤ 1 / sieveMass m z := by
  have hm1 : ∀ i, 1 < m i := by intro i; have := hm i; omega
  have hG := sieveMass_pos hm1 hz
  have hD : (1 : ℝ) ≤ (spectralDenominator m k : ℝ) := by
    exact_mod_cast spectralDenominator_pos m k
  have hs : 1 ≤ Real.sqrt (spectralDenominator m k : ℝ) :=
    Real.le_sqrt_of_sq_le (by simpa only [one_pow] using hD)
  apply (integerSieveCoefficient_bound m hm z hz k).trans
  exact one_div_le_one_div_of_le hG (by nlinarith)

theorem integerSieveCoefficient_nonzero_bound (hm : ∀ i, 25 ≤ m i)
    (q : ℝ) (hq : 0 < q) (hmq : ∀ i, q ^ 2 ≤ (m i : ℝ))
    (z : ℝ) (hz : 1 < z) (k : ComplexSieveCube m) (hk : k ≠ 0) :
    |integerSieveCoefficient m z k| ≤ 1 / (sieveMass m z * q) := by
  have hm1 : ∀ i, 1 < m i := by intro i; have := hm i; omega
  have hG := sieveMass_pos hm1 hz
  have hs : q ≤ Real.sqrt (spectralDenominator m k : ℝ) :=
    Real.le_sqrt_of_sq_le (nonzero_spectralDenominator_lower_bound m q hmq k hk)
  apply (integerSieveCoefficient_bound m hm z hz k).trans
  exact one_div_le_one_div_of_le (mul_pos hG hq) (mul_le_mul_of_nonneg_left hs hG.le)

theorem weightedSelbergSum_zero (hm : ∀ i, 1 < m i)
    (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    (z η : ℝ) (hz : 1 < z) (hη : η < 1 / 2) (hspacing : 2 * η < 1 / z ^ 4)
    (f : 𝓢(ℝ, ℂ)) (hband : ∀ ξ, η < |ξ| → 𝓕 f ξ = 0) :
    weightedSelbergSum m z f 0 = (1 / (sieveMass m z : ℂ)) * ∫ x, f x := by
  rw [weightedSelbergSum_expansion m hm z (by linarith)]
  have hsum : (∑ k ∈ selbergSpectrum m z, (integerSieveCoefficient m z k : ℂ) *
        integerFourierSum f (0 + sieveFrequency m k)) =
      (integerSieveCoefficient m z 0 : ℂ) * integerFourierSum f 0 := by
    rw [Finset.sum_eq_single 0]
    · rw [sieveFrequency_zero, zero_add]
    · intro k hk hk0
      have hsep := sieveFrequency_circle_separated m
        (fun i => lt_trans Nat.zero_lt_one (hm i)) hcop (by linarith : 0 < z) hk0
        (Finset.mem_filter.mp hk).2
        (Finset.mem_filter.mp (zero_mem_selbergSpectrum m z hz)).2
      rw [sieveFrequency_zero, AddCircle.coe_zero, dist_zero_right] at hsep
      have hgap : η < 1 / z ^ 4 := by
        have : 0 < 1 / z ^ 4 := by positivity
        linarith
      rw [zero_add, integerFourierSum_vanish f _ η hη hband (hgap.trans_le hsep), mul_zero]
    · intro hnot
      exact (hnot (zero_mem_selbergSpectrum m z hz)).elim
  rw [hsum, integerSieveCoefficient_zero m hm z hz, integerFourierSum_zero f η hη hband]
  push_cast
  rfl

theorem weightedSelbergSum_off_diagonal (hm : ∀ i, 25 ≤ m i)
    (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    (q : ℝ) (hq : 0 < q) (hmq : ∀ i, q ^ 2 ≤ (m i : ℝ))
    (z η : ℝ) (hz : 1 < z) (hη : η < 1 / 2) (hspacing : 2 * η < 1 / z ^ 4)
    (f : 𝓢(ℝ, ℂ)) (hband : ∀ ξ, η < |ξ| → 𝓕 f ξ = 0)
    (hreal : ∀ x, (f x).im = 0) (hpos : ∀ x, 0 ≤ (f x).re)
    (a : ℝ) (ha : η < ‖(a : UnitAddCircle)‖) :
    ‖weightedSelbergSum m z f a‖ ≤ (∫ x, (f x).re) / (sieveMass m z * q) := by
  have hm1 : ∀ i, 1 < m i := by intro i; have := hm i; omega
  have hG := sieveMass_pos hm1 hz
  have hbound := weightedSelbergSum_bound m hm1 hcop z η (by linarith)
    hη hspacing f hband hreal hpos a (1 / (sieveMass m z * q))
      (by positivity) (by
        intro k _ hactive
        have hk : k ≠ 0 := by
          intro hk
          subst k
          rw [sieveFrequency_zero, add_zero] at hactive
          exact hactive (integerFourierSum_vanish f a η hη hband ha)
        exact integerSieveCoefficient_nonzero_bound m hm q hq hmq z hz k hk)
  simpa only [one_div_mul_eq_div] using hbound

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/SelbergDualBound.lean -/
section
/- # The finite dual quadratic-form estimate -/

open MeasureTheory FourierTransform
open scoped SchwartzMap ComplexConjugate

namespace Erdos12Proof

theorem integral_eq_ofReal_re (f : 𝓢(ℝ, ℂ)) (hreal : ∀ x, (f x).im = 0) :
    (∫ x, f x) = ((∫ x, (f x).re : ℝ) : ℂ) := by
  have hpoint : (f : ℝ → ℂ) = fun x => ((f x).re : ℂ) := by
    funext x
    exact Complex.ext rfl (hreal x)
  conv_lhs => rw [hpoint]
  exact integral_complex_ofReal

theorem finite_gram_bound {κ : Type*} [DecidableEq κ] (S : Finset κ)
    (c : κ → ℂ) (a : κ → ℝ) (K : ℝ → ℂ) (M B : ℝ) (hB : 0 ≤ B)
    (hdiag : K 0 = (M : ℂ))
    (hoff : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ‖K (a i - a j)‖ ≤ B) :
    (∑ i ∈ S, ∑ j ∈ S, c i * conj (c j) * K (a i - a j)).re ≤
      M * (∑ i ∈ S, ‖c i‖ ^ 2) + B * (∑ i ∈ S, ‖c i‖) ^ 2 := by
  have hpoint (i : κ) (hi : i ∈ S) (j : κ) (hj : j ∈ S) :
      (c i * conj (c j) * K (a i - a j)).re ≤
        (if i = j then M * ‖c i‖ ^ 2 else 0) + B * ‖c i‖ * ‖c j‖ := by
    by_cases hij : i = j
    · subst j
      rw [sub_self, hdiag, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        sub_zero, ite_true]
      nlinarith [mul_nonneg hB (sq_nonneg ‖c i‖)]
    · calc
        _ ≤ ‖c i * conj (c j) * K (a i - a j)‖ := Complex.re_le_norm _
        _ = ‖c i‖ * ‖c j‖ * ‖K (a i - a j)‖ := by rw [norm_mul, norm_mul, Complex.norm_conj]
        _ ≤ ‖c i‖ * ‖c j‖ * B :=
          mul_le_mul_of_nonneg_left (hoff i hi j hj hij) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ = _ := by rw [ite_eq_right hij]; ring
  calc
    _ = ∑ i ∈ S, ∑ j ∈ S, (c i * conj (c j) * K (a i - a j)).re := by simp
    _ ≤ ∑ i ∈ S, ∑ j ∈ S,
        ((if i = j then M * ‖c i‖ ^ 2 else 0) + B * ‖c i‖ * ‖c j‖) :=
      Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hpoint i hi j hj
    _ = _ := by
      simp_rw [Finset.sum_add_distrib]
      have hdiagSum : (∑ i ∈ S, ∑ j ∈ S, if i = j then M * ‖c i‖ ^ 2 else 0) =
          M * ∑ i ∈ S, ‖c i‖ ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        simp [hi]
      rw [hdiagSum]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → ℕ)
variable [∀ i, NeZero (m i)]

theorem weightedSelbergSum_zero_real (hm : ∀ i, 1 < m i)
    (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    (z η : ℝ) (hz : 1 < z) (hη : η < 1 / 2) (hspacing : 2 * η < 1 / z ^ 4)
    (f : 𝓢(ℝ, ℂ)) (hband : ∀ ξ, η < |ξ| → 𝓕 f ξ = 0)
    (hreal : ∀ x, (f x).im = 0) :
    weightedSelbergSum m z f 0 = ((∫ x, (f x).re) / sieveMass m z : ℝ) := by
  rw [weightedSelbergSum_zero m hm hcop z η hz hη hspacing f hband,
    integral_eq_ofReal_re f hreal]
  push_cast
  ring

theorem selberg_dual_gram_bound {κ : Type*} [DecidableEq κ] (S : Finset κ)
    (c : κ → ℂ) (a : κ → ℝ) (hm : ∀ i, 25 ≤ m i)
    (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    (q : ℝ) (hq : 0 < q) (hmq : ∀ i, q ^ 2 ≤ (m i : ℝ))
    (z η : ℝ) (hz : 1 < z) (hη : η < 1 / 2) (hspacing : 2 * η < 1 / z ^ 4)
    (f : 𝓢(ℝ, ℂ)) (hband : ∀ ξ, η < |ξ| → 𝓕 f ξ = 0)
    (hreal : ∀ x, (f x).im = 0) (hpos : ∀ x, 0 ≤ (f x).re)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      η < dist (a i : UnitAddCircle) (a j : UnitAddCircle)) :
    (∑ i ∈ S, ∑ j ∈ S,
      c i * conj (c j) * weightedSelbergSum m z f (a i - a j)).re ≤
        ((∫ x, (f x).re) / sieveMass m z) *
          ((∑ i ∈ S, ‖c i‖ ^ 2) + (∑ i ∈ S, ‖c i‖) ^ 2 / q) := by
  have hm1 : ∀ i, 1 < m i := by intro i; have := hm i; omega
  have hG := sieveMass_pos hm1 hz
  have hI : 0 ≤ ∫ x, (f x).re := integral_nonneg hpos
  have hoff (i : κ) (hi : i ∈ S) (j : κ) (hj : j ∈ S) (hij : i ≠ j) :
      ‖weightedSelbergSum m z f (a i - a j)‖ ≤
        (∫ x, (f x).re) / (sieveMass m z * q) := by
    apply weightedSelbergSum_off_diagonal m hm hcop q hq hmq z η hz hη hspacing
      f hband hreal hpos
    have h := hsep i hi j hj hij
    simpa only [dist_eq_norm, ← AddCircle.coe_sub] using h
  have h := finite_gram_bound S c a (weightedSelbergSum m z f)
    ((∫ x, (f x).re) / sieveMass m z)
    ((∫ x, (f x).re) / (sieveMass m z * q)) (by positivity)
    (weightedSelbergSum_zero_real m hm1 hcop z η hz hη hspacing f hband hreal) hoff
  convert h using 1
  ring

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/SelbergWeightedSums.lean -/
section
/- # Summability and the weighted square-sum identity -/

open MeasureTheory
open scoped SchwartzMap ComplexConjugate

namespace Erdos12Proof

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → ℕ)
variable [∀ i, NeZero (m i)]

noncomputable def selbergSchwartzWeight (z : ℝ) (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  schwartzTrigProduct (selbergSpectrum m z)
    (fun k => (integerSieveCoefficient m z k : ℂ)) (sieveFrequency m) f

theorem selbergSchwartzWeight_integer (hm : ∀ i, 1 < m i) (z : ℝ) (hz : 0 < z)
    (f : 𝓢(ℝ, ℂ)) (n : ℤ) :
    selbergSchwartzWeight m z f n = (integerSieveMajorant m z n : ℂ) * f n := by
  rw [selbergSchwartzWeight, schwartzTrigProduct_apply,
    integerSieveMajorant_expansion m hm z hz]
  unfold trigPolynomial
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm (sieveFrequency m k) (n : ℝ)]

theorem selbergSchwartzWeight_fourierSum (hm : ∀ i, 1 < m i) (z : ℝ) (hz : 0 < z)
    (f : 𝓢(ℝ, ℂ)) (a : ℝ) :
    integerFourierSum (selbergSchwartzWeight m z f) a = weightedSelbergSum m z f a := by
  unfold integerFourierSum weightedSelbergSum
  apply tsum_congr
  intro n
  rw [selbergSchwartzWeight_integer m hm z hz]
  ring

theorem selbergSquareProduct_re {κ : Type*} (S : Finset κ) (c : κ → ℂ) (a : κ → ℝ)
    (hm : ∀ i, 1 < m i) (z : ℝ) (hz : 0 < z) (f : 𝓢(ℝ, ℂ)) (n : ℤ) :
    (schwartzSquareProduct S c a (selbergSchwartzWeight m z f) n).re =
      integerSieveMajorant m z n * (f n).re * ‖trigPolynomial S c a n‖ ^ 2 := by
  rw [schwartzSquareProduct_apply, selbergSchwartzWeight_integer m hm z hz]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

theorem selberg_weighted_square_summable {κ : Type*} (S : Finset κ) (c : κ → ℂ)
    (a : κ → ℝ) (hm : ∀ i, 1 < m i) (z : ℝ) (hz : 0 < z) (f : 𝓢(ℝ, ℂ)) :
    Summable (fun n : ℤ =>
      integerSieveMajorant m z n * (f n).re * ‖trigPolynomial S c a n‖ ^ 2) := by
  have h := (Complex.hasSum_re
    (schwartz_summable_int (schwartzSquareProduct S c a (selbergSchwartzWeight m z f))).hasSum).summable
  exact h.congr (fun n => selbergSquareProduct_re m S c a hm z hz f n)

theorem selberg_weighted_square_identity {κ : Type*} (S : Finset κ) (c : κ → ℂ)
    (a : κ → ℝ) (hm : ∀ i, 1 < m i) (z : ℝ) (hz : 0 < z) (f : 𝓢(ℝ, ℂ)) :
    (∑' n : ℤ, integerSieveMajorant m z n * (f n).re * ‖trigPolynomial S c a n‖ ^ 2) =
      (∑ i ∈ S, ∑ j ∈ S,
        c i * conj (c j) * weightedSelbergSum m z f (a i - a j)).re := by
  calc
    _ = ∑' n : ℤ, (schwartzSquareProduct S c a (selbergSchwartzWeight m z f) n).re := by
      apply tsum_congr
      intro n
      exact (selbergSquareProduct_re m S c a hm z hz f n).symm
    _ = (∑' n : ℤ, schwartzSquareProduct S c a (selbergSchwartzWeight m z f) n).re :=
      (Complex.re_tsum (schwartz_summable_int _)).symm
    _ = _ := by
      rw [schwartzSquareProduct_integer_sum]
      simp only [selbergSchwartzWeight_fourierSum m hm z hz]

theorem sifted_dual_sum_le_weighted {κ : Type*} (S : Finset κ) (c : κ → ℂ)
    (a : κ → ℝ) (T : Finset ℤ) (hm : ∀ i, 1 < m i)
    (z : ℝ) (hz : 1 < z) (f : 𝓢(ℝ, ℂ)) (hpos : ∀ x, 0 ≤ (f x).re)
    (hmajorant : ∀ n ∈ T, 1 ≤ (f n).re)
    (hsifted : ∀ n ∈ T, ∀ i, (n : ZMod (m i)) ≠ 0) :
    (∑ n ∈ T, ‖trigPolynomial S c a n‖ ^ 2) ≤
      ∑' n : ℤ, integerSieveMajorant m z n * (f n).re * ‖trigPolynomial S c a n‖ ^ 2 := by
  calc
    _ ≤ ∑ n ∈ T, integerSieveMajorant m z n * (f n).re *
        ‖trigPolynomial S c a n‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      rw [integerSieveMajorant_eq_one m hm z hz n (hsifted n hn), one_mul]
      have h := mul_le_mul_of_nonneg_right (hmajorant n hn) (sq_nonneg ‖trigPolynomial S c a n‖)
      simpa only [one_mul] using h
    _ ≤ _ := (selberg_weighted_square_summable m S c a hm z (by linarith) f).sum_le_tsum T
      (fun n _ => mul_nonneg
        (mul_nonneg (integerSieveMajorant_nonneg m z n) (hpos n)) (sq_nonneg _))

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/SiftedDual.lean -/
section
/- # The finite sifted dual estimate -/

open MeasureTheory FourierTransform
open scoped SchwartzMap ComplexConjugate

namespace Erdos12Proof

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
variable (m : ι → ℕ) [∀ i, NeZero (m i)]

theorem sifted_dual_bound (S : Finset κ) (c : κ → ℂ) (a : κ → ℝ) (T : Finset ℤ)
    (hm : ∀ i, 25 ≤ m i) (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    (q : ℝ) (hq : 0 < q) (hmq : ∀ i, q ^ 2 ≤ (m i : ℝ))
    (z η : ℝ) (hz : 1 < z) (hη : η < 1 / 2) (hspacing : 2 * η < 1 / z ^ 4)
    (f : 𝓢(ℝ, ℂ)) (hband : ∀ ξ, η < |ξ| → 𝓕 f ξ = 0)
    (hreal : ∀ x, (f x).im = 0) (hpos : ∀ x, 0 ≤ (f x).re)
    (hmajorant : ∀ n ∈ T, 1 ≤ (f n).re)
    (hsifted : ∀ n ∈ T, ∀ i, (n : ZMod (m i)) ≠ 0)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      η < dist (a i : UnitAddCircle) (a j : UnitAddCircle)) :
    (∑ n ∈ T, ‖trigPolynomial S c a n‖ ^ 2) ≤
      ((∫ x, (f x).re) / sieveMass m z) *
        ((∑ i ∈ S, ‖c i‖ ^ 2) + (∑ i ∈ S, ‖c i‖) ^ 2 / q) := by
  have hm1 : ∀ i, 1 < m i := by intro i; have := hm i; omega
  calc
    _ ≤ ∑' n : ℤ, integerSieveMajorant m z n * (f n).re *
        ‖trigPolynomial S c a n‖ ^ 2 :=
      sifted_dual_sum_le_weighted m S c a T hm1 z hz f hpos hmajorant hsifted
    _ = (∑ i ∈ S, ∑ j ∈ S,
        c i * conj (c j) * weightedSelbergSum m z f (a i - a j)).re :=
      selberg_weighted_square_identity m S c a hm1 z (by linarith) f
    _ ≤ _ := selberg_dual_gram_bound m S c a hm hcop q hq hmq z η hz hη hspacing
      f hband hreal hpos hsep

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/QuantitativeSiftedDual.lean -/
section
/- # A uniform dual bound on a finite interval -/

open MeasureTheory FourierTransform
open scoped SchwartzMap

namespace Erdos12Proof

noncomputable def intervalMajorantConstant : ℝ := Classical.choose exists_interval_majorant

theorem intervalMajorantConstant_pos : 0 < intervalMajorantConstant :=
  (Classical.choose_spec exists_interval_majorant).1

theorem exists_dual_bandwidth (N δ z : ℝ) (hδ : 0 < δ) (hz : 1 < z) (hN : z ^ 4 ≤ N) :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧ 2 * η < 1 / z ^ 4 ∧ η < δ ∧
      N + η⁻¹ ≤ 5 * (N + δ⁻¹) := by
  let η := 1 / (4 * (N + δ⁻¹))
  have hz0 : 0 < z := by linarith
  have hz4 : 1 < z ^ 4 := one_lt_pow₀ hz (by norm_num)
  have hN0 : 0 < N := lt_of_lt_of_le (pow_pos hz0 4) hN
  have hsum : 0 < N + δ⁻¹ := add_pos hN0 (inv_pos.mpr hδ)
  have hη : 0 < η := one_div_pos.mpr (mul_pos (by norm_num) hsum)
  have hidentity : η * (4 * (N + δ⁻¹)) = 1 := by
    dsimp [η]
    field_simp
  have hηN : η * z ^ 4 ≤ η * N := mul_le_mul_of_nonneg_left hN hη.le
  have hηinv : 0 < η * δ⁻¹ := mul_pos hη (inv_pos.mpr hδ)
  refine ⟨η, hη, ?_, ?_, ?_, ?_⟩
  · have : 1 < N + δ⁻¹ := by linarith [inv_pos.mpr hδ]
    dsimp [η]
    apply (div_lt_iff₀ (mul_pos (by norm_num) hsum)).mpr
    nlinarith
  · apply (lt_div_iff₀ (pow_pos hz0 4)).mpr
    nlinarith
  · have hsmall : η * δ⁻¹ < 1 := by nlinarith [mul_pos hη hN0]
    have : η / δ < 1 := by simpa only [div_eq_mul_inv] using hsmall
    exact (div_lt_one hδ).mp this
  · have hinv : η⁻¹ = 4 * (N + δ⁻¹) := by simp [η]
    rw [hinv]
    nlinarith [inv_pos.mpr hδ]

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
variable (m : ι → ℕ) [∀ i, NeZero (m i)]

theorem quantitative_sifted_dual_bound (S : Finset κ) (c : κ → ℂ) (a : κ → ℝ)
    (T : Finset ℤ) (hm : ∀ i, 25 ≤ m i)
    (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    (q : ℝ) (hq : 0 < q) (hmq : ∀ i, q ^ 2 ≤ (m i : ℝ))
    (N δ z : ℝ) (hδ : 0 < δ) (hz : 1 < z) (hN : z ^ 4 ≤ N)
    (hinterval : ∀ n ∈ T, 0 ≤ (n : ℝ) ∧ (n : ℝ) ≤ N)
    (hsifted : ∀ n ∈ T, ∀ i, (n : ZMod (m i)) ≠ 0)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      δ ≤ dist (a i : UnitAddCircle) (a j : UnitAddCircle)) :
    (∑ n ∈ T, ‖trigPolynomial S c a n‖ ^ 2) ≤
      (5 * intervalMajorantConstant * (N + δ⁻¹) / sieveMass m z) *
        ((∑ i ∈ S, ‖c i‖ ^ 2) + (∑ i ∈ S, ‖c i‖) ^ 2 / q) := by
  obtain ⟨η, hη, hηhalf, hspacing, hηδ, hmass⟩ := exists_dual_bandwidth N δ z hδ hz hN
  have hN0 : 0 ≤ N := (pow_nonneg (by linarith : (0 : ℝ) ≤ z) 4).trans hN
  obtain ⟨f, hreal, hpos, hmajorant, hband, hintegral⟩ :=
    (Classical.choose_spec exists_interval_majorant).2 N η hN0 hη
  have hbase := sifted_dual_bound m S c a T hm hcop q hq hmq z η hz hηhalf hspacing
    f hband hreal hpos (fun n hn => hmajorant n (hinterval n hn).1 (hinterval n hn).2)
      hsifted (fun i hi j hj hij => hηδ.trans_le (hsep i hi j hj hij))
  have hm1 : ∀ i, 1 < m i := by intro i; have := hm i; omega
  have hG := sieveMass_pos hm1 hz
  have hI : (∫ x, (f x).re) ≤ 5 * intervalMajorantConstant * (N + δ⁻¹) := by
    calc
      _ ≤ intervalMajorantConstant * (N + η⁻¹) := hintegral
      _ ≤ intervalMajorantConstant * (5 * (N + δ⁻¹)) :=
        mul_le_mul_of_nonneg_left hmass intervalMajorantConstant_pos.le
      _ = _ := by ring
  apply hbase.trans
  apply mul_le_mul_of_nonneg_right ((div_le_div_iff_of_pos_right hG).mpr hI)
  exact add_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg ‖c i‖)
    (div_nonneg (sq_nonneg _) hq.le)

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/RestrictionParameters.lean -/
section
/- # Parameters in the logarithmic dual restriction estimate -/

namespace Erdos12Proof

noncomputable def coefficientEnergy {κ : Type*} (S : Finset κ) (c : κ → ℂ) : ℝ :=
  ∑ i ∈ S, ‖c i‖ ^ 2

noncomputable def coefficientMass {κ : Type*} (S : Finset κ) (c : κ → ℂ) : ℝ :=
  ∑ i ∈ S, ‖c i‖

noncomputable def coefficientRatio {κ : Type*} (S : Finset κ) (c : κ → ℂ) : ℝ :=
  coefficientMass S c ^ 2 / coefficientEnergy S c

theorem coefficientEnergy_nonneg {κ : Type*} (S : Finset κ) (c : κ → ℂ) :
    0 ≤ coefficientEnergy S c := Finset.sum_nonneg (fun i _ => sq_nonneg ‖c i‖)

theorem coefficientRatio_ge_one {κ : Type*} (S : Finset κ) (c : κ → ℂ)
    (hc : 0 < coefficientEnergy S c) : 1 ≤ coefficientRatio S c := by
  unfold coefficientRatio
  apply (le_div_iff₀ hc).mpr
  simpa only [one_mul, coefficientEnergy, coefficientMass] using
    Finset.sum_sq_le_sq_sum_of_nonneg (s := S) (fun i _ => norm_nonneg (c i))

theorem coefficientRatio_identity {κ : Type*} (S : Finset κ) (c : κ → ℂ)
    (hc : 0 < coefficientEnergy S c) :
    coefficientRatio S c * coefficientEnergy S c = coefficientMass S c ^ 2 := by
  unfold coefficientRatio
  exact div_mul_cancel₀ _ hc.ne'

theorem coefficient_correction_bound {κ : Type*} (S : Finset κ) (c : κ → ℂ)
    (hc : 0 < coefficientEnergy S c) :
    coefficientEnergy S c + coefficientMass S c ^ 2 / (2 * coefficientRatio S c) ≤
      2 * coefficientEnergy S c := by
  have hR := coefficientRatio_ge_one S c hc
  have hidentity := coefficientRatio_identity S c hc
  have hq : 0 < 2 * coefficientRatio S c := by linarith
  have hterm : coefficientMass S c ^ 2 / (2 * coefficientRatio S c) ≤ coefficientEnergy S c := by
    apply (div_le_iff₀ hq).mpr
    nlinarith
  linarith

noncomputable def sieveRemovalCutoff (R : ℝ) : ℝ := max 25 ((2 * R) ^ 2)

theorem sieveRemovalCutoff_pos (R : ℝ) : 0 < sieveRemovalCutoff R := by
  unfold sieveRemovalCutoff
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 25) (le_max_left _ _)

theorem sieveRemovalCutoff_log_bound {R : ℝ} (hR : 1 ≤ R) :
    Real.log (sieveRemovalCutoff R) ≤ 5 * Real.log (2 * R) := by
  have hb : 1 ≤ 2 * R := by linarith
  have h25 : (25 : ℝ) ≤ (2 * R) ^ 5 := by
    calc
      (25 : ℝ) ≤ 2 ^ 5 := by norm_num
      _ ≤ (2 * R) ^ 5 := by gcongr; linarith
  have h2 : (2 * R) ^ 2 ≤ (2 * R) ^ 5 := pow_le_pow_right₀ hb (by norm_num)
  have hbound : sieveRemovalCutoff R ≤ (2 * R) ^ 5 := by
    unfold sieveRemovalCutoff
    exact max_le h25 h2
  have h := Real.log_le_log (sieveRemovalCutoff_pos R) hbound
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/LogarithmicDual.lean -/
section
/- # The logarithmic dual restriction bound for sifted integers -/

namespace Erdos12Proof

noncomputable def dualRestrictionConstant : ℝ :=
  50 * intervalMajorantConstant * primeRemovalConstant

theorem dualRestrictionConstant_pos : 0 < dualRestrictionConstant :=
  mul_pos (mul_pos (by norm_num) intervalMajorantConstant_pos) primeRemovalConstant_pos

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
variable (m : ι → ℕ) [∀ i, NeZero (m i)]

omit [DecidableEq ι] [DecidableEq κ] [∀ i, NeZero (m i)] in
theorem logarithmic_sifted_dual_bound (S : Finset κ) (c : κ → ℂ) (a : κ → ℝ)
    (T : Finset ℤ) (hprime : ∀ i, (m i).Prime)
    (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    (hc : 0 < coefficientEnergy S c)
    (N δ z : ℝ) (hδ : 0 < δ) (hz : 1 < z) (hN : z ^ 4 ≤ N)
    (hinterval : ∀ n ∈ T, 0 ≤ (n : ℝ) ∧ (n : ℝ) ≤ N)
    (hsifted : ∀ n ∈ T, ∀ i, (n : ZMod (m i)) ≠ 0)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      δ ≤ dist (a i : UnitAddCircle) (a j : UnitAddCircle)) :
    (∑ n ∈ T, ‖trigPolynomial S c a n‖ ^ 2) ≤
      dualRestrictionConstant * ((N + δ⁻¹) / sieveMass m z) *
        Real.log (2 * coefficientRatio S c) * coefficientEnergy S c := by
  classical
  let : ∀ i, NeZero (m i) := fun i => ⟨(hprime i).ne_zero⟩
  have hC := intervalMajorantConstant_pos
  let R := coefficientRatio S c
  let x := sieveRemovalCutoff R
  let small := Finset.univ.filter (fun i => (m i : ℝ) ≤ x)
  let mBig : {i // i ∉ small} → ℕ := fun i => m i
  have hR : 1 ≤ R := coefficientRatio_ge_one S c hc
  have hx25 : 25 ≤ x := by exact le_max_left 25 ((2 * R) ^ 2)
  have hxq : (2 * R) ^ 2 ≤ x := by exact le_max_right 25 ((2 * R) ^ 2)
  have hq : 0 < 2 * R := by linarith
  have hm1 : ∀ i, 1 < m i := fun i => (hprime i).one_lt
  have hinj : Function.Injective m := by
    intro i j hij
    by_contra hne
    have hself := hcop i j hne
    rw [← hij] at hself
    have hone : m i = 1 := by simpa only [Nat.coprime_self] using hself
    have := hm1 i
    omega
  have hbig (i : {i // i ∉ small}) : x < (mBig i : ℝ) := by
    have hi := i.property
    simpa only [small, Finset.mem_filter, Finset.mem_univ, true_and, not_le] using hi
  have hbig25 : ∀ i, 25 ≤ mBig i := by
    intro i
    exact_mod_cast hx25.trans (hbig i).le
  have hbigq : ∀ i, (2 * R) ^ 2 ≤ (mBig i : ℝ) := fun i => hxq.trans (hbig i).le
  have hbigcop : ∀ i j, i ≠ j → (mBig i).Coprime (mBig j) := by
    intro i j hij
    exact hcop i j (fun hval => hij (Subtype.ext hval))
  have hbase := quantitative_sifted_dual_bound mBig S c a T hbig25 hbigcop
    (2 * R) hq hbigq N δ z hδ hz hN hinterval (fun n hn i => hsifted n hn i) hsep
  have hG := sieveMass_pos hm1 hz
  have hGbig := sieveMass_pos (m := mBig) (fun i => hm1 i) hz
  have hremove := sieveMass_small_prime_removal m hm1 small hinj.injOn
    (fun i _ => hprime i) x z (by linarith) hz
      (fun i hi => (Finset.mem_filter.mp hi).2)
  have hlog := sieveRemovalCutoff_log_bound hR
  have hcompare : sieveMass m z ≤
      (5 * primeRemovalConstant * Real.log (2 * R)) * sieveMass mBig z := by
    apply hremove.trans
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlog primeRemovalConstant_pos.le) hGbig.le
    convert h using 1
    ring
  have hinverse : 1 / sieveMass mBig z ≤
      (5 * primeRemovalConstant * Real.log (2 * R)) / sieveMass m z := by
    apply (div_le_div_iff₀ hGbig hG).mpr
    simpa only [one_mul] using hcompare
  have hA : 0 ≤ N + δ⁻¹ := by
    have hN0 := (pow_nonneg (by linarith : (0 : ℝ) ≤ z) 4).trans hN
    exact add_nonneg hN0 (inv_nonneg.mpr hδ.le)
  have hfactor : 0 ≤ 5 * intervalMajorantConstant * (N + δ⁻¹) / sieveMass mBig z := by
    positivity
  have hbase2 : (∑ n ∈ T, ‖trigPolynomial S c a n‖ ^ 2) ≤
      (5 * intervalMajorantConstant * (N + δ⁻¹) / sieveMass mBig z) *
        (2 * coefficientEnergy S c) := by
    apply hbase.trans
    exact mul_le_mul_of_nonneg_left (coefficient_correction_bound S c hc) hfactor
  calc
    _ ≤ (5 * intervalMajorantConstant * (N + δ⁻¹) / sieveMass mBig z) *
        (2 * coefficientEnergy S c) := hbase2
    _ = (5 * intervalMajorantConstant * (N + δ⁻¹) * (2 * coefficientEnergy S c)) *
        (1 / sieveMass mBig z) := by ring
    _ ≤ (5 * intervalMajorantConstant * (N + δ⁻¹) * (2 * coefficientEnergy S c)) *
        ((5 * primeRemovalConstant * Real.log (2 * R)) / sieveMass m z) :=
      mul_le_mul_of_nonneg_left hinverse (by positivity)
    _ = _ := by unfold dualRestrictionConstant R; ring

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/FiniteFourier.lean -/
section
/- # Finite Fourier pairings and phase selection -/

open scoped ComplexConjugate

namespace Erdos12Proof

noncomputable def finiteFourierSum (T : Finset ℤ) (b : ℤ → ℂ) (ξ : ℝ) : ℂ :=
  ∑ n ∈ T, b n * unitExp (ξ * n)

theorem finiteFourier_pairing {κ : Type*} (S : Finset κ) (c : κ → ℂ) (a : κ → ℝ)
    (T : Finset ℤ) (b : ℤ → ℂ) :
    (∑ i ∈ S, c i * finiteFourierSum T b (a i)) =
      ∑ n ∈ T, b n * trigPolynomial S c a n := by
  unfold finiteFourierSum trigPolynomial
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem finite_pairing_cauchy_sq (T : Finset ℤ) (b P : ℤ → ℂ) :
    ‖∑ n ∈ T, b n * P n‖ ^ 2 ≤
      (∑ n ∈ T, ‖b n‖ ^ 2) * (∑ n ∈ T, ‖P n‖ ^ 2) := by
  have hnorm := norm_sum_le T (fun n => b n * P n)
  simp only [norm_mul] at hnorm
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq T (fun n => ‖b n‖) (fun n => ‖P n‖))

noncomputable def aligningPhase (z : ℂ) : ℂ := conj z / (‖z‖ : ℂ)

theorem aligningPhase_mul (z : ℂ) : aligningPhase z * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [aligningPhase, hz]
  · have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
    calc
      _ = z * conj z / (‖z‖ : ℂ) := by unfold aligningPhase; ring
      _ = ((‖z‖ ^ 2 : ℝ) : ℂ) / (‖z‖ : ℂ) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      _ = _ := by push_cast; field_simp

theorem aligningPhase_norm {z : ℂ} (hz : z ≠ 0) : ‖aligningPhase z‖ = 1 := by
  unfold aligningPhase
  rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg z), div_self (norm_ne_zero_iff.mpr hz)]

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/FourierLevelSets.lean -/
section
/- # Level-set estimates from the logarithmic dual inequality -/

namespace Erdos12Proof

theorem coefficientEnergy_unit {κ : Type*} (S : Finset κ) (c : κ → ℂ)
    (hc : ∀ i ∈ S, ‖c i‖ = 1) : coefficientEnergy S c = (S.card : ℝ) := by
  unfold coefficientEnergy
  calc
    _ = ∑ i ∈ S, (1 : ℝ) := Finset.sum_congr rfl (fun i hi => by rw [hc i hi, one_pow])
    _ = _ := by simp

theorem coefficientMass_unit {κ : Type*} (S : Finset κ) (c : κ → ℂ)
    (hc : ∀ i ∈ S, ‖c i‖ = 1) : coefficientMass S c = (S.card : ℝ) := by
  unfold coefficientMass
  calc
    _ = ∑ i ∈ S, (1 : ℝ) := Finset.sum_congr rfl hc
    _ = _ := by simp

theorem coefficientRatio_unit {κ : Type*} (S : Finset κ) (c : κ → ℂ)
    (hS : S.Nonempty) (hc : ∀ i ∈ S, ‖c i‖ = 1) : coefficientRatio S c = (S.card : ℝ) := by
  have hcard : (S.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hS
  unfold coefficientRatio
  rw [coefficientEnergy_unit S c hc, coefficientMass_unit S c hc]
  field_simp

variable {ι κ : Type*} [Fintype ι] (m : ι → ℕ)

theorem fourier_level_set_bound (S : Finset κ) (a : κ → ℝ) (T : Finset ℤ) (b : ℤ → ℂ)
    (hprime : ∀ i, (m i).Prime) (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    (N δ z t : ℝ) (hδ : 0 < δ) (hz : 1 < z) (hN : z ^ 4 ≤ N) (ht : 0 < t)
    (hS : S.Nonempty)
    (hinterval : ∀ n ∈ T, 0 ≤ (n : ℝ) ∧ (n : ℝ) ≤ N)
    (hsifted : ∀ n ∈ T, ∀ i, (n : ZMod (m i)) ≠ 0)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      δ ≤ dist (a i : UnitAddCircle) (a j : UnitAddCircle))
    (hlevel : ∀ i ∈ S, t ≤ ‖finiteFourierSum T b (a i)‖) :
    t ^ 2 * S.card ≤ dualRestrictionConstant * ((N + δ⁻¹) / sieveMass m z) *
      Real.log (2 * (S.card : ℝ)) * coefficientEnergy T b := by
  classical
  let F := fun i => finiteFourierSum T b (a i)
  let c := fun i => aligningPhase (F i)
  have hunit : ∀ i ∈ S, ‖c i‖ = 1 := by
    intro i hi
    apply aligningPhase_norm
    exact norm_ne_zero_iff.mp (ne_of_gt (ht.trans_le (hlevel i hi)))
  have hcard : 0 < (S.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hS
  have henergy := coefficientEnergy_unit S c hunit
  have hratio := coefficientRatio_unit S c hS hunit
  have hdu := logarithmic_sifted_dual_bound m S c a T hprime hcop
    (by rw [henergy]; exact hcard) N δ z hδ hz hN hinterval hsifted hsep
  rw [henergy, hratio] at hdu
  have hnorm : ‖∑ i ∈ S, c i * F i‖ = ∑ i ∈ S, ‖F i‖ := by
    have heq : (∑ i ∈ S, c i * F i) = ((∑ i ∈ S, ‖F i‖ : ℝ) : ℂ) := by
      simp only [c, aligningPhase_mul, Complex.ofReal_sum]
    rw [heq]
    exact Complex.norm_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg (F i))
  have hcs := finite_pairing_cauchy_sq T b (fun n => trigPolynomial S c a n)
  rw [← finiteFourier_pairing S c a T b] at hcs
  change ‖∑ i ∈ S, c i * F i‖ ^ 2 ≤ coefficientEnergy T b *
    (∑ n ∈ T, ‖trigPolynomial S c a n‖ ^ 2) at hcs
  rw [hnorm] at hcs
  have hlower : t * (S.card : ℝ) ≤ ∑ i ∈ S, ‖F i‖ := by
    calc
      _ = ∑ i ∈ S, t := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum hlevel
  have hfull := (pow_le_pow_left₀ (mul_nonneg ht.le hcard.le) hlower 2).trans
    (hcs.trans (mul_le_mul_of_nonneg_left hdu (coefficientEnergy_nonneg T b)))
  apply (mul_le_mul_iff_of_pos_right hcard).mp
  calc
    (t ^ 2 * (S.card : ℝ)) * (S.card : ℝ) = (t * (S.card : ℝ)) ^ 2 := by ring
    _ ≤ _ := hfull
    _ = _ := by ring

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/LogarithmicDistribution.lean -/
section
/- # Power bounds for logarithmic level-set inequalities -/

namespace Erdos12Proof

noncomputable def logarithmicTailConstant (p : ℝ) : ℝ :=
  (2 : ℝ) ^ (1 - 1 / p) / (1 - 1 / p)

theorem logarithmicTailConstant_pos {p : ℝ} (hp : 1 < p) :
    0 < logarithmicTailConstant p := by
  have hp0 : 0 < p := by linarith
  have hε : 0 < 1 - 1 / p := sub_pos.mpr ((div_lt_one hp0).mpr hp)
  exact div_pos (Real.rpow_pos_of_pos (by norm_num) _) hε

theorem logarithmic_level_power_bound {p m t : ℝ} (hp : 1 < p) (hm : 0 < m) (ht : 0 < t)
    (hlevel : t * m ≤ Real.log (2 * m)) :
    m ≤ (logarithmicTailConstant p / t) ^ p := by
  let ε := 1 - 1 / p
  have hp0 : 0 < p := by linarith
  have hε : 0 < ε := sub_pos.mpr ((div_lt_one hp0).mpr hp)
  have hsplit : ε + 1 / p = 1 := by dsimp [ε]; ring
  have hlog : Real.log (2 * m) ≤ m ^ ε * logarithmicTailConstant p := by
    calc
      _ ≤ (2 * m) ^ ε / ε := Real.log_le_rpow_div (by positivity) hε
      _ = _ := by
        rw [Real.mul_rpow (by norm_num) hm.le]
        dsimp [logarithmicTailConstant, ε]
        ring
  have hscaled : m ^ ε * (t * m ^ (1 / p)) ≤ m ^ ε * logarithmicTailConstant p := by
    calc
      _ = t * (m ^ ε * m ^ (1 / p)) := by ring
      _ = t * m := by rw [← Real.rpow_add hm, hsplit, Real.rpow_one]
      _ ≤ _ := hlevel.trans hlog
  have hroot : m ^ (1 / p) ≤ logarithmicTailConstant p / t := by
    apply (le_div_iff₀ ht).mpr
    simpa only [mul_comm t] using
      (mul_le_mul_iff_of_pos_left (Real.rpow_pos_of_pos hm ε)).mp hscaled
  have hpower := Real.rpow_le_rpow (Real.rpow_nonneg hm.le _) hroot hp0.le
  rw [← Real.rpow_mul hm.le, one_div_mul_cancel hp0.ne', Real.rpow_one] at hpower
  exact hpower

theorem logarithmic_threshold_le_one {m t : ℝ} (hm : 0 < m)
    (hlevel : t * m ≤ Real.log (2 * m)) : t ≤ 1 := by
  have hlog : Real.log (2 * m) ≤ m := by
    rw [Real.log_mul (by norm_num) hm.ne']
    linarith [Real.log_le_sub_one_of_pos hm,
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact (mul_le_mul_iff_of_pos_right hm).mp (by simpa only [one_mul] using hlevel.trans hlog)

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/LogarithmicLevels.lean -/
section
/- # Finite families satisfying normalized logarithmic level bounds -/

namespace Erdos12Proof

def HasLogarithmicLevels {κ : Type*} (S : Finset κ) (v : κ → ℝ) : Prop :=
  ∀ E : Finset κ, E ⊆ S → E.Nonempty → ∀ t : ℝ, 0 < t →
    (∀ i ∈ E, t ≤ v i) → t * E.card ≤ Real.log (2 * (E.card : ℝ))

theorem HasLogarithmicLevels.le_one {κ : Type*} {S : Finset κ} {v : κ → ℝ}
    (h : HasLogarithmicLevels S v) {i : κ} (hi : i ∈ S) : v i ≤ 1 := by
  classical
  by_cases hpos : 0 < v i
  · have hlevel := h {i} (Finset.singleton_subset_iff.mpr hi) (Finset.singleton_nonempty i)
      (v i) hpos (by intro j hj; have hij := Finset.mem_singleton.mp hj; subst j; exact le_rfl)
    simp only [Finset.card_singleton, Nat.cast_one, mul_one] at hlevel
    apply hlevel.trans
    have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at htwo
    exact htwo
  · exact (le_of_not_gt hpos).trans zero_le_one

theorem HasLogarithmicLevels.card_power_bound {κ : Type*} {S : Finset κ} {v : κ → ℝ}
    (h : HasLogarithmicLevels S v) {p t : ℝ} (hp : 1 < p) (ht : 0 < t) :
    ((S.filter (fun i => t ≤ v i)).card : ℝ) ≤ (logarithmicTailConstant p / t) ^ p := by
  classical
  let E := S.filter (fun i => t ≤ v i)
  by_cases hE : E.Nonempty
  · have hm : 0 < (E.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hE
    exact logarithmic_level_power_bound hp hm ht
      (h E (Finset.filter_subset _ _) hE t ht (fun i hi => (Finset.mem_filter.mp hi).2))
  · have hempty : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
    change (E.card : ℝ) ≤ _
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    exact Real.rpow_nonneg (div_nonneg (logarithmicTailConstant_pos hp).le ht.le) _

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/LogarithmicMoments.lean -/
section
/- # Moment bounds obtained by integrating logarithmic level sets -/

open MeasureTheory Set

namespace Erdos12Proof

theorem logarithmic_level_moment {κ : Type*} [Fintype κ] (v : κ → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hlevels : HasLogarithmicLevels Finset.univ v)
    {p r : ℝ} (hp : 1 < p) (hpr : p < r) :
    (∑ i, (v i) ^ r) ≤ (logarithmicTailConstant p) ^ p / (1 - p / r) := by
  classical
  let : MeasurableSpace κ := ⊤
  have hr : 0 < r := by linarith
  have hC := logarithmicTailConstant_pos hp
  have hnonneg : ∀ i, 0 ≤ (v i) ^ r := fun i => Real.rpow_nonneg (hv i) r
  have hbounded : ∀ i, (v i) ^ r ≤ 1 := fun i =>
    Real.rpow_le_one (hv i) (hlevels.le_one (Finset.mem_univ i)) hr.le
  have htail (x : ℝ) (hx : 0 < x) :
      (Measure.count : Measure κ).real {i | x ≤ (v i) ^ r} ≤
        (logarithmicTailConstant p) ^ p * x ^ (-p / r) := by
    let t := x ^ r⁻¹
    have ht : 0 < t := Real.rpow_pos_of_pos hx _
    have hsets : {i | x ≤ (v i) ^ r} =
        (↑(Finset.univ.filter (fun i => t ≤ v i)) : Set κ) := by
      ext i
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, mem_ofPred_eq]
      exact (Real.rpow_inv_le_iff_of_pos hx.le (hv i) hr).symm
    rw [hsets, measureReal_def, Measure.count_apply_finset]
    simp only [ENNReal.toReal_natCast]
    apply (hlevels.card_power_bound hp ht).trans_eq
    dsimp [t]
    rw [Real.div_rpow hC.le (Real.rpow_nonneg hx.le _) p, ← Real.rpow_mul hx.le]
    rw [div_eq_mul_inv, ← Real.rpow_neg hx.le]
    congr 1
    ring
  have hexp : -1 < -p / r := by
    have : p / r < 1 := (div_lt_one hr).mpr hpr
    rw [neg_div]
    linarith
  have hupper : IntegrableOn
      (fun x : ℝ => (logarithmicTailConstant p) ^ p * x ^ (-p / r)) (Ioc 0 1) :=
    (intervalIntegral.intervalIntegrable_rpow' hexp (a := 0) (b := 1)).1.const_mul _
  have hcake := (Integrable.of_finite (f := fun i : κ => (v i) ^ r)
    (μ := Measure.count)).integral_eq_integral_Ioc_meas_le
      (Filter.Eventually.of_forall hnonneg) (Filter.Eventually.of_forall hbounded)
  rw [integral_count] at hcake
  calc
    _ = ∫ x in Ioc (0 : ℝ) 1, (Measure.count : Measure κ).real {i | x ≤ (v i) ^ r} := hcake
    _ ≤ ∫ x in Ioc (0 : ℝ) 1, (logarithmicTailConstant p) ^ p * x ^ (-p / r) := by
      apply setIntegral_mono_of_nonneg
      · intro x _
        positivity
      · intro x hx
        exact htail x hx.1
      · exact hupper
    _ = _ := by
      rw [integral_const_mul, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        integral_rpow (Or.inl hexp)]
      rw [Real.one_rpow, Real.zero_rpow (by linarith : -p / r + 1 ≠ 0), sub_zero]
      ring

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/FiniteLogarithmicMoments.lean -/
section
/- # Moment bounds on an arbitrary finite index set -/

namespace Erdos12Proof

theorem HasLogarithmicLevels.on_subtype {κ : Type*} {S : Finset κ} {v : κ → ℝ}
    (h : HasLogarithmicLevels S v) :
    HasLogarithmicLevels (Finset.univ : Finset S) (fun i => v i) := by
  classical
  intro E _ hE t ht hbound
  let E' := E.map (Function.Embedding.subtype (fun i => i ∈ S))
  have hsub : E' ⊆ S := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
    exact j.property
  have hnonempty : E'.Nonempty := by
    obtain ⟨i, hi⟩ := hE
    exact ⟨i, Finset.mem_map.mpr ⟨i, hi, rfl⟩⟩
  have hbound' : ∀ i ∈ E', t ≤ v i := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    exact hbound j hj
  have hlevel := h E' hsub hnonempty t ht hbound'
  simpa only [E', Finset.card_map] using hlevel

theorem finite_logarithmic_level_moment {κ : Type*} (S : Finset κ) (v : κ → ℝ)
    (hv : ∀ i ∈ S, 0 ≤ v i) (hlevels : HasLogarithmicLevels S v)
    {p r : ℝ} (hp : 1 < p) (hpr : p < r) :
    (∑ i ∈ S, (v i) ^ r) ≤ (logarithmicTailConstant p) ^ p / (1 - p / r) := by
  have h := logarithmic_level_moment (fun i : S => v i) (fun i => hv i i.property)
    hlevels.on_subtype hp hpr
  rw [Finset.sum_coe_sort (s := S) (f := fun i : κ => (v i) ^ r)] at h
  exact h

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/FourierNormalization.lean -/
section
/- # Normalizing the squared Fourier values -/

namespace Erdos12Proof

variable {ι : Type*} [Fintype ι]

noncomputable def fourierEnergyScale (m : ι → ℕ) (T : Finset ℤ) (b : ℤ → ℂ)
    (N δ z : ℝ) : ℝ :=
  dualRestrictionConstant * ((N + δ⁻¹) / sieveMass m z) * coefficientEnergy T b

theorem fourierEnergyScale_pos (m : ι → ℕ) (T : Finset ℤ) (b : ℤ → ℂ)
    (hprime : ∀ i, (m i).Prime) (hb : 0 < coefficientEnergy T b)
    (N δ z : ℝ) (hδ : 0 < δ) (hz : 1 < z) (hN : z ^ 4 ≤ N) :
    0 < fourierEnergyScale m T b N δ z := by
  have hG := sieveMass_pos (fun i => (hprime i).one_lt) hz
  have hN0 : 0 < N := lt_of_lt_of_le (pow_pos (by linarith : (0 : ℝ) < z) 4) hN
  exact mul_pos (mul_pos dualRestrictionConstant_pos
    (div_pos (add_pos hN0 (inv_pos.mpr hδ)) hG)) hb

theorem fourier_normalized_log_levels {κ : Type*} (m : ι → ℕ)
    (S : Finset κ) (a : κ → ℝ) (T : Finset ℤ) (b : ℤ → ℂ)
    (hprime : ∀ i, (m i).Prime) (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    (hb : 0 < coefficientEnergy T b)
    (N δ z : ℝ) (hδ : 0 < δ) (hz : 1 < z) (hN : z ^ 4 ≤ N)
    (hinterval : ∀ n ∈ T, 0 ≤ (n : ℝ) ∧ (n : ℝ) ≤ N)
    (hsifted : ∀ n ∈ T, ∀ i, (n : ZMod (m i)) ≠ 0)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      δ ≤ dist (a i : UnitAddCircle) (a j : UnitAddCircle)) :
    HasLogarithmicLevels S
      (fun i => ‖finiteFourierSum T b (a i)‖ ^ 2 / fourierEnergyScale m T b N δ z) := by
  have hK := fourierEnergyScale_pos m T b hprime hb N δ z hδ hz hN
  intro E hES hE t ht hbound
  let level := Real.sqrt (fourierEnergyScale m T b N δ z * t)
  have hlevelpos : 0 < level := Real.sqrt_pos.mpr (mul_pos hK ht)
  have hlarge : ∀ i ∈ E, level ≤ ‖finiteFourierSum T b (a i)‖ := by
    intro i hi
    apply (Real.sqrt_le_left (norm_nonneg _)).mpr
    have h := (le_div_iff₀ hK).mp (hbound i hi)
    simpa only [mul_comm] using h
  have hlevel := fourier_level_set_bound m E a T b hprime hcop N δ z level hδ hz hN
    hlevelpos hE hinterval hsifted (fun i hi j hj hij => hsep i (hES hi) j (hES hj) hij) hlarge
  apply (mul_le_mul_iff_of_pos_left hK).mp
  calc
    fourierEnergyScale m T b N δ z * (t * E.card) = level ^ 2 * E.card := by
      dsimp [level]
      rw [Real.sq_sqrt (mul_nonneg hK.le ht.le)]
      ring
    _ ≤ _ := hlevel
    _ = _ := by unfold fourierEnergyScale; ring

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/SiftedRestriction.lean -/
section
/- # The strong restriction inequality for finite sifted sets -/

namespace Erdos12Proof

noncomputable def normalizedMomentConstant (q : ℝ) : ℝ :=
  let r := q / 2
  let p := (r + 1) / 2
  (logarithmicTailConstant p) ^ p / (1 - p / r)

theorem normalizedMomentConstant_pos {q : ℝ} (hq : 2 < q) :
    0 < normalizedMomentConstant q := by
  have hr : 1 < q / 2 := by linarith
  have hp : 1 < (q / 2 + 1) / 2 := by linarith
  have hpr : (q / 2 + 1) / 2 < q / 2 := by linarith
  unfold normalizedMomentConstant
  exact div_pos (Real.rpow_pos_of_pos (logarithmicTailConstant_pos hp) _)
    (sub_pos.mpr ((div_lt_one (by linarith)).mpr hpr))

noncomputable def restrictionMomentConstant (q : ℝ) : ℝ :=
  normalizedMomentConstant q * dualRestrictionConstant ^ (q / 2)

theorem restrictionMomentConstant_pos {q : ℝ} (hq : 2 < q) :
    0 < restrictionMomentConstant q :=
  mul_pos (normalizedMomentConstant_pos hq) (Real.rpow_pos_of_pos dualRestrictionConstant_pos _)

variable {ι : Type*} [Fintype ι]

theorem sifted_restriction_positive_energy {κ : Type*} (m : ι → ℕ)
    (S : Finset κ) (a : κ → ℝ) (T : Finset ℤ) (b : ℤ → ℂ)
    (hprime : ∀ i, (m i).Prime) (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    (hb : 0 < coefficientEnergy T b) (q : ℝ) (hq : 2 < q)
    (N δ z : ℝ) (hδ : 0 < δ) (hz : 1 < z) (hN : z ^ 4 ≤ N)
    (hinterval : ∀ n ∈ T, 0 ≤ (n : ℝ) ∧ (n : ℝ) ≤ N)
    (hsifted : ∀ n ∈ T, ∀ i, (n : ZMod (m i)) ≠ 0)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      δ ≤ dist (a i : UnitAddCircle) (a j : UnitAddCircle)) :
    (∑ i ∈ S, ‖finiteFourierSum T b (a i)‖ ^ q) ≤
      normalizedMomentConstant q * (fourierEnergyScale m T b N δ z) ^ (q / 2) := by
  let K := fourierEnergyScale m T b N δ z
  let v := fun i => ‖finiteFourierSum T b (a i)‖ ^ 2 / K
  let r := q / 2
  let p := (r + 1) / 2
  have hr : 1 < r := by dsimp [r]; linarith
  have hp : 1 < p := by dsimp [p]; linarith
  have hpr : p < r := by dsimp [p]; linarith
  have hK : 0 < K := fourierEnergyScale_pos m T b hprime hb N δ z hδ hz hN
  have hv : ∀ i ∈ S, 0 ≤ v i := fun i _ => div_nonneg (sq_nonneg _) hK.le
  have hlevels : HasLogarithmicLevels S v :=
    fourier_normalized_log_levels m S a T b hprime hcop hb N δ z hδ hz hN hinterval hsifted hsep
  have hmoment := finite_logarithmic_level_moment S v hv hlevels hp hpr
  have hterm (i : κ) : ‖finiteFourierSum T b (a i)‖ ^ q = (v i) ^ r * K ^ r := by
    calc
      _ = (‖finiteFourierSum T b (a i)‖ ^ 2) ^ r := by
        rw [← Real.rpow_two, ← Real.rpow_mul (norm_nonneg _)]
        congr 1
        dsimp [r]
        ring
      _ = (v i * K) ^ r := by rw [div_mul_cancel₀ _ hK.ne']
      _ = _ := Real.mul_rpow (div_nonneg (sq_nonneg _) hK.le) hK.le
  calc
    _ = (∑ i ∈ S, (v i) ^ r) * K ^ r := by simp only [hterm, Finset.sum_mul]
    _ ≤ ((logarithmicTailConstant p) ^ p / (1 - p / r)) * K ^ r :=
      mul_le_mul_of_nonneg_right hmoment (Real.rpow_nonneg hK.le _)
    _ = _ := rfl

theorem sifted_restriction_moment {κ : Type*} (m : ι → ℕ)
    (S : Finset κ) (a : κ → ℝ) (T : Finset ℤ) (b : ℤ → ℂ)
    (hprime : ∀ i, (m i).Prime) (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    (q : ℝ) (hq : 2 < q) (N δ z : ℝ) (hδ : 0 < δ) (hz : 1 < z) (hN : z ^ 4 ≤ N)
    (hinterval : ∀ n ∈ T, 0 ≤ (n : ℝ) ∧ (n : ℝ) ≤ N)
    (hsifted : ∀ n ∈ T, ∀ i, (n : ZMod (m i)) ≠ 0)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      δ ≤ dist (a i : UnitAddCircle) (a j : UnitAddCircle)) :
    (∑ i ∈ S, ‖finiteFourierSum T b (a i)‖ ^ q) ≤
      restrictionMomentConstant q *
        (((N + δ⁻¹) / sieveMass m z) * coefficientEnergy T b) ^ (q / 2) := by
  classical
  have hG := sieveMass_pos (fun i => (hprime i).one_lt) hz
  have hN0 : 0 < N := lt_of_lt_of_le (pow_pos (by linarith : (0 : ℝ) < z) 4) hN
  have hX : 0 ≤ ((N + δ⁻¹) / sieveMass m z) * coefficientEnergy T b :=
    mul_nonneg (div_nonneg (add_nonneg hN0.le (inv_nonneg.mpr hδ.le)) hG.le)
      (coefficientEnergy_nonneg T b)
  by_cases hb : 0 < coefficientEnergy T b
  · have h := sifted_restriction_positive_energy m S a T b hprime hcop hb q hq
      N δ z hδ hz hN hinterval hsifted hsep
    convert h using 1
    unfold fourierEnergyScale restrictionMomentConstant
    rw [mul_assoc dualRestrictionConstant ((N + δ⁻¹) / sieveMass m z) (coefficientEnergy T b),
      Real.mul_rpow dualRestrictionConstant_pos.le hX]
    ring
  · have hzero : coefficientEnergy T b = 0 := le_antisymm (le_of_not_gt hb) (coefficientEnergy_nonneg T b)
    have hbzero : ∀ n ∈ T, b n = 0 := by
      intro n hn
      have hle := Finset.single_le_sum (fun i _ => sq_nonneg ‖b i‖) hn
      have hs : ‖b n‖ ^ 2 = 0 := by
        change ‖b n‖ ^ 2 ≤ coefficientEnergy T b at hle
        linarith [sq_nonneg ‖b n‖]
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hs)
    have hFzero : ∀ x, finiteFourierSum T b x = 0 := by
      intro x
      exact Finset.sum_eq_zero (fun n hn => by rw [hbzero n hn, zero_mul])
    simp only [hFzero, norm_zero, Real.zero_rpow (by linarith : q ≠ 0), Finset.sum_const_zero]
    exact mul_nonneg (restrictionMomentConstant_pos hq).le (Real.rpow_nonneg hX _)

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/RestrictionNorm.lean -/
section
/- # The restriction estimate in its norm form -/

namespace Erdos12Proof

theorem sifted_restriction_lq {ι κ : Type*} [Fintype ι] (m : ι → ℕ)
    (S : Finset κ) (a : κ → ℝ) (T : Finset ℤ) (b : ℤ → ℂ)
    (hprime : ∀ i, (m i).Prime) (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    (q : ℝ) (hq : 2 < q) (N δ z : ℝ) (hδ : 0 < δ) (hz : 1 < z) (hN : z ^ 4 ≤ N)
    (hinterval : ∀ n ∈ T, 0 ≤ (n : ℝ) ∧ (n : ℝ) ≤ N)
    (hsifted : ∀ n ∈ T, ∀ i, (n : ZMod (m i)) ≠ 0)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      δ ≤ dist (a i : UnitAddCircle) (a j : UnitAddCircle)) :
    (∑ i ∈ S, ‖finiteFourierSum T b (a i)‖ ^ q) ^ (1 / q) ≤
      (restrictionMomentConstant q) ^ (1 / q) *
        Real.sqrt (((N + δ⁻¹) / sieveMass m z) * coefficientEnergy T b) := by
  have hq0 : 0 < q := by linarith
  have hG := sieveMass_pos (fun i => (hprime i).one_lt) hz
  have hN0 : 0 < N := lt_of_lt_of_le (pow_pos (by linarith : (0 : ℝ) < z) 4) hN
  have hX : 0 ≤ ((N + δ⁻¹) / sieveMass m z) * coefficientEnergy T b :=
    mul_nonneg (div_nonneg (add_nonneg hN0.le (inv_nonneg.mpr hδ.le)) hG.le)
      (coefficientEnergy_nonneg T b)
  have hmoment := sifted_restriction_moment m S a T b hprime hcop q hq
    N δ z hδ hz hN hinterval hsifted hsep
  have h := Real.rpow_le_rpow
    (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) q)) hmoment
    (one_div_pos.mpr hq0).le
  have hexponent : (q / 2) * (1 / q) = (1 / 2 : ℝ) := by field_simp
  rw [Real.mul_rpow (restrictionMomentConstant_pos hq).le (Real.rpow_nonneg hX (q / 2)),
    ← Real.rpow_mul hX, hexponent, ← Real.sqrt_eq_rpow] at h
  exact h

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/FiniteFourierNorms.lean -/
section
/- # Finite counting-measure norms used in the Fourier comparison -/

namespace Erdos12Proof

noncomputable def finiteLqNorm {κ : Type*} (S : Finset κ) (f : κ → ℂ) (q : ℝ) : ℝ :=
  (∑ i ∈ S, ‖f i‖ ^ q) ^ (1 / q)

theorem finiteLqNorm_nonneg {κ : Type*} (S : Finset κ) (f : κ → ℂ) (q : ℝ) :
    0 ≤ finiteLqNorm S f q :=
  Real.rpow_nonneg (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg (f i)) _)) _

theorem finiteLqNorm_holder {κ : Type*} (S : Finset κ) (f g : κ → ℂ)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    ‖∑ i ∈ S, f i * g i‖ ≤ finiteLqNorm S f p * finiteLqNorm S g q := by
  calc
    _ ≤ ∑ i ∈ S, ‖f i * g i‖ := norm_sum_le _ _
    _ = ∑ i ∈ S, ‖f i‖ * ‖g i‖ := by simp only [norm_mul]
    _ ≤ _ := Real.inner_le_Lp_mul_Lq_of_nonneg (s := S)
      hpq (fun i _ => norm_nonneg (f i)) (fun i _ => norm_nonneg (g i))

theorem finiteLqNorm_interpolate {κ : Type*} (S : Finset κ) (f : κ → ℂ)
    {p q U : ℝ} (hq : 0 < q) (hpq : q < p) (hU : 0 ≤ U)
    (hf : ∀ i ∈ S, ‖f i‖ ≤ U) :
    finiteLqNorm S f p ≤ U ^ (1 - q / p) * (finiteLqNorm S f q) ^ (q / p) := by
  have hp : 0 < p := hq.trans hpq
  have hqsum : 0 ≤ ∑ i ∈ S, ‖f i‖ ^ q :=
    Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hsum : (∑ i ∈ S, ‖f i‖ ^ p) ≤ U ^ (p - q) * ∑ i ∈ S, ‖f i‖ ^ q := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hsplit : ‖f i‖ ^ p = ‖f i‖ ^ (p - q) * ‖f i‖ ^ q := by
      by_cases hzero : ‖f i‖ = 0
      · simp [hzero, hp.ne', hq.ne', (sub_pos.mpr hpq).ne']
      · rw [← Real.rpow_add (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)), sub_add_cancel]
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (norm_nonneg _) (hf i hi) (sub_pos.mpr hpq).le)
      (Real.rpow_nonneg (norm_nonneg _) _)
  have hroot := Real.rpow_le_rpow
    (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)) hsum (one_div_pos.mpr hp).le
  have hexpU : (p - q) * (1 / p) = 1 - q / p := by field_simp
  have hexpSum : (1 / q) * (q / p) = 1 / p := by field_simp
  rw [Real.mul_rpow (Real.rpow_nonneg hU _) hqsum, ← Real.rpow_mul hU, hexpU] at hroot
  calc
    _ ≤ U ^ (1 - q / p) * (∑ i ∈ S, ‖f i‖ ^ q) ^ (1 / p) := hroot
    _ = _ := by unfold finiteLqNorm; rw [← Real.rpow_mul hqsum, hexpSum]

theorem norm_le_finiteLqNorm {κ : Type*} (S : Finset κ) (f : κ → ℂ) {q : ℝ}
    (hq : 0 < q) {i : κ} (hi : i ∈ S) : ‖f i‖ ≤ finiteLqNorm S f q := by
  have hsum := Finset.single_le_sum (fun j _ => Real.rpow_nonneg (norm_nonneg (f j)) q) hi
  have h := Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg (f i)) q) hsum
    (one_div_pos.mpr hq).le
  rw [← Real.rpow_mul (norm_nonneg (f i)), mul_one_div_cancel hq.ne', Real.rpow_one] at h
  exact h

theorem finiteLqNorm_mono_exponent {κ : Type*} (S : Finset κ) (f : κ → ℂ)
    {p q : ℝ} (hq : 0 < q) (hpq : q < p) : finiteLqNorm S f p ≤ finiteLqNorm S f q := by
  have h := finiteLqNorm_interpolate S f hq hpq (finiteLqNorm_nonneg S f q)
    (fun i hi => norm_le_finiteLqNorm S f hq hi)
  have hexp : 1 - q / p + q / p = (1 : ℝ) := by ring
  rw [← Real.rpow_add' (finiteLqNorm_nonneg S f q) (by rw [hexp]; norm_num),
    hexp, Real.rpow_one] at h
  exact h

theorem finiteLqNorm_sub_le {κ : Type*} (S : Finset κ) (f g : κ → ℂ)
    {q : ℝ} (hq : 1 ≤ q) :
    finiteLqNorm S (fun i => f i - g i) q ≤ finiteLqNorm S f q + finiteLqNorm S g q := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  calc
    _ ≤ (∑ i ∈ S, (‖f i‖ + ‖g i‖) ^ q) ^ (1 / q) := by
      apply Real.rpow_le_rpow
      · exact Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)
      · exact Finset.sum_le_sum (fun i _ => Real.rpow_le_rpow (norm_nonneg _) (norm_sub_le _ _) hq0.le)
      · exact (one_div_pos.mpr hq0).le
    _ ≤ _ := Real.Lp_add_le_of_nonneg (s := S) hq
      (fun i _ => norm_nonneg (f i)) (fun i _ => norm_nonneg (g i))

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/CyclicIntegerFourier.lean -/
section
/- # Integer sums and their normalized cyclic Fourier transforms -/

namespace Erdos12Proof

variable {M : ℕ} [NeZero M]

noncomputable def cyclicFrequency (k : ZMod M) : ℝ := -(k.val : ℝ) / M

theorem cyclicFrequency_circle (k : ZMod M) :
    (cyclicFrequency k : UnitAddCircle) = -ZMod.toAddCircle k := by
  rw [ZMod.toAddCircle_apply, cyclicFrequency, neg_div, AddCircle.coe_neg]

theorem cyclicFrequency_separated {k l : ZMod M} (hkl : k ≠ l) :
    1 / (M : ℝ) ≤ dist (cyclicFrequency k : UnitAddCircle) (cyclicFrequency l : UnitAddCircle) := by
  have hval : 0 < (k - l).val := by
    apply Nat.pos_of_ne_zero
    intro h
    have hz : k - l = 0 := (ZMod.val_eq_zero _).mp h
    exact hkl (sub_eq_zero.mp hz)
  have hnot : ¬M ∣ (k - l).val := Nat.not_dvd_of_pos_of_lt hval (ZMod.val_lt _)
  have h := circle_norm_nat_fraction (NeZero.pos M) hnot
  rw [cyclicFrequency_circle, cyclicFrequency_circle, dist_neg_neg, dist_eq_norm,
    ← map_sub, ZMod.toAddCircle_apply]
  exact h

theorem cyclicCharacter_integer (n : ℤ) (k : ZMod M) :
    ZMod.stdAddChar (-((n : ZMod M) * k)) = unitExp ((n : ℝ) * cyclicFrequency k) := by
  have hcast : -((n : ZMod M) * k) = ((-n * (k.val : ℤ) : ℤ) : ZMod M) := by
    push_cast
    rw [ZMod.natCast_zmod_val]
    ring
  rw [hcast, ZMod.stdAddChar_coe]
  unfold unitExp cyclicFrequency
  congr 1
  push_cast
  ring

noncomputable def integerCyclicLift (T : Finset ℤ) (b : ℤ → ℂ) : ZMod M → ℂ :=
  finitePushforward (fun n : T => (n.val : ZMod M)) (fun n : T => b n)

theorem integerCyclicLift_fourier (T : Finset ℤ) (b : ℤ → ℂ) (k : ZMod M) :
    cyclicFourier (integerCyclicLift T b) k =
      (M : ℂ)⁻¹ * finiteFourierSum T b (cyclicFrequency k) := by
  classical
  unfold cyclicFourier integerCyclicLift
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul]
  rw [finitePushforward_weighted_sum]
  congr 1
  simp only [cyclicCharacter_integer]
  rw [Finset.sum_coe_sort (s := T)
    (f := fun n : ℤ => unitExp ((n : ℝ) * cyclicFrequency k) * b n)]
  unfold finiteFourierSum
  apply Finset.sum_congr rfl
  intro n _
  rw [mul_comm (n : ℝ), mul_comm]

theorem integerCyclicLift_fourier_norm (T : Finset ℤ) (b : ℤ → ℂ) (k : ZMod M) :
    ‖cyclicFourier (integerCyclicLift T b) k‖ =
      (M : ℝ)⁻¹ * ‖finiteFourierSum T b (cyclicFrequency k)‖ := by
  rw [integerCyclicLift_fourier, norm_mul, norm_inv]
  simp only [Complex.norm_natCast]

theorem finiteLqNorm_const_mul {κ : Type*} (S : Finset κ) (f : κ → ℂ)
    (c : ℂ) {q : ℝ} (hq : 0 < q) :
    finiteLqNorm S (fun i => c * f i) q = ‖c‖ * finiteLqNorm S f q := by
  unfold finiteLqNorm
  simp only [norm_mul, Real.mul_rpow (norm_nonneg c) (norm_nonneg _), ← Finset.mul_sum]
  rw [Real.mul_rpow (Real.rpow_nonneg (norm_nonneg c) q)
    (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg (f i)) q)),
    ← Real.rpow_mul (norm_nonneg c)]
  rw [mul_one_div_cancel hq.ne', Real.rpow_one]

theorem integerCyclicLift_fourier_lq (T : Finset ℤ) (b : ℤ → ℂ)
    (S : Finset (ZMod M)) {q : ℝ} (hq : 0 < q) :
    finiteLqNorm S (cyclicFourier (integerCyclicLift T b)) q =
      (M : ℝ)⁻¹ * finiteLqNorm S (fun k => finiteFourierSum T b (cyclicFrequency k)) q := by
  have hfun : cyclicFourier (integerCyclicLift (M := M) T b) =
      fun k => (M : ℂ)⁻¹ * finiteFourierSum T b (cyclicFrequency k) := by
    funext k
    exact integerCyclicLift_fourier T b k
  rw [hfun, finiteLqNorm_const_mul S _ _ hq, norm_inv]
  simp only [Complex.norm_natCast]

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/RationalApproximation.lean -/
section
/- # Reduced rational approximations from a short return on the circle -/

namespace Erdos12Proof

theorem circle_norm_int_fraction {a : ℤ} {d : ℕ} (hd : 0 < d)
    (hnot : ¬(d : ℤ) ∣ a) :
    1 / (d : ℝ) ≤ ‖(((a : ℝ) / d : ℝ) : UnitAddCircle)‖ := by
  let : NeZero d := ⟨hd.ne'⟩
  have hx : (a : ZMod d) ≠ 0 := by
    intro hzero
    exact hnot ((ZMod.intCast_zmod_eq_zero_iff_dvd a d).mp hzero)
  have hval : 0 < (a : ZMod d).val := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact hx ((ZMod.val_eq_zero _).mp hz)
  have hndvd : ¬d ∣ (a : ZMod d).val :=
    Nat.not_dvd_of_pos_of_lt hval (ZMod.val_lt _)
  rw [← ZMod.toAddCircle_intCast, ZMod.toAddCircle_apply]
  exact circle_norm_nat_fraction hd hndvd

theorem circle_norm_rational_mul (q : ℚ) {h : ℕ} (hh : 0 < h) (hhd : h < q.den) :
    1 / (q.den : ℝ) ≤ ‖(((h : ℝ) * q : ℝ) : UnitAddCircle)‖ := by
  have hnot : ¬(q.den : ℤ) ∣ (h : ℤ) * q.num := by
    rw [Int.natCast_dvd, Int.natAbs_mul, Int.natAbs_natCast]
    intro hdiv
    have hdh := q.reduced.symm.dvd_of_dvd_mul_right hdiv
    exact (Nat.not_dvd_of_pos_of_lt hh hhd) hdh
  have hbase := circle_norm_int_fraction q.den_pos hnot
  simpa only [Int.cast_mul, Int.cast_natCast, Rat.cast_def, mul_div_assoc] using hbase

theorem reduced_approximation_of_short_return {h : ℕ} (hh : 0 < h) (θ ε : ℝ)
    (hreturn : ‖(((h : ℝ) * θ : ℝ) : UnitAddCircle)‖ ≤ ε) :
    ∃ q : ℚ, q.den ≤ h ∧ |θ - (q : ℝ)| ≤ ε / q.den := by
  let r : ℤ := round ((h : ℝ) * θ)
  let q : ℚ := Rat.divInt r (h : ℤ)
  have hhR : 0 < (h : ℝ) := by exact_mod_cast hh
  have hdenDvd : q.den ∣ h := by
    have hdiv := Rat.den_dvd r (h : ℤ)
    exact_mod_cast hdiv
  have hden : q.den ≤ h := Nat.le_of_dvd hh hdenDvd
  have hε : 0 ≤ ε := (norm_nonneg _).trans hreturn
  have hqcast : (q : ℝ) = (r : ℝ) / h := by
    simp only [q, Rat.cast_divInt, Int.cast_natCast]
  have herror : |θ - (q : ℝ)| = ‖(((h : ℝ) * θ : ℝ) : UnitAddCircle)‖ / h := by
    rw [hqcast, UnitAddCircle.norm_eq]
    have hid : θ - (r : ℝ) / h = ((h : ℝ) * θ - r) / h := by field_simp
    rw [hid, abs_div, abs_of_pos hhR]
  refine ⟨q, hden, ?_⟩
  rw [herror]
  exact (div_le_div_of_nonneg_right hreturn hhR.le).trans
    (div_le_div_of_nonneg_left hε (by exact_mod_cast q.den_pos) (by exact_mod_cast hden))

theorem reduced_rational_orbit_spacing (q : ℚ) {h : ℕ} (hh : 0 < h)
    (hhd : h < q.den) {β : ℝ} (hβ : |β| ≤ 1 / (2 * (q.den : ℝ) ^ 2)) :
    1 / (2 * (q.den : ℝ)) ≤
      ‖(((h : ℝ) * ((q : ℝ) + β) : ℝ) : UnitAddCircle)‖ := by
  have hdR : 0 < (q.den : ℝ) := by exact_mod_cast q.den_pos
  have hbase := circle_norm_rational_mul q hh hhd
  have herror : |(h : ℝ) * β| ≤ 1 / (2 * (q.den : ℝ)) := by
    calc
      _ = (h : ℝ) * |β| := by rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg h)]
      _ ≤ (q.den : ℝ) * (1 / (2 * (q.den : ℝ) ^ 2)) :=
        mul_le_mul (by exact_mod_cast hhd.le) hβ (abs_nonneg _) hdR.le
      _ = _ := by field_simp
  have htri := circle_norm_perturbation ((h : ℝ) * q) ((h : ℝ) * β)
  rw [← mul_add] at htri
  have hhalf : 1 / (q.den : ℝ) = 2 * (1 / (2 * (q.den : ℝ))) := by ring
  rw [hhalf] at hbase
  linarith

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/GridSmoothing.lean -/
section
/- # Complete-cell smoothing of a finite arithmetic grid -/

namespace Erdos12Proof

theorem finiteMean_sub {Ω : Type*} [Fintype Ω] (f g : Ω → ℂ) :
    finiteMean (fun x => f x - g x) = finiteMean f - finiteMean g := by
  simp only [finiteMean, Finset.sum_sub_distrib, sub_div]

theorem finiteMean_product {K α β : Type*} [Field K] [Fintype α] [Fintype β] (f : α → β → K) :
    finiteMean (fun p : α × β => f p.1 p.2) = finiteMean (fun x => finiteMean (f x)) := by
  simp only [finiteMean, Fintype.card_prod, Fintype.sum_prod_type, Nat.cast_mul,
    Finset.sum_div, div_div]
  rw [mul_comm (Fintype.card α : K)]

theorem norm_finiteMean_le {Ω : Type*} [Fintype Ω] (f : Ω → ℂ) :
    ‖finiteMean f‖ ≤ finiteMean (fun x => ‖f x‖) := by
  unfold finiteMean
  rw [norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right (norm_sum_le _ _) (Nat.cast_nonneg _)

theorem norm_finiteMean_le_bound {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℂ) {C : ℝ} (hf : ∀ x, ‖f x‖ ≤ C) : ‖finiteMean f‖ ≤ C := by
  calc
    _ ≤ finiteMean (fun x => ‖f x‖) := norm_finiteMean_le f
    _ ≤ finiteMean (fun _ : Ω => C) := finiteMean_mono hf
    _ = C := finiteMean_const C

theorem unitExp_mean_norm_le_one {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (t : Ω → ℝ) : ‖finiteMean (fun x => unitExp (t x))‖ ≤ 1 := by
  exact norm_finiteMean_le_bound _ (fun x => (unitExp_norm (t x)).le)

theorem unitExp_mean_close_to_one {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (t : Ω → ℝ) {A : ℝ} (hA : ∀ x, |t x| ≤ A) :
    ‖finiteMean (fun x => unitExp (t x)) - 1‖ ≤ 2 * Real.pi * A := by
  rw [← finiteMean_const (Ω := Ω) (1 : ℂ), ← finiteMean_sub]
  apply norm_finiteMean_le_bound
  intro x
  exact (unitExp_sub_one_bound (t x)).trans
    (mul_le_mul_of_nonneg_left (hA x) (by positivity))

noncomputable def gridPhaseAverage (a start length : ℕ) (t : ℝ) : ℂ :=
  finiteMean (fun k : Fin length => unitExp (((a * (start + k.val) : ℕ) : ℝ) * t))

noncomputable def cellPhaseAverage (a start length : ℕ) (t : ℝ) : ℂ :=
  finiteMean (fun k : Fin length => finiteMean (fun j : Fin a =>
    unitExp (((a * (start + k.val) + j.val : ℕ) : ℝ) * t)))

theorem cellPhaseAverage_factor (a start length : ℕ) (t : ℝ) :
    cellPhaseAverage a start length t = gridPhaseAverage a start length t *
      finiteMean (fun j : Fin a => unitExp ((j.val : ℝ) * t)) := by
  have hphase (k : Fin length) (j : Fin a) :
      unitExp (((a * (start + k.val) + j.val : ℕ) : ℝ) * t) =
        unitExp (((a * (start + k.val) : ℕ) : ℝ) * t) * unitExp ((j.val : ℝ) * t) := by
    rw [Nat.cast_add, add_mul, unitExp_add]
  simp only [cellPhaseAverage, hphase, finiteMean_const_mul, finiteMean_mul_const,
    gridPhaseAverage]

theorem gridPhaseAverage_norm_le_one (a start : ℕ) {length : ℕ} (hL : 0 < length) (t : ℝ) :
    ‖gridPhaseAverage a start length t‖ ≤ 1 := by
  let : NeZero length := ⟨hL.ne'⟩
  exact unitExp_mean_norm_le_one _

theorem cellPhaseAverage_close (start : ℕ) {a length : ℕ} (ha : 0 < a) (hL : 0 < length)
    (t : ℝ) :
    ‖gridPhaseAverage a start length t - cellPhaseAverage a start length t‖ ≤
      2 * Real.pi * (a : ℝ) * |t| := by
  let : NeZero a := ⟨ha.ne'⟩
  have hsmall := unitExp_mean_close_to_one (fun j : Fin a => (j.val : ℝ) * t)
    (A := (a : ℝ) * |t|) (fun j => by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast j.isLt.le) (abs_nonneg t))
  rw [cellPhaseAverage_factor]
  rw [show gridPhaseAverage a start length t -
      gridPhaseAverage a start length t * finiteMean (fun j : Fin a => unitExp ((j.val : ℝ) * t)) =
      gridPhaseAverage a start length t *
        (1 - finiteMean (fun j : Fin a => unitExp ((j.val : ℝ) * t))) by ring,
    norm_mul, norm_sub_rev]
  calc
    _ ≤ 1 * (2 * Real.pi * ((a : ℝ) * |t|)) :=
      mul_le_mul (gridPhaseAverage_norm_le_one a start hL t) hsmall (norm_nonneg _) zero_le_one
    _ = _ := by ring

theorem cellPhaseAverage_eq_interval (a start length : ℕ) (t : ℝ) :
    cellPhaseAverage a start length t =
      finiteMean (fun n : Fin (length * a) => unitExp (((a * start + n.val : ℕ) : ℝ) * t)) := by
  rw [cellPhaseAverage, ← finiteMean_product]
  have h := finiteMean_equiv (finProdFinEquiv : Fin length × Fin a ≃ Fin (length * a))
    (fun n => unitExp (((a * start + n.val : ℕ) : ℝ) * t))
  rw [← h]
  congr 1
  funext p
  congr 2
  change ((a * (start + p.1.val) + p.2.val : ℕ) : ℝ) =
    ((a * start + (p.2.val + a * p.1.val) : ℕ) : ℝ)
  push_cast
  ring

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/GridGeometricBounds.lean -/
section
/- # Geometric estimates for the grid and its complete-cell smoothing -/

namespace Erdos12Proof

noncomputable def intervalPhaseMean (start length : ℕ) (t : ℝ) : ℂ :=
  finiteMean (fun k : Fin length => unitExp (((start + k.val : ℕ) : ℝ) * t))

theorem intervalPhaseMean_factor (start length : ℕ) (t : ℝ) :
    intervalPhaseMean start length t = unitExp ((start : ℝ) * t) *
      finiteMean (fun k : Fin length => unitExp ((k.val : ℝ) * t)) := by
  simp only [intervalPhaseMean, Nat.cast_add, add_mul, unitExp_add, finiteMean_const_mul]

theorem intervalPhaseMean_far (start : ℕ) {length : ℕ} (hL : 0 < length)
    (t : ℝ) (ht : 0 < ‖(t : UnitAddCircle)‖) :
    ‖intervalPhaseMean start length t‖ ≤
      1 / (2 * (length : ℝ) * ‖(t : UnitAddCircle)‖) := by
  have hnot : ¬∃ n : ℤ, (n : ℝ) = t := by
    rintro ⟨n, hn⟩
    have hdist : 0 < AnalyticNumberTheory.LargeSieve.distToInt t := by
      simpa only [distToInt_eq_circle_norm] using ht
    rw [← hn] at hdist
    simp [AnalyticNumberTheory.LargeSieve.distToInt] at hdist
  have hsum := AnalyticNumberTheory.LargeSieve.geomSum_exp_bound_far length hnot
  simp only [← unitExp_eq_charReal, distToInt_eq_circle_norm] at hsum
  rw [intervalPhaseMean_factor, norm_mul, unitExp_norm, one_mul, finiteMean,
    norm_div, Complex.norm_natCast, Fintype.card_fin,
    Fin.sum_univ_eq_sum_range (fun k => unitExp ((k : ℝ) * t))]
  have h := div_le_div_of_nonneg_right hsum
    (show (0 : ℝ) ≤ (length : ℝ) by exact_mod_cast hL.le)
  convert h using 1
  ring

theorem gridPhaseAverage_eq_interval (a start length : ℕ) (t : ℝ) :
    gridPhaseAverage a start length t = intervalPhaseMean start length ((a : ℝ) * t) := by
  unfold gridPhaseAverage intervalPhaseMean
  congr 1
  funext k
  congr 1
  push_cast
  ring

theorem gridPhaseAverage_far (a start : ℕ) {length : ℕ} (hL : 0 < length)
    (t : ℝ) (ht : 0 < ‖(((a : ℝ) * t : ℝ) : UnitAddCircle)‖) :
    ‖gridPhaseAverage a start length t‖ ≤
      1 / (2 * (length : ℝ) * ‖(((a : ℝ) * t : ℝ) : UnitAddCircle)‖) := by
  rw [gridPhaseAverage_eq_interval]
  exact intervalPhaseMean_far start hL _ ht

theorem cellPhaseAverage_eq_intervalMean (a start length : ℕ) (t : ℝ) :
    cellPhaseAverage a start length t = intervalPhaseMean (a * start) (length * a) t :=
  cellPhaseAverage_eq_interval a start length t

theorem cellPhaseAverage_far (start : ℕ) {a length : ℕ} (ha : 0 < a) (hL : 0 < length)
    (t : ℝ) (ht : 0 < ‖(t : UnitAddCircle)‖) :
    ‖cellPhaseAverage a start length t‖ ≤
      1 / (2 * (length : ℝ) * a * ‖(t : UnitAddCircle)‖) := by
  rw [cellPhaseAverage_eq_intervalMean]
  have h := intervalPhaseMean_far (a * start) (Nat.mul_pos hL ha) t ht
  simpa only [Nat.cast_mul, mul_assoc] using h

theorem gridPhaseAverage_small_phase (start : ℕ) {a length : ℕ}
    (ha : 0 < a) (hL : 0 < length) (t : ℝ) (ht : 0 < |t|)
    (hsmall : (a : ℝ) * |t| ≤ 1 / 2) :
    ‖gridPhaseAverage a start length t‖ ≤ 1 / (2 * (length : ℝ) * a * |t|) := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have habs : |(a : ℝ) * t| = (a : ℝ) * |t| := by
    rw [abs_mul, abs_of_pos haR]
  have hnorm : ‖(((a : ℝ) * t : ℝ) : UnitAddCircle)‖ = (a : ℝ) * |t| := by
    rw [(AddCircle.norm_coe_eq_abs_iff (p := 1) one_ne_zero).mpr (by simpa only [abs_one, habs] using hsmall)]
    exact habs
  have h := gridPhaseAverage_far a start hL t (by rw [hnorm]; exact mul_pos haR ht)
  simpa only [hnorm, mul_assoc] using h

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/Sifting.lean -/
section
/- # Rough and smooth factorizations used by the two-block argument -/

namespace Erdos12Proof

def Rough (D : ℝ) (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → D < p

def Smooth (D : ℝ) (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ D

theorem rough_one (D : ℝ) : Rough D 1 := by
  intro p hp hdiv
  exact False.elim (hp.not_dvd_one hdiv)

theorem smooth_one (D : ℝ) : Smooth D 1 := by
  intro p hp hdiv
  exact False.elim (hp.not_dvd_one hdiv)

theorem Rough.of_dvd {D : ℝ} {a b : ℕ} (hb : Rough D b) (hab : a ∣ b) : Rough D a := by
  intro p hp hpa
  exact hb p hp (dvd_trans hpa hab)

theorem Smooth.of_dvd {D : ℝ} {a b : ℕ} (hb : Smooth D b) (hab : a ∣ b) : Smooth D a := by
  intro p hp hpa
  exact hb p hp (dvd_trans hpa hab)

theorem Smooth.mul {D : ℝ} {a b : ℕ} (ha : Smooth D a) (hb : Smooth D b) :
    Smooth D (a * b) := by
  intro p hp hdiv
  rcases hp.dvd_mul.mp hdiv with hpa | hpb
  · exact ha p hp hpa
  · exact hb p hp hpb

theorem smooth_of_le {D : ℝ} {a : ℕ} (ha : 0 < a) (hD : (a : ℝ) ≤ D) : Smooth D a := by
  intro p _ hpa
  exact le_trans (by exact_mod_cast Nat.le_of_dvd ha hpa) hD

theorem Rough.coprime_smooth {D : ℝ} {a b : ℕ} (ha : Rough D a) (hb : Smooth D b) :
    a.Coprime b := by
  apply Nat.coprime_of_dvd
  intro p hp hpa hpb
  exact (not_lt_of_ge (hb p hp hpb)) (ha p hp hpa)

theorem eq_one_of_rough_smooth {D : ℝ} {a : ℕ} (ha : Rough D a) (ha' : Smooth D a) :
    a = 1 := by
  have hcop := ha.coprime_smooth ha'
  simpa only [Nat.coprime_self] using hcop

theorem rough_factor_unique {D : ℝ} {a b d e : ℕ}
    (ha : Rough D a) (hb : Rough D b) (hd : Smooth D d) (he : Smooth D e)
    (ha0 : 0 < a) (hb0 : 0 < b) (hprod : d * a = e * b) : a = b := by
  have hab : a ∣ b := by
    apply (ha.coprime_smooth he).dvd_of_dvd_mul_left
    rw [← hprod]
    exact dvd_mul_left a d
  have hba : b ∣ a := by
    apply (hb.coprime_smooth hd).dvd_of_dvd_mul_left
    rw [hprod]
    exact dvd_mul_left b e
  exact Nat.le_antisymm (Nat.le_of_dvd hb0 hab) (Nat.le_of_dvd ha0 hba)

theorem forbidden_smooth_multiple_sum {D : ℝ} {A : Set ℕ} (hA : PropertyP A)
    {a x y k : ℕ} (ha : a ∈ A) (hx : x ∈ A) (hy : y ∈ A)
    (hax : a < x) (hay : a < y) (hk : 1 < k)
    (hxRough : Rough D x) (hkSmooth : Smooth D k) : x + y ≠ 2 * k * a := by
  intro hsum
  have haSum : a ∣ x + y := by
    rw [hsum]
    exact dvd_mul_left a (2 * k)
  have hxy := hA ha hx hy haSum hax hay
  have hxmul : x = k * a := by
    rw [← hxy] at hsum
    nlinarith
  have hkx : k ∣ x := by
    rw [hxmul]
    exact dvd_mul_right k a
  have hkOne := eq_one_of_rough_smooth (hxRough.of_dvd hkx) hkSmooth
  omega

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/RationalGridBounds.lean -/
section
/- # Geometric bounds near a reduced rational frequency -/

namespace Erdos12Proof

theorem circle_norm_rational_unit_mul (q : ℚ) {a : ℕ}
    (ha : a.Coprime q.den) (hd : 1 < q.den) :
    1 / (q.den : ℝ) ≤ ‖(((a : ℝ) * q : ℝ) : UnitAddCircle)‖ := by
  have hnot : ¬(q.den : ℤ) ∣ (a : ℤ) * q.num := by
    rw [Int.natCast_dvd, Int.natAbs_mul, Int.natAbs_natCast]
    intro hdiv
    have hda := q.reduced.symm.dvd_of_dvd_mul_right hdiv
    have hdone := Nat.eq_one_of_dvd_coprimes ha hda (dvd_refl q.den)
    omega
  have hbase := circle_norm_int_fraction q.den_pos hnot
  simpa only [Int.cast_mul, Int.cast_natCast, Rat.cast_def, mul_div_assoc] using hbase

theorem circle_norm_rational_unit_perturbation (q : ℚ) {a : ℕ}
    (ha : a.Coprime q.den) (hd : 1 < q.den) (β : ℝ)
    (hβ : |(a : ℝ) * β| ≤ 1 / (2 * (q.den : ℝ))) :
    1 / (2 * (q.den : ℝ)) ≤
      ‖(((a : ℝ) * ((q : ℝ) + β) : ℝ) : UnitAddCircle)‖ := by
  have hbase := circle_norm_rational_unit_mul q ha hd
  have htri := circle_norm_perturbation ((a : ℝ) * q) ((a : ℝ) * β)
  rw [← mul_add] at htri
  have hhalf : 1 / (q.den : ℝ) = 2 * (1 / (2 * (q.den : ℝ))) := by ring
  rw [hhalf] at hbase
  linarith

theorem gridPhaseAverage_of_norm_lower (a start : ℕ) {length : ℕ} (hL : 0 < length)
    (t δ : ℝ) (hδ : 0 < δ)
    (ht : δ ≤ ‖(((a : ℝ) * t : ℝ) : UnitAddCircle)‖) :
    ‖gridPhaseAverage a start length t‖ ≤ 1 / (2 * (length : ℝ) * δ) := by
  have hLR : 0 < (length : ℝ) := by exact_mod_cast hL
  exact (gridPhaseAverage_far a start hL t (hδ.trans_le ht)).trans
    (one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left ht (by positivity)))

theorem gridPhaseAverage_near_rational {D : ℝ} {a length : ℕ} (ha : Rough D a)
    (hL : 0 < length) (start : ℕ) (q : ℚ) (hd : 1 < q.den)
    (hden : (q.den : ℝ) ≤ D) (β : ℝ)
    (hβ : |(a : ℝ) * β| ≤ 1 / (2 * (q.den : ℝ))) :
    ‖gridPhaseAverage a start length ((q : ℝ) + β)‖ ≤ (q.den : ℝ) / length := by
  have hdR : 0 < (q.den : ℝ) := by exact_mod_cast q.den_pos
  have hcop := ha.coprime_smooth (smooth_of_le q.den_pos hden)
  have hnorm := circle_norm_rational_unit_perturbation q hcop hd β hβ
  have h := gridPhaseAverage_of_norm_lower a start hL ((q : ℝ) + β)
    (1 / (2 * (q.den : ℝ))) (by positivity) hnorm
  convert h using 1
  field_simp

theorem cellPhaseAverage_of_norm_lower (start : ℕ) {a length : ℕ}
    (ha : 0 < a) (hL : 0 < length) (t δ : ℝ) (hδ : 0 < δ)
    (ht : δ ≤ ‖(t : UnitAddCircle)‖) :
    ‖cellPhaseAverage a start length t‖ ≤ 1 / (2 * (length : ℝ) * a * δ) := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hLR : 0 < (length : ℝ) := by exact_mod_cast hL
  exact (cellPhaseAverage_far start ha hL t (hδ.trans_le ht)).trans
    (one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left ht (by positivity)))

theorem cellPhaseAverage_near_rational (start : ℕ) {a length : ℕ}
    (ha : 0 < a) (hL : 0 < length) (q : ℚ) (hd : 1 < q.den)
    (β : ℝ) (hβ : |β| ≤ 1 / (2 * (q.den : ℝ))) :
    ‖cellPhaseAverage a start length ((q : ℝ) + β)‖ ≤
      (q.den : ℝ) / ((length : ℝ) * a) := by
  have hdR : 0 < (q.den : ℝ) := by exact_mod_cast q.den_pos
  have hnorm := circle_norm_rational_unit_perturbation q (a := 1)
    (Nat.coprime_one_left _) hd β (by simpa only [Nat.cast_one, one_mul] using hβ)
  simp only [Nat.cast_one, one_mul] at hnorm
  have h := cellPhaseAverage_of_norm_lower start ha hL ((q : ℝ) + β)
    (1 / (2 * (q.den : ℝ))) (by positivity) hnorm
  convert h using 1
  field_simp

theorem unitExp_nat_mul_add_int (a : ℕ) (t : ℝ) (n : ℤ) :
    unitExp ((a : ℝ) * (t + n)) = unitExp ((a : ℝ) * t) := by
  rw [mul_add, unitExp_add]
  have hprod : (a : ℝ) * n = ((a : ℤ) * n : ℤ) := by push_cast; rfl
  rw [hprod, unitExp_int, mul_one]

theorem gridPhaseAverage_add_int (a start length : ℕ) (t : ℝ) (n : ℤ) :
    gridPhaseAverage a start length (t + n) = gridPhaseAverage a start length t := by
  unfold gridPhaseAverage
  simp only [unitExp_nat_mul_add_int]

theorem cellPhaseAverage_add_int (a start length : ℕ) (t : ℝ) (n : ℤ) :
    cellPhaseAverage a start length (t + n) = cellPhaseAverage a start length t := by
  unfold cellPhaseAverage
  simp only [unitExp_nat_mul_add_int]

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/WeightedGridBounds.lean -/
section
/- # Weighted Fourier expressions for rough grids and their smoothing -/

namespace Erdos12Proof

noncomputable def blockMass (E : Finset ℕ) (c : ℝ) : ℝ := c * E.card

noncomputable def blockGridFourier (E : Finset ℕ) (c : ℝ) (start length : ℕ) (t : ℝ) : ℂ :=
  (c : ℂ) * ∑ a ∈ E, gridPhaseAverage a start length t

noncomputable def blockCellFourier (E : Finset ℕ) (c : ℝ) (start length : ℕ) (t : ℝ) : ℂ :=
  (c : ℂ) * ∑ a ∈ E, cellPhaseAverage a start length t

theorem norm_weighted_sum_le {κ : Type*} (S : Finset κ) (f : κ → ℂ)
    {c C : ℝ} (hc : 0 ≤ c) (hf : ∀ i ∈ S, ‖f i‖ ≤ C) :
    ‖(c : ℂ) * ∑ i ∈ S, f i‖ ≤ c * S.card * C := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hc
  calc
    _ ≤ ∑ i ∈ S, ‖f i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ S, C := Finset.sum_le_sum hf
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

theorem blockGridFourier_near_rational (E : Finset ℕ) {c D : ℝ} (hc : 0 ≤ c)
    (hE : ∀ a ∈ E, Rough D a) (start : ℕ) {length : ℕ} (hL : 0 < length)
    (q : ℚ) (hd : 1 < q.den) (hden : (q.den : ℝ) ≤ D) (β : ℝ)
    (hβ : ∀ a ∈ E, |(a : ℝ) * β| ≤ 1 / (2 * (q.den : ℝ))) :
    ‖blockGridFourier E c start length ((q : ℝ) + β)‖ ≤
      blockMass E c * (q.den : ℝ) / length := by
  unfold blockGridFourier blockMass
  have h := norm_weighted_sum_le E
    (fun a => gridPhaseAverage a start length ((q : ℝ) + β)) hc
    (fun a ha => gridPhaseAverage_near_rational (hE a ha) hL start q hd hden β (hβ a ha))
  simpa only [mul_div_assoc] using h

theorem blockCellFourier_far (E : Finset ℕ) {c X δ : ℝ} (hc : 0 ≤ c)
    (hX : 0 < X) (hE : ∀ a ∈ E, X ≤ (a : ℝ)) (start : ℕ)
    {length : ℕ} (hL : 0 < length) (t : ℝ) (hδ : 0 < δ)
    (ht : δ ≤ ‖(t : UnitAddCircle)‖) :
    ‖blockCellFourier E c start length t‖ ≤
      blockMass E c / (2 * (length : ℝ) * X * δ) := by
  have hLR : 0 < (length : ℝ) := by exact_mod_cast hL
  unfold blockCellFourier blockMass
  have h := norm_weighted_sum_le E (fun a => cellPhaseAverage a start length t) hc
    (C := 1 / (2 * (length : ℝ) * X * δ)) (fun a ha => by
      have haR : 0 < (a : ℝ) := hX.trans_le (hE a ha)
      have haN : 0 < a := by exact_mod_cast haR
      exact (cellPhaseAverage_of_norm_lower start haN hL t δ hδ ht).trans
        (one_div_le_one_div_of_le (by positivity)
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hE a ha) (by positivity)) hδ.le)))
  simpa only [div_eq_mul_inv, one_mul] using h

theorem blockGridFourier_small_phase (E : Finset ℕ) {c X : ℝ} (hc : 0 ≤ c)
    (hX : 0 < X) (hE : ∀ a ∈ E, X ≤ (a : ℝ)) (start : ℕ)
    {length : ℕ} (hL : 0 < length) (t : ℝ) (ht : 0 < |t|)
    (hsmall : ∀ a ∈ E, (a : ℝ) * |t| ≤ 1 / 2) :
    ‖blockGridFourier E c start length t‖ ≤
      blockMass E c / (2 * (length : ℝ) * X * |t|) := by
  have hLR : 0 < (length : ℝ) := by exact_mod_cast hL
  unfold blockGridFourier blockMass
  have h := norm_weighted_sum_le E (fun a => gridPhaseAverage a start length t) hc
    (C := 1 / (2 * (length : ℝ) * X * |t|)) (fun a ha => by
      have haR : 0 < (a : ℝ) := hX.trans_le (hE a ha)
      have haN : 0 < a := by exact_mod_cast haR
      exact (gridPhaseAverage_small_phase start haN hL t ht (hsmall a ha)).trans
        (one_div_le_one_div_of_le (by positivity)
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hE a ha) (by positivity)) ht.le)))
  simpa only [div_eq_mul_inv, one_mul] using h

theorem blockGridCellFourier_close (E : Finset ℕ) {c A : ℝ} (hc : 0 ≤ c)
    (hE : ∀ a ∈ E, 0 < a ∧ (a : ℝ) ≤ A) (start : ℕ)
    {length : ℕ} (hL : 0 < length) (t : ℝ) :
    ‖blockGridFourier E c start length t - blockCellFourier E c start length t‖ ≤
      blockMass E c * (2 * Real.pi * A * |t|) := by
  have heq : blockGridFourier E c start length t - blockCellFourier E c start length t =
      (c : ℂ) * ∑ a ∈ E, (gridPhaseAverage a start length t - cellPhaseAverage a start length t) := by
    unfold blockGridFourier blockCellFourier
    rw [Finset.sum_sub_distrib, mul_sub]
  rw [heq]
  apply norm_weighted_sum_le E _ hc
  intro a ha
  exact (cellPhaseAverage_close start (hE a ha).1 hL t).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hE a ha).2 (by positivity)) (abs_nonneg t))

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/CyclicGridFunctions.lean -/
section
/- # Cyclic grid densities and their exact Fourier transforms -/

namespace Erdos12Proof

theorem finiteMean_comm {K α β : Type*} [Field K] [Fintype α] [Fintype β] (f : α → β → K) :
    finiteMean (fun x => finiteMean (f x)) = finiteMean (fun y => finiteMean (fun x => f x y)) := by
  simp only [finiteMean, Finset.sum_div, div_div]
  rw [Finset.sum_comm, mul_comm (Fintype.card β : K)]

variable {M : ℕ} [NeZero M]

noncomputable def cyclicPointMass (n x : ZMod M) : ℝ := if x = n then 1 else 0

theorem cyclicPointMass_mean (n : ZMod M) :
    finiteMean (cyclicPointMass n) = 1 / (M : ℝ) := by
  simp [finiteMean, cyclicPointMass, ZMod.card]

theorem cyclicFourier_pointMass (n k : ZMod M) :
    cyclicFourier (fun x => (cyclicPointMass n x : ℂ)) k =
      (M : ℂ)⁻¹ * ZMod.stdAddChar (-(n * k)) := by
  unfold cyclicFourier
  congr 1
  simp [ZMod.dft_apply, cyclicPointMass, apply_ite]

theorem cyclicFourier_natPointMass (n : ℕ) (k : ZMod M) :
    cyclicFourier (fun x => (cyclicPointMass (n : ZMod M) x : ℂ)) k =
      (M : ℂ)⁻¹ * unitExp ((n : ℝ) * cyclicFrequency k) := by
  rw [cyclicFourier_pointMass]
  have h := cyclicCharacter_integer (n : ℤ) k
  simpa only [Int.cast_natCast] using congrArg (fun z => (M : ℂ)⁻¹ * z) h

theorem cyclicFourier_mean {Ω : Type*} [Fintype Ω] (f : Ω → ZMod M → ℂ) (k : ZMod M) :
    cyclicFourier (fun x => finiteMean (fun ω => f ω x)) k =
      finiteMean (fun ω => cyclicFourier (f ω) k) := by
  calc
    _ = finiteMean (fun x => finiteMean (fun ω => f ω x * ZMod.stdAddChar (-(x * k)))) := by
      simp only [cyclicFourier_asMean, finiteMean_mul_const]
    _ = finiteMean (fun ω => finiteMean (fun x => f ω x * ZMod.stdAddChar (-(x * k)))) :=
      finiteMean_comm _
    _ = _ := by simp only [cyclicFourier_asMean]

noncomputable def cyclicSetDensity (E : Finset ℕ) (w : ℝ) (x : ZMod M) : ℝ :=
  w * ∑ a ∈ E, cyclicPointMass (a : ZMod M) x

noncomputable def cyclicGridDensity (E : Finset ℕ) (w : ℝ) (start length : ℕ) (x : ZMod M) : ℝ :=
  w * ∑ a ∈ E, finiteMean (fun k : Fin length =>
    cyclicPointMass ((2 * a * (start + k.val) : ℕ) : ZMod M) x)

noncomputable def cyclicCellDensity (E : Finset ℕ) (w : ℝ) (start length : ℕ) (x : ZMod M) : ℝ :=
  w * ∑ a ∈ E, finiteMean (fun k : Fin length => finiteMean (fun j : Fin a =>
    cyclicPointMass ((2 * (a * (start + k.val) + j.val) : ℕ) : ZMod M) x))

theorem cyclicSetDensity_fourier (E : Finset ℕ) (w : ℝ) (k : ZMod M) :
    cyclicFourier (fun x => (cyclicSetDensity E w x : ℂ)) k =
      ((w / M : ℝ) : ℂ) * ∑ a ∈ E, unitExp ((a : ℝ) * cyclicFrequency k) := by
  have hfun : (fun x : ZMod M => (cyclicSetDensity E w x : ℂ)) =
      fun x => (w : ℂ) * ∑ a ∈ E, (cyclicPointMass (a : ZMod M) x : ℂ) := by
    funext x
    unfold cyclicSetDensity
    push_cast
    rfl
  rw [hfun, cyclicFourier_const_mul, cyclicFourier_sum]
  simp only [cyclicFourier_natPointMass, ← Finset.mul_sum]
  push_cast
  ring

theorem cyclicGridDensity_fourier (E : Finset ℕ) (w : ℝ) (start length : ℕ) (k : ZMod M) :
    cyclicFourier (fun x => (cyclicGridDensity E w start length x : ℂ)) k =
      blockGridFourier E (w / M) start length (2 * cyclicFrequency k) := by
  have hfun : (fun x : ZMod M => (cyclicGridDensity E w start length x : ℂ)) =
      fun x => (w : ℂ) * ∑ a ∈ E, finiteMean (fun j : Fin length =>
        (cyclicPointMass ((2 * a * (start + j.val) : ℕ) : ZMod M) x : ℂ)) := by
    funext x
    unfold cyclicGridDensity finiteMean
    push_cast
    rfl
  rw [hfun, cyclicFourier_const_mul, cyclicFourier_sum]
  simp only [cyclicFourier_mean, cyclicFourier_natPointMass, finiteMean_const_mul,
    ← Finset.mul_sum]
  have hphase (a : ℕ) (j : Fin length) :
      ((2 * a * (start + j.val) : ℕ) : ℝ) * cyclicFrequency k =
        ((a * (start + j.val) : ℕ) : ℝ) * (2 * cyclicFrequency k) := by
    push_cast
    ring
  simp only [hphase]
  unfold blockGridFourier gridPhaseAverage
  push_cast
  ring

theorem cyclicCellDensity_fourier (E : Finset ℕ) (w : ℝ) (start length : ℕ) (k : ZMod M) :
    cyclicFourier (fun x => (cyclicCellDensity E w start length x : ℂ)) k =
      blockCellFourier E (w / M) start length (2 * cyclicFrequency k) := by
  have hfun : (fun x : ZMod M => (cyclicCellDensity E w start length x : ℂ)) =
      fun x => (w : ℂ) * ∑ a ∈ E, finiteMean (fun i : Fin length => finiteMean (fun j : Fin a =>
        (cyclicPointMass ((2 * (a * (start + i.val) + j.val) : ℕ) : ZMod M) x : ℂ))) := by
    funext x
    unfold cyclicCellDensity finiteMean
    push_cast
    rfl
  rw [hfun, cyclicFourier_const_mul, cyclicFourier_sum]
  simp only [cyclicFourier_mean, cyclicFourier_natPointMass, finiteMean_const_mul,
    ← Finset.mul_sum]
  have hphase (a : ℕ) (i : Fin length) (j : Fin a) :
      ((2 * (a * (start + i.val) + j.val) : ℕ) : ℝ) * cyclicFrequency k =
        ((a * (start + i.val) + j.val : ℕ) : ℝ) * (2 * cyclicFrequency k) := by
    push_cast
    ring
  simp only [hphase]
  unfold blockCellFourier cellPhaseAverage
  push_cast
  ring

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/RoughProducts.lean -/
section
/- # Unique products of rough numbers and smooth multipliers -/

namespace Erdos12Proof

theorem rough_smooth_product_unique {D : ℝ} {a b d e : ℕ}
    (ha : Rough D a) (hb : Rough D b) (hd : Smooth D d) (he : Smooth D e)
    (ha0 : 0 < a) (hb0 : 0 < b) (hprod : d * a = e * b) : a = b ∧ d = e := by
  have hab := rough_factor_unique ha hb hd he ha0 hb0 hprod
  refine ⟨hab, ?_⟩
  apply mul_right_cancel₀ ha0.ne'
  simpa only [← hab] using hprod

theorem rough_smooth_pairs_injective {D : ℝ} (E K : Finset ℕ)
    (hrough : ∀ a ∈ E, Rough D a) (hpos : ∀ a ∈ E, 0 < a)
    (hsmooth : ∀ k ∈ K, Smooth D k) :
    Set.InjOn (fun p : ℕ × ℕ => p.2 * p.1) (E ×ˢ K : Finset (ℕ × ℕ)) := by
  intro x hx y hy hxy
  obtain ⟨hxE, hxK⟩ := Finset.mem_product.mp hx
  obtain ⟨hyE, hyK⟩ := Finset.mem_product.mp hy
  obtain ⟨hfirst, hsecond⟩ := rough_smooth_product_unique
    (hrough x.1 hxE) (hrough y.1 hyE) (hsmooth x.2 hxK) (hsmooth y.2 hyK)
    (hpos x.1 hxE) (hpos y.1 hyE) hxy
  exact Prod.ext hfirst hsecond

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/CyclicGridSupport.lean -/
section
/- # Supports of the cyclic block functions and their forbidden correlation -/

namespace Erdos12Proof

variable {M : ℕ}

theorem cyclicPointMass_nonneg (n x : ZMod M) : 0 ≤ cyclicPointMass n x := by
  unfold cyclicPointMass
  split_ifs <;> norm_num

theorem cyclicSetDensity_nonneg (E : Finset ℕ) {w : ℝ} (hw : 0 ≤ w) (x : ZMod M) :
    0 ≤ cyclicSetDensity E w x := by
  exact mul_nonneg hw (Finset.sum_nonneg (fun a _ => cyclicPointMass_nonneg _ _))

theorem cyclicGridDensity_nonneg (E : Finset ℕ) {w : ℝ} (hw : 0 ≤ w)
    (start length : ℕ) (x : ZMod M) : 0 ≤ cyclicGridDensity E w start length x := by
  exact mul_nonneg hw (Finset.sum_nonneg (fun a _ =>
    finiteMean_nonneg (fun _ => cyclicPointMass_nonneg _ _)))

theorem cyclicCellDensity_nonneg (E : Finset ℕ) {w : ℝ} (hw : 0 ≤ w)
    (start length : ℕ) (x : ZMod M) : 0 ≤ cyclicCellDensity E w start length x := by
  exact mul_nonneg hw (Finset.sum_nonneg (fun a _ =>
    finiteMean_nonneg (fun _ => finiteMean_nonneg (fun _ => cyclicPointMass_nonneg _ _))))

theorem cyclicSetDensity_zero (E : Finset ℕ) (w : ℝ) (x : ZMod M)
    (h : ∀ a ∈ E, x ≠ (a : ZMod M)) : cyclicSetDensity E w x = 0 := by
  unfold cyclicSetDensity
  have hz : ∀ a ∈ E, cyclicPointMass (a : ZMod M) x = 0 := by
    intro a ha
    simp only [cyclicPointMass, ite_eq_right (h a ha)]
  rw [Finset.sum_eq_zero hz, mul_zero]

theorem cyclicSetDensity_support (E : Finset ℕ) (w : ℝ) (x : ZMod M)
    (hx : cyclicSetDensity E w x ≠ 0) : ∃ a ∈ E, x = (a : ZMod M) := by
  classical
  by_contra h
  apply hx
  apply cyclicSetDensity_zero
  intro a ha hxa
  exact h ⟨a, ha, hxa⟩

theorem cyclicGridDensity_zero (E : Finset ℕ) (w : ℝ) (start length : ℕ) (x : ZMod M)
    (h : ∀ a ∈ E, ∀ k : Fin length, x ≠ ((2 * a * (start + k.val) : ℕ) : ZMod M)) :
    cyclicGridDensity E w start length x = 0 := by
  unfold cyclicGridDensity
  have hz : ∀ a ∈ E, finiteMean (fun k : Fin length =>
      cyclicPointMass ((2 * a * (start + k.val) : ℕ) : ZMod M) x) = 0 := by
    intro a ha
    have hpoint (k : Fin length) :
        cyclicPointMass ((2 * a * (start + k.val) : ℕ) : ZMod M) x = 0 := by
      simp only [cyclicPointMass, ite_eq_right (h a ha k)]
    simp only [hpoint, finiteMean_zero]
  rw [Finset.sum_eq_zero hz, mul_zero]

theorem cyclicGridDensity_support (E : Finset ℕ) (w : ℝ) (start length : ℕ) (x : ZMod M)
    (hx : cyclicGridDensity E w start length x ≠ 0) :
    ∃ a ∈ E, ∃ k : Fin length, x = ((2 * a * (start + k.val) : ℕ) : ZMod M) := by
  classical
  by_contra h
  apply hx
  apply cyclicGridDensity_zero
  intro a ha k hxa
  exact h ⟨a, ha, k, hxa⟩

theorem nat_eq_of_cyclic_eq {a b : ℕ} (ha : a < M) (hb : b < M)
    (hab : (a : ZMod M) = (b : ZMod M)) : a = b := by
  have h := congrArg ZMod.val hab
  simpa only [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] using h

theorem rough_grid_correlation_zero [NeZero M] {A : Set ℕ} (hA : PropertyP A) (E T : Finset ℕ)
    (hE : ∀ a ∈ E, a ∈ A) (hT : ∀ n ∈ T, n ∈ A) (D : ℝ)
    (hrough : ∀ n ∈ T, Rough D n) (start length : ℕ) (hstart : 1 < start)
    (hsmooth : ∀ k : Fin length, Smooth D (start + k.val))
    (hless : ∀ a ∈ E, ∀ n ∈ T, a < n)
    (hsum : ∀ n ∈ T, ∀ m ∈ T, n + m < M)
    (hgrid : ∀ a ∈ E, ∀ k : Fin length, 2 * a * (start + k.val) < M)
    (wt wb : ℝ) :
    cyclicCorrelation (fun x : ZMod M => (cyclicSetDensity T wt x : ℂ))
      (fun x => (cyclicSetDensity T wt x : ℂ))
      (fun x => (cyclicGridDensity E wb start length x : ℂ)) = 0 := by
  have hpoint (x y : ZMod M) :
      (cyclicSetDensity T wt x : ℂ) * (cyclicSetDensity T wt y : ℂ) *
        (cyclicGridDensity E wb start length (x + y) : ℂ) = 0 := by
    by_cases hx : cyclicSetDensity T wt x = 0
    · simp only [hx, Complex.ofReal_zero, zero_mul]
    by_cases hy : cyclicSetDensity T wt y = 0
    · simp only [hy, Complex.ofReal_zero, mul_zero, zero_mul]
    by_cases hb : cyclicGridDensity E wb start length (x + y) = 0
    · simp only [hb, Complex.ofReal_zero, mul_zero]
    obtain ⟨n, hn, hxn⟩ := cyclicSetDensity_support T wt x hx
    obtain ⟨m, hm, hym⟩ := cyclicSetDensity_support T wt y hy
    obtain ⟨a, ha, k, hprod⟩ := cyclicGridDensity_support E wb start length (x + y) hb
    have hcast : ((n + m : ℕ) : ZMod M) = ((2 * a * (start + k.val) : ℕ) : ZMod M) := by
      simpa only [Nat.cast_add, hxn, hym] using hprod
    have heq := nat_eq_of_cyclic_eq (hsum n hn m hm) (hgrid a ha k) hcast
    have hforbid := forbidden_smooth_multiple_sum hA (hE a ha) (hT n hn) (hT m hm)
      (hless a ha n hn) (hless a ha m hm) (by omega : 1 < start + k.val)
      (hrough n hn) (hsmooth k)
    apply False.elim
    apply hforbid
    calc
      n + m = 2 * a * (start + k.val) := heq
      _ = 2 * (start + k.val) * a := by ring
  simp only [cyclicCorrelation, hpoint, finiteMean_zero]

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/CyclicCellBounds.lean -/
section
/- # Pointwise bounds for complete-cell smoothing -/

namespace Erdos12Proof

variable {M : ℕ}

theorem finiteMean_pointMass_lower {Ω : Type*} [Fintype Ω] (f : Ω → ZMod M)
    (x : ZMod M) (hx : ∃ i, f i = x) :
    1 / (Fintype.card Ω : ℝ) ≤ finiteMean (fun i => cyclicPointMass (f i) x) := by
  obtain ⟨i, hi⟩ := hx
  have hsingle := Finset.single_le_sum
    (fun j _ => cyclicPointMass_nonneg (f j) x) (Finset.mem_univ i)
  have hval : cyclicPointMass (f i) x = 1 := by simp [cyclicPointMass, hi]
  rw [hval] at hsingle
  exact div_le_div_of_nonneg_right hsingle (Nat.cast_nonneg _)

theorem finiteMean_pointMass_upper {Ω : Type*} [Fintype Ω] (f : Ω → ZMod M)
    (hf : Function.Injective f) (x : ZMod M) :
    finiteMean (fun i => cyclicPointMass (f i) x) ≤ 1 / (Fintype.card Ω : ℝ) := by
  classical
  have hsum : (∑ i, cyclicPointMass (f i) x) ≤ 1 := by
    by_cases hx : ∃ i, f i = x
    · obtain ⟨i, hi⟩ := hx
      have heq : (∑ j, cyclicPointMass (f j) x) = 1 := by
        rw [Finset.sum_eq_single i]
        · simp [cyclicPointMass, hi]
        · intro j _ hji
          have hne : x ≠ f j := by
            intro hxj
            exact hji (hf (hxj.symm.trans hi.symm))
          simp only [cyclicPointMass, ite_eq_right hne]
        · simp
      exact heq.le
    · have hz : ∀ i, cyclicPointMass (f i) x = 0 := by
        intro i
        have hne : x ≠ f i := fun h => hx ⟨i, h.symm⟩
        simp only [cyclicPointMass, ite_eq_right hne]
      simp only [hz, Finset.sum_const_zero, zero_le_one]
  exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)

theorem cellPointMean_eq_interval (a start length : ℕ) (x : ZMod M) :
    finiteMean (fun i : Fin length => finiteMean (fun j : Fin a =>
      cyclicPointMass ((2 * (a * (start + i.val) + j.val) : ℕ) : ZMod M) x)) =
      finiteMean (fun n : Fin (length * a) =>
        cyclicPointMass ((2 * (a * start + n.val) : ℕ) : ZMod M) x) := by
  rw [← finiteMean_product]
  have h := finiteMean_equiv (finProdFinEquiv : Fin length × Fin a ≃ Fin (length * a))
    (fun n => cyclicPointMass ((2 * (a * start + n.val) : ℕ) : ZMod M) x)
  rw [← h]
  congr 1
  funext p
  change cyclicPointMass ((2 * (a * (start + p.1.val) + p.2.val) : ℕ) : ZMod M) x =
    cyclicPointMass ((2 * (a * start + (p.2.val + a * p.1.val)) : ℕ) : ZMod M) x
  congr 1
  push_cast
  ring

theorem cellPointMean_lower (a start length ℓ : ℕ) (hlo : a * start ≤ ℓ)
    (hhi : ℓ < a * (start + length)) :
    1 / ((length * a : ℕ) : ℝ) ≤
      finiteMean (fun i : Fin length => finiteMean (fun j : Fin a =>
        cyclicPointMass ((2 * (a * (start + i.val) + j.val) : ℕ) : ZMod M)
          ((2 * ℓ : ℕ) : ZMod M))) := by
  have hn : ℓ - a * start < length * a := by
    rw [Nat.mul_add, Nat.mul_comm a length] at hhi
    omega
  let n : Fin (length * a) := ⟨ℓ - a * start, hn⟩
  have hnval : a * start + n.val = ℓ := Nat.add_sub_of_le hlo
  rw [cellPointMean_eq_interval]
  simpa only [Fintype.card_fin] using finiteMean_pointMass_lower
    (fun i : Fin (length * a) => ((2 * (a * start + i.val) : ℕ) : ZMod M))
    ((2 * ℓ : ℕ) : ZMod M) ⟨n, by rw [hnval]⟩

theorem cellPointMean_upper (a start length : ℕ) (x : ZMod M)
    (hbound : ∀ n : Fin (length * a), 2 * (a * start + n.val) < M) :
    finiteMean (fun i : Fin length => finiteMean (fun j : Fin a =>
      cyclicPointMass ((2 * (a * (start + i.val) + j.val) : ℕ) : ZMod M) x)) ≤
      1 / ((length * a : ℕ) : ℝ) := by
  have hinj : Function.Injective
      (fun i : Fin (length * a) => ((2 * (a * start + i.val) : ℕ) : ZMod M)) := by
    intro i j hij
    have hnat := nat_eq_of_cyclic_eq (hbound i) (hbound j) hij
    apply Fin.ext
    omega
  rw [cellPointMean_eq_interval]
  simpa only [Fintype.card_fin] using finiteMean_pointMass_upper _ hinj x

theorem cyclicCellDensity_lower (E : Finset ℕ) {w A : ℝ} (hw : 0 ≤ w)
    (hE : ∀ a ∈ E, 0 < a ∧ (a : ℝ) ≤ A) (start : ℕ) {length : ℕ} (hL : 0 < length)
    (ℓ : ℕ) (hwindow : ∀ a ∈ E, a * start ≤ ℓ ∧ ℓ < a * (start + length)) :
    blockMass E w / ((length : ℝ) * A) ≤ cyclicCellDensity E w start length ((2 * ℓ : ℕ) : ZMod M) := by
  have hLR : 0 < (length : ℝ) := by exact_mod_cast hL
  have heach (a : ℕ) (ha : a ∈ E) :
      1 / ((length : ℝ) * A) ≤ finiteMean (fun i : Fin length => finiteMean (fun j : Fin a =>
        cyclicPointMass ((2 * (a * (start + i.val) + j.val) : ℕ) : ZMod M)
          ((2 * ℓ : ℕ) : ZMod M))) := by
    have haR : 0 < (a : ℝ) := by exact_mod_cast (hE a ha).1
    have hlow := cellPointMean_lower (M := M) a start length ℓ (hwindow a ha).1 (hwindow a ha).2
    rw [Nat.cast_mul] at hlow
    exact (one_div_le_one_div_of_le (mul_pos hLR haR)
      (mul_le_mul_of_nonneg_left (hE a ha).2 hLR.le)).trans hlow
  calc
    _ = w * ∑ _a ∈ E, (1 / ((length : ℝ) * A)) := by
      simp only [blockMass, Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum heach) hw

theorem cyclicCellDensity_upper (E : Finset ℕ) {w X : ℝ} (hw : 0 ≤ w) (hX : 0 < X)
    (hE : ∀ a ∈ E, X ≤ (a : ℝ)) (start : ℕ) {length : ℕ} (hL : 0 < length)
    (hbound : ∀ a ∈ E, ∀ n : Fin (length * a), 2 * (a * start + n.val) < M) (x : ZMod M) :
    cyclicCellDensity E w start length x ≤ blockMass E w / ((length : ℝ) * X) := by
  have hLR : 0 < (length : ℝ) := by exact_mod_cast hL
  have heach (a : ℕ) (ha : a ∈ E) :
      finiteMean (fun i : Fin length => finiteMean (fun j : Fin a =>
        cyclicPointMass ((2 * (a * (start + i.val) + j.val) : ℕ) : ZMod M) x)) ≤
          1 / ((length : ℝ) * X) := by
    have hupper := cellPointMean_upper a start length x (hbound a ha)
    rw [Nat.cast_mul] at hupper
    exact hupper.trans (one_div_le_one_div_of_le (mul_pos hLR hX)
      (mul_le_mul_of_nonneg_left (hE a ha) hLR.le))
  calc
    _ ≤ w * ∑ _a ∈ E, (1 / ((length : ℝ) * X)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum heach) hw
    _ = _ := by
      simp only [blockMass, Finset.sum_const, nsmul_eq_mul]
      ring

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/CyclicGridMeans.lean -/
section
/- # Mean and quadratic bounds for the cyclic block densities -/

namespace Erdos12Proof

variable {M : ℕ} [NeZero M]

theorem cyclicSetDensity_mean (E : Finset ℕ) (w : ℝ) :
    finiteMean (cyclicSetDensity (M := M) E w) = blockMass E (w / M) := by
  unfold cyclicSetDensity
  rw [finiteMean_const_mul, finiteMean_sum]
  simp only [cyclicPointMass_mean, Finset.sum_const, nsmul_eq_mul, blockMass]
  ring

theorem cyclicGridDensity_mean (E : Finset ℕ) (w : ℝ) (start : ℕ) {length : ℕ}
    (hL : 0 < length) :
    finiteMean (cyclicGridDensity (M := M) E w start length) = blockMass E (w / M) := by
  let : NeZero length := ⟨hL.ne'⟩
  have hinner (a : ℕ) : finiteMean (fun x : ZMod M => finiteMean (fun j : Fin length =>
      cyclicPointMass ((2 * a * (start + j.val) : ℕ) : ZMod M) x)) = 1 / (M : ℝ) := by
    rw [finiteMean_comm]
    simp only [cyclicPointMass_mean, finiteMean_const]
  unfold cyclicGridDensity
  rw [finiteMean_const_mul, finiteMean_sum]
  simp only [hinner, Finset.sum_const, nsmul_eq_mul, blockMass]
  ring

theorem cyclicCellDensity_mean (E : Finset ℕ) (w : ℝ) (hE : ∀ a ∈ E, 0 < a)
    (start : ℕ) {length : ℕ} (hL : 0 < length) :
    finiteMean (cyclicCellDensity (M := M) E w start length) = blockMass E (w / M) := by
  let : NeZero length := ⟨hL.ne'⟩
  have hinner (a : ℕ) (ha : a ∈ E) :
      finiteMean (fun x : ZMod M => finiteMean (fun i : Fin length => finiteMean (fun j : Fin a =>
        cyclicPointMass ((2 * (a * (start + i.val) + j.val) : ℕ) : ZMod M) x))) =
          1 / (M : ℝ) := by
    let : NeZero a := ⟨(hE a ha).ne'⟩
    have hsecond (i : Fin length) :
        finiteMean (fun x : ZMod M => finiteMean (fun j : Fin a =>
          cyclicPointMass ((2 * (a * (start + i.val) + j.val) : ℕ) : ZMod M) x)) =
            1 / (M : ℝ) := by
      rw [finiteMean_comm]
      simp only [cyclicPointMass_mean, finiteMean_const]
    rw [finiteMean_comm]
    simp only [hsecond, finiteMean_const]
  unfold cyclicCellDensity
  rw [finiteMean_const_mul, finiteMean_sum]
  rw [Finset.sum_congr rfl hinner]
  simp only [Finset.sum_const, nsmul_eq_mul, blockMass]
  ring

theorem cyclic_real_l2_bound (f : ZMod M → ℝ) (C : ℝ) (hf0 : ∀ x, 0 ≤ f x)
    (hfC : ∀ x, f x ≤ C) :
    finiteLqNorm Finset.univ (cyclicFourier (fun x => (f x : ℂ))) 2 ≤
      Real.sqrt (C * finiteMean f) := by
  unfold finiteLqNorm
  simp only [Real.rpow_two]
  rw [← Real.sqrt_eq_rpow, cyclicFourier_parseval, ← finiteMean_const_mul]
  apply Real.sqrt_le_sqrt
  apply finiteMean_mono
  intro x
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  nlinarith [hf0 x, hfC x]

theorem cyclic_real_lq_bound (f : ZMod M → ℝ) (C : ℝ) (hf0 : ∀ x, 0 ≤ f x)
    (hfC : ∀ x, f x ≤ C) {q : ℝ} (hq : 2 < q) :
    finiteLqNorm Finset.univ (cyclicFourier (fun x => (f x : ℂ))) q ≤
      Real.sqrt (C * finiteMean f) := by
  exact (finiteLqNorm_mono_exponent Finset.univ (cyclicFourier (fun x => (f x : ℂ)))
    (by norm_num : (0 : ℝ) < 2) hq).trans (cyclic_real_l2_bound f C hf0 hfC)

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/SiftedCoefficientSupport.lean -/
section
/- # Restriction when only the nonzero coefficients are sifted -/

namespace Erdos12Proof

theorem finiteFourierSum_filter_nonzero (T : Finset ℤ) (b : ℤ → ℂ) (x : ℝ) :
    finiteFourierSum (T.filter (fun n => b n ≠ 0)) b x = finiteFourierSum T b x := by
  classical
  unfold finiteFourierSum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hb : b n = 0 <;> simp [hb]

theorem coefficientEnergy_filter_nonzero {κ : Type*} (T : Finset κ) (b : κ → ℂ) :
    coefficientEnergy (T.filter (fun n => b n ≠ 0)) b = coefficientEnergy T b := by
  classical
  unfold coefficientEnergy
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hb : b n = 0 <;> simp [hb]

theorem sifted_coefficient_support_restriction {ι κ : Type*} [Fintype ι] (m : ι → ℕ)
    (S : Finset κ) (a : κ → ℝ) (T : Finset ℤ) (b : ℤ → ℂ)
    (hprime : ∀ i, (m i).Prime) (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    (q : ℝ) (hq : 2 < q) (N δ z : ℝ) (hδ : 0 < δ) (hz : 1 < z) (hN : z ^ 4 ≤ N)
    (hinterval : ∀ n ∈ T, 0 ≤ (n : ℝ) ∧ (n : ℝ) ≤ N)
    (hsifted : ∀ n ∈ T, b n ≠ 0 → ∀ i, (n : ZMod (m i)) ≠ 0)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      δ ≤ dist (a i : UnitAddCircle) (a j : UnitAddCircle)) :
    (∑ i ∈ S, ‖finiteFourierSum T b (a i)‖ ^ q) ^ (1 / q) ≤
      (restrictionMomentConstant q) ^ (1 / q) *
        Real.sqrt (((N + δ⁻¹) / sieveMass m z) * coefficientEnergy T b) := by
  classical
  have h := sifted_restriction_lq m S a (T.filter (fun n => b n ≠ 0)) b
    hprime hcop q hq N δ z hδ hz hN
    (fun n hn => hinterval n (Finset.mem_filter.mp hn).1)
    (fun n hn => hsifted n (Finset.mem_filter.mp hn).1 (Finset.mem_filter.mp hn).2)
    hsep
  simpa only [finiteFourierSum_filter_nonzero, coefficientEnergy_filter_nonzero] using h

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/CyclicFunctionRestriction.lean -/
section
/- # Sifted restriction for arbitrary functions on a cyclic group -/

namespace Erdos12Proof

variable {M : ℕ} [NeZero M]

noncomputable def cyclicIntegerDomain : Finset ℤ :=
  Finset.univ.image (fun x : ZMod M => (x.val : ℤ))

theorem cyclicIntegerDomain_sum {K : Type*} [AddCommMonoid K] (f : ℤ → K) :
    (∑ n ∈ cyclicIntegerDomain (M := M), f n) = ∑ x : ZMod M, f x.val := by
  unfold cyclicIntegerDomain
  rw [Finset.sum_image]
  intro x _ y _ hxy
  apply ZMod.val_injective M
  change (x.val : ℤ) = (y.val : ℤ) at hxy
  exact_mod_cast hxy

theorem cyclicIntegerDomain_interval {n : ℤ} (hn : n ∈ cyclicIntegerDomain (M := M)) :
    0 ≤ (n : ℝ) ∧ (n : ℝ) ≤ M := by
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hn
  exact ⟨by positivity, by exact_mod_cast (ZMod.val_lt x).le⟩

theorem cyclicIntegerDomain_energy (f : ZMod M → ℂ) :
    coefficientEnergy (cyclicIntegerDomain (M := M)) (fun n => f (n : ZMod M)) =
      (M : ℝ) * finiteMean (fun x => ‖f x‖ ^ 2) := by
  unfold coefficientEnergy
  rw [cyclicIntegerDomain_sum]
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  unfold finiteMean
  rw [ZMod.card]
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  field_simp

theorem cyclicIntegerDomain_fourier (f : ZMod M → ℂ) (k : ZMod M) :
    finiteFourierSum (cyclicIntegerDomain (M := M)) (fun n => f (n : ZMod M))
      (cyclicFrequency k) = (M : ℂ) * cyclicFourier f k := by
  unfold finiteFourierSum
  rw [cyclicIntegerDomain_sum, ← cyclicFourier_unscaled]
  apply Finset.sum_congr rfl
  intro x _
  have hchar : ZMod.stdAddChar (-(x * k)) = unitExp ((x.val : ℝ) * cyclicFrequency k) := by
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using cyclicCharacter_integer (x.val : ℤ) k
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val, hchar]
  rw [mul_comm (cyclicFrequency k)]

theorem cyclic_function_sifted_restriction {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (f : ZMod M → ℂ) (hprime : ∀ i, (m i).Prime)
    (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    (q : ℝ) (hq : 2 < q) (z : ℝ) (hz : 1 < z) (hzM : z ^ 4 ≤ M)
    (hsifted : ∀ x, f x ≠ 0 → ∀ i, (x.val : ZMod (m i)) ≠ 0) :
    finiteLqNorm Finset.univ (cyclicFourier f) q ≤
      (restrictionMomentConstant q) ^ (1 / q) *
        Real.sqrt ((2 / sieveMass m z) * finiteMean (fun x => ‖f x‖ ^ 2)) := by
  have hM : 0 < (M : ℝ) := by exact_mod_cast NeZero.pos M
  have hq0 : 0 < q := by linarith
  have h := sifted_coefficient_support_restriction m Finset.univ cyclicFrequency
    (cyclicIntegerDomain (M := M)) (fun n => f (n : ZMod M)) hprime hcop q hq
    (M : ℝ) (1 / M) z (one_div_pos.mpr hM) hz hzM
    (fun _ hn => cyclicIntegerDomain_interval hn)
    (fun n hn hfn => by
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hn
      simp only [Int.cast_natCast, ZMod.natCast_zmod_val] at hfn ⊢
      exact hsifted x hfn)
    (fun i _ j _ hij => cyclicFrequency_separated hij)
  change finiteLqNorm Finset.univ
    (fun k => finiteFourierSum (cyclicIntegerDomain (M := M)) (fun n => f (n : ZMod M))
      (cyclicFrequency k)) q ≤ _ at h
  have hfun : (fun k => finiteFourierSum (cyclicIntegerDomain (M := M))
      (fun n => f (n : ZMod M)) (cyclicFrequency k)) =
        fun k => (M : ℂ) * cyclicFourier f k := funext (cyclicIntegerDomain_fourier f)
  rw [hfun, finiteLqNorm_const_mul Finset.univ _ _ hq0, Complex.norm_natCast,
    cyclicIntegerDomain_energy] at h
  simp only [one_div, inv_inv] at h
  have hradicand : (((M : ℝ) + M) / sieveMass m z) *
      ((M : ℝ) * finiteMean (fun x => ‖f x‖ ^ 2)) =
        (M : ℝ) ^ 2 * ((2 / sieveMass m z) * finiteMean (fun x => ‖f x‖ ^ 2)) := by ring
  rw [hradicand, Real.sqrt_mul (sq_nonneg (M : ℝ)), Real.sqrt_sq_eq_abs,
    abs_of_pos hM] at h
  apply (mul_le_mul_iff_right₀ hM).mp
  simpa only [one_div, mul_left_comm] using h

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/CyclicRoughGridBounds.lean -/
section
/- # Pointwise and restriction bounds for a cyclic rough grid -/

namespace Erdos12Proof

variable {M : ℕ}

theorem sum_pointMass_le_one {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ZMod M) (hf : Function.Injective f) (x : ZMod M) :
    (∑ i, cyclicPointMass (f i) x) ≤ 1 := by
  have h := finiteMean_pointMass_upper f hf x
  have hcard : 0 < (Fintype.card Ω : ℝ) := by exact_mod_cast Fintype.card_pos
  exact (div_le_div_iff_of_pos_right hcard).mp h

theorem roughGrid_points_injective (E : Finset ℕ) (D : ℝ)
    (hE : ∀ a ∈ E, Rough D a) (hpos : ∀ a ∈ E, 0 < a) (start length : ℕ)
    (hsmooth : ∀ j : Fin length, Smooth D (2 * (start + j.val)))
    (hbound : ∀ a ∈ E, ∀ j : Fin length, 2 * a * (start + j.val) < M) :
    Function.Injective (fun p : E × Fin length =>
      ((2 * p.1.val * (start + p.2.val) : ℕ) : ZMod M)) := by
  intro x y hxy
  have hnat := nat_eq_of_cyclic_eq (hbound x.1 x.1.property x.2)
    (hbound y.1 y.1.property y.2) hxy
  have hproduct : (2 * (start + x.2.val)) * x.1.val =
      (2 * (start + y.2.val)) * y.1.val := by nlinarith [hnat]
  obtain ⟨ha, hd⟩ := rough_smooth_product_unique (hE x.1 x.1.property) (hE y.1 y.1.property)
    (hsmooth x.2) (hsmooth y.2) (hpos x.1 x.1.property) (hpos y.1 y.1.property) hproduct
  apply Prod.ext
  · exact Subtype.ext ha
  · apply Fin.ext
    omega

theorem cyclicGridDensity_upper_of_injective (E : Finset ℕ) {w : ℝ} (hw : 0 ≤ w)
    (start : ℕ) {length : ℕ} (hL : 0 < length)
    (hinj : Function.Injective (fun p : E × Fin length =>
      ((2 * p.1.val * (start + p.2.val) : ℕ) : ZMod M))) (x : ZMod M) :
    cyclicGridDensity E w start length x ≤ w / length := by
  classical
  by_cases hE : E.Nonempty
  · let : Nonempty E := hE.to_subtype
    let : NeZero length := ⟨hL.ne'⟩
    have hsum := sum_pointMass_le_one _ hinj x
    rw [Fintype.sum_prod_type] at hsum
    rw [Finset.sum_coe_sort (s := E) (f := fun a : ℕ =>
      ∑ j : Fin length, cyclicPointMass ((2 * a * (start + j.val) : ℕ) : ZMod M) x)] at hsum
    have heq : cyclicGridDensity E w start length x =
        (w / length) * ∑ a ∈ E, ∑ j : Fin length,
          cyclicPointMass ((2 * a * (start + j.val) : ℕ) : ZMod M) x := by
      unfold cyclicGridDensity finiteMean
      simp only [Fintype.card_fin]
      rw [← Finset.sum_div, ← mul_div_assoc, div_mul_eq_mul_div]
    rw [heq]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hsum
      (div_nonneg hw (by exact_mod_cast hL.le))
  · have hempty : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
    simp only [hempty, cyclicGridDensity, Finset.sum_empty, mul_zero]
    exact div_nonneg hw (Nat.cast_nonneg length)

theorem roughGrid_sifted_at_prime (E : Finset ℕ) (D H : ℝ)
    (hE : ∀ a ∈ E, Rough D a) (w : ℝ) (start length : ℕ)
    (hsmooth : ∀ j : Fin length, Smooth H (2 * (start + j.val)))
    (hbound : ∀ a ∈ E, ∀ j : Fin length, 2 * a * (start + j.val) < M)
    (p : ℕ) (hp : p.Prime) (hHp : H < p) (hpD : (p : ℝ) ≤ D)
    (x : ZMod M) (hx : cyclicGridDensity E w start length x ≠ 0) :
    (x.val : ZMod p) ≠ 0 := by
  obtain ⟨a, ha, j, hxprod⟩ := cyclicGridDensity_support E w start length x hx
  have hval : x.val = 2 * a * (start + j.val) := by
    rw [hxprod, ZMod.val_natCast_of_lt (hbound a ha j)]
  intro hzero
  have hdiv : p ∣ (2 * (start + j.val)) * a := by
    have hd := (ZMod.natCast_eq_zero_iff x.val p).mp hzero
    rw [hval] at hd
    convert hd using 1
    ring
  rcases hp.dvd_mul.mp hdiv with hmult | hab
  · exact (not_le_of_gt hHp) (hsmooth j p hp hmult)
  · exact (not_lt_of_ge hpD) (hE a ha p hp hab)

theorem roughGrid_restriction [NeZero M] {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hprime : ∀ i, (m i).Prime) (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    (E : Finset ℕ) (D H : ℝ) (hHD : H ≤ D) (hE : ∀ a ∈ E, Rough D a)
    (hpos : ∀ a ∈ E, 0 < a) (w : ℝ) (hw : 0 ≤ w) (start : ℕ)
    {length : ℕ} (hL : 0 < length)
    (hsmooth : ∀ j : Fin length, Smooth H (2 * (start + j.val)))
    (hbound : ∀ a ∈ E, ∀ j : Fin length, 2 * a * (start + j.val) < M)
    (hband : ∀ i, H < m i ∧ (m i : ℝ) ≤ D)
    (q : ℝ) (hq : 2 < q) (z : ℝ) (hz : 1 < z) (hzM : z ^ 4 ≤ M) :
    finiteLqNorm Finset.univ
      (cyclicFourier (fun x : ZMod M => (cyclicGridDensity E w start length x : ℂ))) q ≤
        (restrictionMomentConstant q) ^ (1 / q) *
          Real.sqrt ((2 / sieveMass m z) * ((w / length) * blockMass E (w / M))) := by
  have hsmoothD : ∀ j : Fin length, Smooth D (2 * (start + j.val)) := by
    intro j p hp hdiv
    exact (hsmooth j p hp hdiv).trans hHD
  have hinj := roughGrid_points_injective E D hE hpos start length hsmoothD hbound
  have hupper := cyclicGridDensity_upper_of_injective E hw start hL hinj
  have hrestrict := cyclic_function_sifted_restriction m
    (fun x => (cyclicGridDensity E w start length x : ℂ)) hprime hcop q hq z hz hzM
    (fun x hx i => roughGrid_sifted_at_prime E D H hE w start length hsmooth hbound (m i)
      (hprime i) (hband i).1 (hband i).2 x (by exact_mod_cast hx))
  have henergy : finiteMean (fun x : ZMod M => ‖(cyclicGridDensity E w start length x : ℂ)‖ ^ 2) ≤
      (w / length) * blockMass E (w / M) := by
    calc
      _ ≤ finiteMean (fun x => (w / length) * cyclicGridDensity E w start length x) := by
        apply finiteMean_mono
        intro x
        simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
        nlinarith [cyclicGridDensity_nonneg E hw start length x, hupper x]
      _ = _ := by rw [finiteMean_const_mul, cyclicGridDensity_mean E w start hL]
  have hG := sieveMass_pos (fun i => (hprime i).one_lt) hz
  exact hrestrict.trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left henergy (by positivity)))
    (Real.rpow_nonneg (restrictionMomentConstant_pos hq).le _))

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/CyclicRoughSetBounds.lean -/
section
/- # Pointwise and restriction bounds for a rough set in a cyclic group -/

namespace Erdos12Proof

variable {M : ℕ}

theorem cyclicSetDensity_upper (E : Finset ℕ) {w : ℝ} (hw : 0 ≤ w)
    (hbound : ∀ a ∈ E, a < M) (x : ZMod M) : cyclicSetDensity E w x ≤ w := by
  classical
  by_cases hE : E.Nonempty
  · let : Nonempty E := hE.to_subtype
    have hinj : Function.Injective (fun a : E => (a.val : ZMod M)) := by
      intro a b hab
      apply Subtype.ext
      exact nat_eq_of_cyclic_eq (hbound a a.property) (hbound b b.property) hab
    have hsum := sum_pointMass_le_one (fun a : E => (a.val : ZMod M)) hinj x
    rw [Finset.sum_coe_sort (s := E) (f := fun a : ℕ => cyclicPointMass (a : ZMod M) x)] at hsum
    exact (mul_le_mul_of_nonneg_left hsum hw).trans_eq (mul_one w)
  · have hempty : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
    simpa only [hempty, cyclicSetDensity, Finset.sum_empty, mul_zero] using hw

theorem roughSet_sifted_at_prime (E : Finset ℕ) (D : ℝ)
    (hE : ∀ a ∈ E, Rough D a) (hbound : ∀ a ∈ E, a < M)
    (w : ℝ) (p : ℕ) (hp : p.Prime) (hpD : (p : ℝ) ≤ D)
    (x : ZMod M) (hx : cyclicSetDensity E w x ≠ 0) : (x.val : ZMod p) ≠ 0 := by
  obtain ⟨a, ha, hxa⟩ := cyclicSetDensity_support E w x hx
  have hval : x.val = a := by rw [hxa, ZMod.val_natCast_of_lt (hbound a ha)]
  intro hzero
  have hdiv := (ZMod.natCast_eq_zero_iff x.val p).mp hzero
  rw [hval] at hdiv
  exact (not_lt_of_ge hpD) (hE a ha p hp hdiv)

theorem roughSet_restriction [NeZero M] {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hprime : ∀ i, (m i).Prime) (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    (E : Finset ℕ) (D : ℝ) (hE : ∀ a ∈ E, Rough D a)
    (hmD : ∀ i, (m i : ℝ) ≤ D) (hbound : ∀ a ∈ E, a < M)
    (w : ℝ) (hw : 0 ≤ w) (q : ℝ) (hq : 2 < q)
    (z : ℝ) (hz : 1 < z) (hzM : z ^ 4 ≤ M) :
    finiteLqNorm Finset.univ (cyclicFourier (fun x : ZMod M => (cyclicSetDensity E w x : ℂ))) q ≤
      (restrictionMomentConstant q) ^ (1 / q) *
        Real.sqrt ((2 / sieveMass m z) * (w * blockMass E (w / M))) := by
  have hupper := cyclicSetDensity_upper E hw hbound
  have hrestrict := cyclic_function_sifted_restriction m
    (fun x : ZMod M => (cyclicSetDensity E w x : ℂ)) hprime hcop q hq z hz hzM
    (fun x hx i => roughSet_sifted_at_prime E D hE hbound w (m i) (hprime i) (hmD i) x
      (by exact_mod_cast hx))
  have henergy : finiteMean (fun x : ZMod M => ‖(cyclicSetDensity E w x : ℂ)‖ ^ 2) ≤
      w * blockMass E (w / M) := by
    calc
      _ ≤ finiteMean (fun x => w * cyclicSetDensity E w x) := by
        apply finiteMean_mono
        intro x
        simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
        nlinarith [cyclicSetDensity_nonneg E hw x, hupper x]
      _ = _ := by rw [finiteMean_const_mul, cyclicSetDensity_mean]
  have hG := sieveMass_pos (fun i => (hprime i).one_lt) hz
  exact hrestrict.trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left henergy (by positivity)))
    (Real.rpow_nonneg (restrictionMomentConstant_pos hq).le _))

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/SieveNormScales.lean -/
section
/- # Normalizing the full-prime and prime-band Fourier norms -/

namespace Erdos12Proof

theorem sieve_sqrt_scale {G g U A : ℝ} (hg : 0 < g) (hU : 0 < U)
    (hA : 0 ≤ A) (hG : g * U ≤ G) :
    Real.sqrt ((2 / G) * (U * A)) ≤ Real.sqrt (2 / g) * Real.sqrt A := by
  have hG0 : 0 < G := (mul_pos hg hU).trans_le hG
  have hratio : 2 / G ≤ 2 / (g * U) :=
    div_le_div_of_nonneg_left (by norm_num) (mul_pos hg hU) hG
  calc
    _ ≤ Real.sqrt ((2 / (g * U)) * (U * A)) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hratio (mul_nonneg hU.le hA))
    _ = Real.sqrt ((2 / g) * A) := by congr 1; field_simp
    _ = _ := Real.sqrt_mul (by positivity) A

theorem band_sqrt_scale {G g U α u K L H : ℝ}
    (hg : 0 < g) (hU : 0 < U) (hα : 0 ≤ α) (hu : 0 ≤ u)
    (hK : 0 < K) (hKL : K ≤ L) (hH : 0 < H)
    (hαu : α ≤ u / K) (hG : g * U / H ≤ G) :
    Real.sqrt ((2 / G) * ((U / L) * α)) ≤
      Real.sqrt (2 / g) * (Real.sqrt u / K) * Real.sqrt H := by
  have hL : 0 < L := hK.trans_le hKL
  have hG0 : 0 < G := (div_pos (mul_pos hg hU) hH).trans_le hG
  have hratio : 2 / G ≤ 2 * H / (g * U) := by
    calc
      _ ≤ 2 / (g * U / H) :=
        div_le_div_of_nonneg_left (by norm_num) (div_pos (mul_pos hg hU) hH) hG
      _ = _ := by field_simp
  have henergy : (U / L) * α ≤ U * u / K ^ 2 := by
    calc
      _ ≤ (U / L) * (u / K) := mul_le_mul_of_nonneg_left hαu (div_nonneg hU.le hL.le)
      _ ≤ (U / K) * (u / K) := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left hU.le hK hKL) (div_nonneg hu hK.le)
      _ = _ := by ring
  have hraw : (2 / G) * ((U / L) * α) ≤ (2 / g) * (u / K ^ 2) * H := by
    calc
      _ ≤ (2 * H / (g * U)) * (U * u / K ^ 2) :=
        mul_le_mul hratio henergy (mul_nonneg (div_nonneg hU.le hL.le) hα) (by positivity)
      _ = _ := by field_simp
  have h2g : 0 ≤ 2 / g := by positivity
  have huK : 0 ≤ u / K ^ 2 := div_nonneg hu (sq_nonneg K)
  have hroot : Real.sqrt ((2 / g) * (u / K ^ 2) * H) =
      Real.sqrt (2 / g) * (Real.sqrt u / K) * Real.sqrt H := by
    rw [Real.sqrt_mul (mul_nonneg h2g huK), Real.sqrt_mul h2g,
      Real.sqrt_div hu, Real.sqrt_sq_eq_abs, abs_of_pos hK]
  exact (Real.sqrt_le_sqrt hraw).trans_eq hroot

theorem cell_sqrt_scale {α : ℝ} (hα : 0 ≤ α) : Real.sqrt ((64 * α) * α) = 8 * α := by
  rw [show (64 * α) * α = (8 * α) ^ 2 by ring, Real.sqrt_sq (by positivity)]

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/RoughBlockGeometry.lean -/
section
/- # The intervals, multiplier grid and cyclic modulus for two rough blocks -/

namespace Erdos12Proof

def blockGridStart (K : ℕ) : ℕ := K / 4

def blockGridLength (K : ℕ) : ℕ := 4 * K + 1 - K / 4

def blockModulus (X K : ℕ) : ℕ := 32 * K * X

theorem blockGrid_stop (K : ℕ) : blockGridStart K + blockGridLength K = 4 * K + 1 := by
  unfold blockGridStart blockGridLength
  omega

theorem blockGrid_start_ge_four {K : ℕ} (hK : 16 ≤ K) : 4 ≤ blockGridStart K := by
  unfold blockGridStart
  omega

theorem blockGrid_length_bounds {K : ℕ} (hK : 1 ≤ K) :
    3 * K ≤ blockGridLength K ∧ blockGridLength K ≤ 5 * K := by
  unfold blockGridLength
  omega

theorem blockGrid_length_pos {K : ℕ} (hK : 1 ≤ K) : 0 < blockGridLength K := by
  have h := (blockGrid_length_bounds hK).1
  omega

theorem blockModulus_pos {X K : ℕ} (hX : 0 < X) (hK : 0 < K) : 0 < blockModulus X K := by
  unfold blockModulus
  positivity

theorem blockGrid_multiplier_bound {K : ℕ} (j : Fin (blockGridLength K)) :
    blockGridStart K + j.val ≤ 4 * K := by
  have hstop := blockGrid_stop K
  have hj := j.isLt
  omega

theorem blockGrid_multiplier_smooth {K : ℕ} {D : ℝ} (hK : 16 ≤ K)
    (hD : (4 * K : ℕ) ≤ D) (j : Fin (blockGridLength K)) :
    Smooth D (blockGridStart K + j.val) := by
  have hstart := blockGrid_start_ge_four hK
  apply smooth_of_le (by omega)
  exact le_trans (by exact_mod_cast blockGrid_multiplier_bound j) hD

theorem blockCell_no_wrap {X K a n : ℕ} (hX : 0 < X) (hK : 1 ≤ K)
    (ha : a < 2 * X) (hn : n < blockGridLength K * a) :
    2 * (a * blockGridStart K + n) < blockModulus X K := by
  have hcell : a * blockGridStart K + n < a * (4 * K + 1) := by
    calc
      _ < a * blockGridStart K + blockGridLength K * a := Nat.add_lt_add_left hn _
      _ = a * (blockGridStart K + blockGridLength K) := by ring
      _ = _ := by rw [blockGrid_stop]
  have hproduct := Nat.mul_lt_mul_of_pos_right ha (by omega : 0 < 4 * K + 1)
  have hmax : (2 * X) * (4 * K + 1) ≤ 10 * K * X := by
    calc
      _ ≤ (2 * X) * (5 * K) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
  have hpos : 0 < K * X := Nat.mul_pos (by omega) hX
  unfold blockModulus
  nlinarith

theorem blockGrid_no_wrap {X K a : ℕ} (hX : 0 < X) (hK : 1 ≤ K)
    (hXa : X ≤ a) (ha : a < 2 * X) (j : Fin (blockGridLength K)) :
    2 * a * (blockGridStart K + j.val) < blockModulus X K := by
  have ha0 : 0 < a := hX.trans_le hXa
  have hn : a * j.val < blockGridLength K * a := by
    simpa only [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_left j.isLt ha0
  calc
    _ = 2 * (a * blockGridStart K + a * j.val) := by ring
    _ < _ := blockCell_no_wrap hX hK ha hn

theorem blockCell_covers_middle {X K a ℓ : ℕ} (hX : 0 < X)
    (hXa : X ≤ a) (ha : a < 2 * X) (hlo : K * X ≤ ℓ) (hhi : ℓ ≤ 2 * (K * X)) :
    a * blockGridStart K ≤ ℓ ∧ ℓ < a * (blockGridStart K + blockGridLength K) := by
  constructor
  · calc
      _ ≤ (2 * X) * blockGridStart K := Nat.mul_le_mul_right _ ha.le
      _ = X * (2 * blockGridStart K) := by ring
      _ ≤ X * K := Nat.mul_le_mul_left _ (by unfold blockGridStart; omega)
      _ = K * X := Nat.mul_comm _ _
      _ ≤ ℓ := hlo
  · calc
      ℓ ≤ 2 * (K * X) := hhi
      _ = (2 * K) * X := by ring
      _ < (4 * K + 1) * X := Nat.mul_lt_mul_of_pos_right (by omega) hX
      _ = X * (blockGridStart K + blockGridLength K) := by rw [blockGrid_stop]; ring
      _ ≤ a * (blockGridStart K + blockGridLength K) := Nat.mul_le_mul_right _ hXa

theorem block_earlier_lt_later {X K a n : ℕ} (hK : 2 ≤ K)
    (ha : a < 2 * X) (hn : K * X ≤ n) : a < n := by
  exact ha.trans_le ((Nat.mul_le_mul_right X hK).trans hn)

theorem block_later_sum_no_wrap {X K n m : ℕ} (hX : 0 < X) (hK : 0 < K)
    (hn : n < 2 * (K * X)) (hm : m < 2 * (K * X)) : n + m < blockModulus X K := by
  have hpos := Nat.mul_pos hK hX
  unfold blockModulus
  nlinarith

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/FinitePrimeSieve.lean -/
section
/- # A finite-set representation of the prime sieve mass -/

namespace Erdos12Proof

noncomputable def finitePrimeSieveMass (P : Finset ℕ) (z : ℝ) : ℝ :=
  selbergMass sieveLocalWeight
    (P.powerset.filter (fun s => ((∏ p ∈ s, p : ℕ) : ℝ) < z))

theorem finitePrimeSieveMass_eq (P : Finset ℕ) (z : ℝ) :
    sieveMass (fun p : P => (p : ℕ)) z = finitePrimeSieveMass P z := by
  unfold sieveMass finitePrimeSieveMass selbergMass
  apply Finset.sum_bij (fun s _ => s.map (Function.Embedding.subtype (fun p => p ∈ P)))
  · intro s hs
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_powerset.mpr
      intro p hp
      exact Finset.property_of_mem_map_subtype s hp
    · have hbound := (Finset.mem_filter.mp hs).2
      simpa only [Finset.prod_map, Function.Embedding.subtype_apply] using hbound
  · intro s _ t _ hst
    exact Finset.map_injective _ hst
  · intro s hs
    obtain ⟨hsP, hsbound⟩ := Finset.mem_filter.mp hs
    have hsub := Finset.mem_powerset.mp hsP
    refine ⟨s.subtype (fun p => p ∈ P), ?_, Finset.subtype_map_of_mem hsub⟩
    simp only [sieveSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Finset.prod_subtype_of_mem (fun p : ℕ => p) hsub]
    exact hsbound
  · intro s _
    simp only [tensorWeight, Finset.prod_map, Function.Embedding.subtype_apply]

theorem finitePrimeSieveMass_mono {P Q : Finset ℕ} (hPQ : P ⊆ Q)
    (hprime : ∀ p ∈ Q, p.Prime) (z : ℝ) :
    finitePrimeSieveMass P z ≤ finitePrimeSieveMass Q z := by
  unfold finitePrimeSieveMass selbergMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro s hs
    obtain ⟨hsP, hbound⟩ := Finset.mem_filter.mp hs
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr ((Finset.mem_powerset.mp hsP).trans hPQ), hbound⟩
  · intro s hs _
    apply Finset.prod_nonneg
    intro p hp
    have hpQ := (Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1) hp
    exact (sieveLocalWeight_pos (hprime p hpQ).one_lt).le

theorem primeBand_mono {x X y : ℝ} (hxX : x ≤ X) : primeBand y x ⊆ primeBand y X := by
  intro p hp
  obtain ⟨hpx, hpy⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨primesThrough_mono hxX hpx, hpy⟩

theorem finitePrimeSieveMass_band_mono {x X y : ℝ} (hxX : x ≤ X) (z : ℝ) :
    finitePrimeSieveMass (primeBand y x) z ≤ finitePrimeSieveMass (primeBand y X) z := by
  apply finitePrimeSieveMass_mono (primeBand_mono hxX)
  intro p hp
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/SelbergMassLowerBound.lean -/
section
/- # The finite Markov step in the lower bound for the sifting mass -/

namespace Erdos12Proof

theorem sieveLocalWeight_probability {p : ℕ} (hp : 1 < p) :
    sieveLocalWeight p / (1 + sieveLocalWeight p) = (1 / p : ℝ) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp
    linarith
  unfold sieveLocalWeight
  field_simp
  simp [hp0]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem log_modulus_product (m : ι → ℕ) (hm : ∀ i, 0 < m i) (t : Finset ι) :
    Real.log ((∏ i ∈ t, m i : ℕ) : ℝ) = ∑ i ∈ t, Real.log (m i : ℝ) := by
  rw [Nat.cast_prod]
  exact Real.log_prod (fun i _ => by exact_mod_cast (Nat.ne_of_gt (hm i)))

theorem sieveMass_ge_half_euler_product (m : ι → ℕ) (hm : ∀ i, 1 < m i)
    (z : ℝ) (hz : 1 < z)
    (hmean : (∑ i, Real.log (m i : ℝ) / (m i : ℝ)) ≤ Real.log z / 2) :
    (1 / 2 : ℝ) * (∏ i, (1 + sieveLocalWeight (m i))) ≤ sieveMass m z := by
  let w := fun i => sieveLocalWeight (m i)
  let a := fun i => Real.log (m i : ℝ)
  have hw : ∀ i, 0 ≤ w i := fun i => (sieveLocalWeight_pos (hm i)).le
  have ha : ∀ i, 0 ≤ a i := by
    intro i
    exact Real.log_nonneg (by exact_mod_cast (hm i).le)
  have hmoment : subsetMoment w a Finset.univ ≤
      (Real.log z / 2) * ∑ t ∈ (Finset.univ : Finset ι).powerset, tensorWeight w t := by
    rw [subsetMoment_eq w a hw, subsetWeight_sum]
    have hprob : (∑ i, (w i / (1 + w i)) * a i) =
        ∑ i, Real.log (m i : ℝ) / (m i : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show w i / (1 + w i) = (1 / (m i) : ℝ) from sieveLocalWeight_probability (hm i)]
      dsimp only [a]
      ring
    rw [hprob]
    have hprod : 0 ≤ ∏ i, (1 + w i) :=
      Finset.prod_nonneg (fun i _ => by have := hw i; linarith)
    nlinarith [mul_le_mul_of_nonneg_left hmean hprod]
  have hmarkov := finite_weighted_markov (Finset.univ : Finset ι).powerset
    (tensorWeight w) (fun t => ∑ i ∈ t, a i)
    (fun t _ => Finset.prod_nonneg (fun i _ => hw i))
    (fun t _ => Finset.sum_nonneg (fun i _ => ha i))
    (Real.log_pos hz) hmoment
  have hfilter : (Finset.univ : Finset ι).powerset.filter (fun t => (∑ i ∈ t, a i) < Real.log z) =
      sieveSupport m z := by
    ext t
    simp only [Finset.powerset_univ, sieveSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    dsimp only [a]
    rw [← log_modulus_product m (fun i => Nat.zero_lt_of_lt (hm i)) t]
    exact Real.log_lt_log_iff
      (by exact_mod_cast Finset.prod_pos (fun i _ => Nat.zero_lt_of_lt (hm i))) (by linarith)
  rw [hfilter, subsetWeight_sum] at hmarkov
  exact hmarkov

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/PrimeBandMass.lean -/
section
/- # The finite Markov bound for prime-band sieve masses -/

namespace Erdos12Proof

noncomputable def primeLogWeightConstant : ℝ := Classical.choose prime_log_reciprocal_bound

theorem primeLogWeightConstant_pos : 0 < primeLogWeightConstant :=
  (Classical.choose_spec prime_log_reciprocal_bound).1

theorem primeLogWeightConstant_bound {x : ℝ} (hx : 2 ≤ x) :
    primeLogReciprocalSum x ≤ primeLogWeightConstant * Real.log x :=
  (Classical.choose_spec prime_log_reciprocal_bound).2 x hx

theorem primeBand_log_moment (x y : ℝ) :
    (∑ p : primeBand y x, Real.log (p : ℕ) / (p : ℕ)) ≤ primeLogReciprocalSum x := by
  rw [Finset.sum_coe_sort (s := primeBand y x) (f := fun p : ℕ => Real.log p / (p : ℝ))]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro p hp _
  have hprime := (Finset.mem_filter.mp hp).2
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hprime.one_le)) (Nat.cast_nonneg p)

theorem primeBand_mass_ge_half_euler (x y z : ℝ) (hx : 2 ≤ x) (hz : 1 < z)
    (hmean : primeLogWeightConstant * Real.log x ≤ Real.log z / 2) :
    (1 / 2 : ℝ) * primeBandEulerProduct y x ≤ finitePrimeSieveMass (primeBand y x) z := by
  have hm : ∀ p : primeBand y x, 1 < (p : ℕ) := fun p =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp p.property).1).2.one_lt
  have hlog : (∑ p : primeBand y x, Real.log (p : ℕ) / (p : ℕ)) ≤ Real.log z / 2 :=
    (primeBand_log_moment x y).trans ((primeLogWeightConstant_bound hx).trans hmean)
  have h := sieveMass_ge_half_euler_product (fun p : primeBand y x => (p : ℕ)) hm z hz hlog
  rw [Finset.prod_coe_sort (s := primeBand y x) (f := fun p : ℕ => 1 + sieveLocalWeight p)] at h
  rwa [finitePrimeSieveMass_eq] at h

theorem primeBand_mass_lower_bound :
    ∃ c > (0 : ℝ), ∀ x y z : ℝ, 2 ≤ y → y ≤ x → 1 < z →
      primeLogWeightConstant * Real.log x ≤ Real.log z / 2 →
      c * Real.log x / Real.log y ≤ finitePrimeSieveMass (primeBand y x) z := by
  obtain ⟨c, hc, hbound⟩ := primeBandEulerProduct_lower_bound
  refine ⟨c / 2, half_pos hc, ?_⟩
  intro x y z hy hyx hz hmean
  calc
    _ = (1 / 2 : ℝ) * (c * Real.log x / Real.log y) := by ring
    _ ≤ (1 / 2 : ℝ) * primeBandEulerProduct y x :=
      mul_le_mul_of_nonneg_left (hbound x y hy hyx) (by norm_num)
    _ ≤ _ := primeBand_mass_ge_half_euler x y z (hy.trans hyx) hz hmean

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/SieveDensityPrinciple.lean -/
section
/- # Uniform lower bounds for full-prime and prime-band sieve masses -/

namespace Erdos12Proof

noncomputable def sieveMassExponent : ℝ := 1 / (4 * (primeLogWeightConstant + 1))

theorem sieveMassExponent_pos : 0 < sieveMassExponent := by
  have hC := primeLogWeightConstant_pos
  unfold sieveMassExponent
  positivity

theorem sieveMassExponent_le_one : sieveMassExponent ≤ 1 := by
  have hC := primeLogWeightConstant_pos
  unfold sieveMassExponent
  apply (div_le_one (by positivity)).mpr
  linarith

theorem primeLogWeight_mul_sieveMassExponent_le_half :
    primeLogWeightConstant * sieveMassExponent ≤ 1 / 2 := by
  have hC := primeLogWeightConstant_pos
  unfold sieveMassExponent
  rw [mul_one_div]
  apply (div_le_iff₀ (by positivity)).mpr
  linarith

noncomputable def primeBandDensityConstant : ℝ :=
  Classical.choose primeBand_mass_lower_bound * sieveMassExponent

theorem primeBandDensityConstant_pos : 0 < primeBandDensityConstant :=
  mul_pos (Classical.choose_spec primeBand_mass_lower_bound).1 sieveMassExponent_pos

theorem primeBand_density_bound (z y : ℝ) (hz : 1 < z) (hy : 2 ≤ y)
    (hyz : y ≤ z ^ sieveMassExponent) :
    primeBandDensityConstant * Real.log z / Real.log y ≤
      finitePrimeSieveMass (primeBand y z) z := by
  have hz0 : 0 < z := by linarith
  have hlog : Real.log (z ^ sieveMassExponent) = sieveMassExponent * Real.log z :=
    Real.log_rpow hz0 _
  have hmean : primeLogWeightConstant * Real.log (z ^ sieveMassExponent) ≤ Real.log z / 2 := by
    rw [hlog]
    have h := mul_le_mul_of_nonneg_right primeLogWeight_mul_sieveMassExponent_le_half
      (Real.log_pos hz).le
    nlinarith
  have h := (Classical.choose_spec primeBand_mass_lower_bound).2
    (z ^ sieveMassExponent) y z hy hyz hz hmean
  have hxz : z ^ sieveMassExponent ≤ z :=
    Real.rpow_le_self_of_one_le hz.le sieveMassExponent_le_one
  calc
    _ = (Classical.choose primeBand_mass_lower_bound) *
        Real.log (z ^ sieveMassExponent) / Real.log y := by
      unfold primeBandDensityConstant
      rw [hlog]
      ring
    _ ≤ finitePrimeSieveMass (primeBand y (z ^ sieveMassExponent)) z := h
    _ ≤ _ := finitePrimeSieveMass_band_mono hxz z

noncomputable def fullSieveDensityConstant : ℝ := primeBandDensityConstant / Real.log 2

theorem fullSieveDensityConstant_pos : 0 < fullSieveDensityConstant :=
  div_pos primeBandDensityConstant_pos (Real.log_pos (by norm_num))

theorem fullSieve_density_bound (z : ℝ) (hz : 1 < z) (hlarge : 2 ≤ z ^ sieveMassExponent) :
    fullSieveDensityConstant * Real.log z ≤ finitePrimeSieveMass (primesThrough z) z := by
  calc
    _ = primeBandDensityConstant * Real.log z / Real.log 2 := by
      unfold fullSieveDensityConstant
      ring
    _ ≤ finitePrimeSieveMass (primeBand 2 z) z := primeBand_density_bound z 2 hz le_rfl hlarge
    _ ≤ _ := finitePrimeSieveMass_mono (Finset.filter_subset _ _)
      (fun p hp => (Finset.mem_filter.mp hp).2) z

theorem fullSieve_density_eventually :
    ∃ Z₀ : ℝ, 2 ≤ Z₀ ∧ ∀ z : ℝ, Z₀ ≤ z →
      fullSieveDensityConstant * Real.log z ≤ finitePrimeSieveMass (primesThrough z) z := by
  refine ⟨max 2 ((2 : ℝ) ^ sieveMassExponent⁻¹), le_max_left _ _, ?_⟩
  intro z hz
  have hz2 : 2 ≤ z := (le_max_left _ _).trans hz
  have hroot : ((2 : ℝ) ^ sieveMassExponent⁻¹) ^ sieveMassExponent = 2 := by
    rw [← Real.rpow_mul (by norm_num), inv_mul_cancel₀ sieveMassExponent_pos.ne', Real.rpow_one]
  apply fullSieve_density_bound z (by linarith)
  rw [← hroot]
  exact Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) ((le_max_right _ _).trans hz)
    sieveMassExponent_pos.le

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/SieveLevel.lean -/
section
/- # The sieve level used in the rough-block argument -/

namespace Erdos12Proof

noncomputable def restrictionSieveLevel (D N : ℝ) : ℝ := min D (N ^ (1 / 4 : ℝ)) / 2

theorem restrictionSieveLevel_properties (D N : ℝ) (hD : 0 < D) (hDN : D ≤ N)
    (hlogD : 16 ≤ Real.log D) :
    1 < restrictionSieveLevel D N ∧ restrictionSieveLevel D N ≤ D ∧
      (restrictionSieveLevel D N) ^ 4 ≤ N ∧ Real.log D / 8 ≤ Real.log (restrictionSieveLevel D N) := by
  have hN : 0 < N := lt_of_lt_of_le hD hDN
  have hD1 : 1 ≤ D := (Real.log_pos_iff hD.le).mp (by linarith) |>.le
  have hrootD : 0 < D ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hD _
  have hrootN : 0 < N ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hN _
  have hrootle : D ^ (1 / 4 : ℝ) ≤ min D (N ^ (1 / 4 : ℝ)) := le_min
    (Real.rpow_le_self_of_one_le hD1 (by norm_num))
    (Real.rpow_le_rpow hD.le hDN (by norm_num))
  have hzpos : 0 < restrictionSieveLevel D N :=
    div_pos (lt_min hD hrootN) (by norm_num)
  have hlower : D ^ (1 / 4 : ℝ) / 2 ≤ restrictionSieveLevel D N :=
    div_le_div_of_nonneg_right hrootle (by norm_num)
  have hloglower := Real.log_le_log (div_pos hrootD (by norm_num)) hlower
  rw [Real.log_div (ne_of_gt hrootD) (by norm_num), Real.log_rpow hD] at hloglower
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlogz : Real.log D / 8 ≤ Real.log (restrictionSieveLevel D N) := by
    linarith
  have hz : 1 < restrictionSieveLevel D N := (Real.log_pos_iff hzpos.le).mp (by linarith)
  have hzD : restrictionSieveLevel D N ≤ D := by
    unfold restrictionSieveLevel
    have := min_le_left D (N ^ (1 / 4 : ℝ))
    linarith
  have hzroot : restrictionSieveLevel D N ≤ N ^ (1 / 4 : ℝ) := by
    unfold restrictionSieveLevel
    have := min_le_right D (N ^ (1 / 4 : ℝ))
    linarith
  have hrootpower : (N ^ (1 / 4 : ℝ)) ^ 4 = N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    norm_num
  have hzpower := (pow_le_pow_left₀ hzpos.le hzroot 4).trans_eq hrootpower
  exact ⟨hz, hzD, hzpower, hlogz⟩

noncomputable def roughSieveExponent : ℝ := sieveMassExponent / 32

theorem roughSieveExponent_pos : 0 < roughSieveExponent := div_pos sieveMassExponent_pos (by norm_num)

noncomputable def roughSieveThreshold : ℝ := Real.exp (max 16 (128 / sieveMassExponent))

theorem roughSieveThreshold_pos : 0 < roughSieveThreshold := Real.exp_pos _

theorem roughSieveThreshold_log {D : ℝ} (hD : roughSieveThreshold ≤ D) :
    16 ≤ Real.log D ∧ 128 ≤ sieveMassExponent * Real.log D := by
  have hD0 : 0 < D := lt_of_lt_of_le roughSieveThreshold_pos hD
  have h := Real.log_le_log roughSieveThreshold_pos hD
  rw [roughSieveThreshold, Real.log_exp] at h
  refine ⟨(le_max_left _ _).trans h, ?_⟩
  have hlarge := (le_max_right (16 : ℝ) (128 / sieveMassExponent)).trans h
  simpa only [mul_comm] using (div_le_iff₀ sieveMassExponent_pos).mp hlarge

theorem roughSieve_prime_band_fits {D N K : ℝ} (hD : roughSieveThreshold ≤ D) (hDN : D ≤ N)
    (hK : 16 ≤ K) (hKD : K ≤ D ^ roughSieveExponent) :
    4 * K ≤ (restrictionSieveLevel D N) ^ sieveMassExponent := by
  have hD0 : 0 < D := lt_of_lt_of_le roughSieveThreshold_pos hD
  have hK0 : 0 < K := by linarith
  have hlogs := roughSieveThreshold_log hD
  obtain ⟨hz, _, _, hlogz⟩ := restrictionSieveLevel_properties D N hD0 hDN hlogs.1
  have hlogK := Real.log_le_log hK0 hKD
  rw [Real.log_rpow hD0] at hlogK
  have hlog4 : Real.log (4 : ℝ) ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    norm_num at h
    exact h
  have hlogband : Real.log (4 * K) ≤ sieveMassExponent * Real.log (restrictionSieveLevel D N) := by
    rw [Real.log_mul (by norm_num) hK0.ne']
    have hscaled := mul_le_mul_of_nonneg_left hlogz sieveMassExponent_pos.le
    unfold roughSieveExponent at hlogK
    nlinarith [hlogs.2]
  apply (Real.log_le_log_iff (by positivity)
    (Real.rpow_pos_of_pos (by linarith) sieveMassExponent)).mp
  rw [Real.log_rpow (by linarith : 0 < restrictionSieveLevel D N)]
  exact hlogband

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/SieveDensityBounds.lean -/
section
/- # Uniform sieve-density bounds at the rough-block scales -/

namespace Erdos12Proof

theorem fullSieve_density_rough (D N : ℝ) (hD : roughSieveThreshold ≤ D) (hDN : D ≤ N) :
    (fullSieveDensityConstant / 8) * Real.log D ≤
      finitePrimeSieveMass (primesThrough D) (restrictionSieveLevel D N) := by
  have hD0 : 0 < D := lt_of_lt_of_le roughSieveThreshold_pos hD
  have hlogs := roughSieveThreshold_log hD
  obtain ⟨hz, hzD, _, hlogz⟩ := restrictionSieveLevel_properties D N hD0 hDN hlogs.1
  have hscaled := mul_le_mul_of_nonneg_left hlogz sieveMassExponent_pos.le
  have hlarge : 2 ≤ (restrictionSieveLevel D N) ^ sieveMassExponent := by
    apply (Real.log_le_log_iff (by norm_num)
      (Real.rpow_pos_of_pos (by linarith) sieveMassExponent)).mp
    rw [Real.log_rpow (by linarith : 0 < restrictionSieveLevel D N)]
    have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h
      exact h
    nlinarith [hlogs.2]
  calc
    _ = fullSieveDensityConstant * (Real.log D / 8) := by ring
    _ ≤ fullSieveDensityConstant * Real.log (restrictionSieveLevel D N) :=
      mul_le_mul_of_nonneg_left hlogz fullSieveDensityConstant_pos.le
    _ ≤ finitePrimeSieveMass (primesThrough (restrictionSieveLevel D N))
        (restrictionSieveLevel D N) := fullSieve_density_bound _ hz hlarge
    _ ≤ _ := finitePrimeSieveMass_mono (primesThrough_mono hzD)
      (fun p hp => (Finset.mem_filter.mp hp).2) _

theorem primeBand_density_rough (D N K : ℝ) (hD : roughSieveThreshold ≤ D) (hDN : D ≤ N)
    (hK : 16 ≤ K) (hKD : K ≤ D ^ roughSieveExponent) :
    (primeBandDensityConstant / 16) * Real.log D / Real.log (2 * K) ≤
      finitePrimeSieveMass (primeBand (4 * K) D) (restrictionSieveLevel D N) := by
  have hD0 : 0 < D := lt_of_lt_of_le roughSieveThreshold_pos hD
  have hK0 : 0 < K := by linarith
  have hlogs := roughSieveThreshold_log hD
  obtain ⟨hz, hzD, _, hlogz⟩ := restrictionSieveLevel_properties D N hD0 hDN hlogs.1
  have hlog2K : 0 < Real.log (2 * K) := Real.log_pos (by linarith)
  have hlog4K : 0 < Real.log (4 * K) := Real.log_pos (by linarith)
  have hlogcomp : Real.log (4 * K) ≤ 2 * Real.log (2 * K) := by
    rw [show 4 * K = 2 * (2 * K) by ring, Real.log_mul (by norm_num) (by positivity)]
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ 2 * K)
    linarith
  have hfit := roughSieve_prime_band_fits hD hDN hK hKD
  have hbase := primeBand_density_bound (restrictionSieveLevel D N) (4 * K) hz (by linarith) hfit
  have hlogz0 : 0 < Real.log (restrictionSieveLevel D N) := Real.log_pos hz
  calc
    _ = primeBandDensityConstant * (Real.log D / 8) / (2 * Real.log (2 * K)) := by ring
    _ ≤ primeBandDensityConstant * Real.log (restrictionSieveLevel D N) /
        (2 * Real.log (2 * K)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hlogz primeBandDensityConstant_pos.le
    _ ≤ primeBandDensityConstant * Real.log (restrictionSieveLevel D N) /
        Real.log (4 * K) := div_le_div_of_nonneg_left
      (mul_pos primeBandDensityConstant_pos hlogz0).le hlog4K hlogcomp
    _ ≤ finitePrimeSieveMass (primeBand (4 * K) (restrictionSieveLevel D N))
        (restrictionSieveLevel D N) := hbase
    _ ≤ _ := finitePrimeSieveMass_band_mono hzD _

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/SiftedCounting.lean -/
section
/- # Counting sifted integers from the one-frequency dual estimate -/

namespace Erdos12Proof

noncomputable def sieveCardinalityConstant : ℝ := 2 * dualRestrictionConstant * Real.log 2

theorem sieveCardinalityConstant_pos : 0 < sieveCardinalityConstant :=
  mul_pos (mul_pos (by norm_num) dualRestrictionConstant_pos) (Real.log_pos (by norm_num))

theorem sifted_cardinality_bound {ι : Type*} [Fintype ι] (m : ι → ℕ) (T : Finset ℤ)
    (hprime : ∀ i, (m i).Prime) (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    (N z : ℝ) (hz : 1 < z) (hN : z ^ 4 ≤ N)
    (hinterval : ∀ n ∈ T, 0 ≤ (n : ℝ) ∧ (n : ℝ) ≤ N)
    (hsifted : ∀ n ∈ T, ∀ i, (n : ZMod (m i)) ≠ 0) :
    (T.card : ℝ) ≤ sieveCardinalityConstant * N / sieveMass m z := by
  classical
  have h := logarithmic_sifted_dual_bound m ({()} : Finset Unit) (fun _ => 1) (fun _ => 0)
    T hprime hcop (by simp [coefficientEnergy]) N 1 z (by norm_num) hz hN hinterval hsifted
      (by intro i _ j _ hij; exact (hij (Subsingleton.elim i j)).elim)
  have hcount : (T.card : ℝ) ≤ dualRestrictionConstant * ((N + 1) / sieveMass m z) * Real.log 2 := by
    simpa [trigPolynomial, unitExp, coefficientEnergy, coefficientMass, coefficientRatio] using h
  have hG := sieveMass_pos (fun i => (hprime i).one_lt) hz
  have hN1 : 1 ≤ N := (one_le_pow₀ hz.le).trans hN
  have hC := dualRestrictionConstant_pos
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  calc
    _ ≤ dualRestrictionConstant * ((N + 1) / sieveMass m z) * Real.log 2 := hcount
    _ ≤ dualRestrictionConstant * ((2 * N) / sieveMass m z) * Real.log 2 := by
      gcongr
      linarith
    _ = _ := by unfold sieveCardinalityConstant; ring

noncomputable def roughCardinalityConstant : ℝ :=
  8 * sieveCardinalityConstant / fullSieveDensityConstant

theorem roughCardinalityConstant_pos : 0 < roughCardinalityConstant :=
  div_pos (mul_pos (by norm_num) sieveCardinalityConstant_pos) fullSieveDensityConstant_pos

theorem rough_integer_cardinality_bound (T : Finset ℤ) (D N : ℝ)
    (hD : roughSieveThreshold ≤ D) (hDN : D ≤ N)
    (hinterval : ∀ n ∈ T, 0 ≤ (n : ℝ) ∧ (n : ℝ) ≤ N)
    (hrough : ∀ n ∈ T, ∀ p : ℕ, p.Prime → (p : ℝ) ≤ D → (n : ZMod p) ≠ 0) :
    (T.card : ℝ) ≤ roughCardinalityConstant * N / Real.log D := by
  let m : primesThrough D → ℕ := fun p => p
  have hprime : ∀ p, (m p).Prime := fun p => (Finset.mem_filter.mp p.property).2
  have hcop : ∀ p q, p ≠ q → (m p).Coprime (m q) := by
    intro p q hpq
    exact (Nat.coprime_primes (hprime p) (hprime q)).mpr (fun h => hpq (Subtype.ext h))
  have hD0 := lt_of_lt_of_le roughSieveThreshold_pos hD
  have hlogs := roughSieveThreshold_log hD
  obtain ⟨hz, _, hzN, _⟩ := restrictionSieveLevel_properties D N hD0 hDN hlogs.1
  have hcount := sifted_cardinality_bound m T hprime hcop N (restrictionSieveLevel D N)
    hz hzN hinterval (by
      intro n hn p
      exact hrough n hn p (hprime p) ((mem_primesThrough hD0.le).mp p.property).2)
  have hGlower : (fullSieveDensityConstant / 8) * Real.log D ≤
      sieveMass m (restrictionSieveLevel D N) := by
    change _ ≤ sieveMass (fun p : primesThrough D => (p : ℕ)) _
    rw [finitePrimeSieveMass_eq]
    exact fullSieve_density_rough D N hD hDN
  have hlog : 0 < Real.log D := by linarith [hlogs.1]
  have hN : 0 ≤ N := (lt_of_lt_of_le hD0 hDN).le
  have hC := sieveCardinalityConstant_pos
  have hden : 0 < (fullSieveDensityConstant / 8) * Real.log D :=
    mul_pos (div_pos fullSieveDensityConstant_pos (by norm_num)) hlog
  calc
    _ ≤ sieveCardinalityConstant * N / sieveMass m (restrictionSieveLevel D N) := hcount
    _ ≤ sieveCardinalityConstant * N / ((fullSieveDensityConstant / 8) * Real.log D) :=
      div_le_div_of_nonneg_left (mul_nonneg hC.le hN) hden hGlower
    _ = _ := by unfold roughCardinalityConstant; field_simp

theorem rough_natural_cardinality_bound (E : Finset ℕ) (D N : ℝ)
    (hD : roughSieveThreshold ≤ D) (hDN : D ≤ N)
    (hupper : ∀ n ∈ E, (n : ℝ) ≤ N) (hrough : ∀ n ∈ E, Rough D n) :
    (E.card : ℝ) ≤ roughCardinalityConstant * N / Real.log D := by
  let e : ℕ ↪ ℤ := ⟨fun n => n, Int.ofNat_injective⟩
  let T := E.map e
  have hinterval : ∀ n ∈ T, 0 ≤ (n : ℝ) ∧ (n : ℝ) ≤ N := by
    intro n hn
    obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hn
    change 0 ≤ ((k : ℤ) : ℝ) ∧ ((k : ℤ) : ℝ) ≤ N
    simpa only [Int.cast_natCast] using And.intro (Nat.cast_nonneg k) (hupper k hk)
  have hsifted : ∀ n ∈ T, ∀ p : ℕ, p.Prime → (p : ℝ) ≤ D → (n : ZMod p) ≠ 0 := by
    intro n hn p hp hpD hzero
    obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hn
    have hdiv : p ∣ k := (ZMod.natCast_eq_zero_iff k p).mp
      (by simpa only [e, Function.Embedding.coeFn_mk, Int.cast_natCast] using hzero)
    exact (not_lt_of_ge hpD) (hrough k hk p hp hdiv)
  have h := rough_integer_cardinality_bound T D N hD hDN hinterval hsifted
  simpa only [T, Finset.card_map] using h

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/RoughBlockScales.lean -/
section
/- # Density normalization and scale estimates for the rough-block argument -/

namespace Erdos12Proof

noncomputable def roughBlockDensity (E : Finset ℕ) (D : ℝ) (X : ℕ) : ℝ :=
  Real.log D * E.card / X

theorem roughBlockDensity_bound (E : Finset ℕ) (D : ℝ) (X : ℕ)
    (hD : roughSieveThreshold ≤ D) (hDX : D ≤ X)
    (hE : ∀ n ∈ E, Rough D n) (hupper : ∀ n ∈ E, (n : ℝ) ≤ 2 * X) :
    roughBlockDensity E D X ≤ 2 * roughCardinalityConstant := by
  have hD0 : 0 < D := lt_of_lt_of_le roughSieveThreshold_pos hD
  have hX : 0 < (X : ℝ) := hD0.trans_le hDX
  have hlog : 0 < Real.log D := by linarith [(roughSieveThreshold_log hD).1]
  have hcount := rough_natural_cardinality_bound E D (2 * X) hD (by linarith) hupper hE
  have hprod := (le_div_iff₀ hlog).mp hcount
  unfold roughBlockDensity
  apply (div_le_iff₀ hX).mpr
  nlinarith

theorem blockMass_density_identity (E : Finset ℕ) (D : ℝ) {X K : ℕ}
    (hX : 0 < X) (hK : 0 < K) :
    blockMass E (Real.log D / blockModulus X K) = roughBlockDensity E D X / (32 * K) := by
  have hXR : (X : ℝ) ≠ 0 := by exact_mod_cast hX.ne'
  have hKR : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  unfold blockMass roughBlockDensity blockModulus
  push_cast
  field_simp

theorem normalized_restriction_scale {g A U X K R G n : ℝ}
    (hg : 0 < g) (hA : 0 ≤ A) (hU : 0 < U) (hX : 0 < X) (hK : 0 < K)
    (hn : 0 ≤ n) (hG : g * U ≤ G) (hR : R ≤ A * X) :
    Real.sqrt ((R / G) * (n * (U / (32 * K * X)) ^ 2)) ≤
      Real.sqrt (A / g) * Real.sqrt (U * n / X) / (32 * K) := by
  have hGpos : 0 < G := (mul_pos hg hU).trans_le hG
  have hratio : R / G ≤ A * X / (g * U) := by
    exact (div_le_div_of_nonneg_right hR hGpos.le).trans
      (div_le_div_of_nonneg_left (mul_nonneg hA hX.le) (mul_pos hg hU) hG)
  have hraw : (R / G) * (n * (U / (32 * K * X)) ^ 2) ≤
      (A / g) * (U * n / X) / (32 * K) ^ 2 := by
    calc
      _ ≤ (A * X / (g * U)) * (n * (U / (32 * K * X)) ^ 2) :=
        mul_le_mul_of_nonneg_right hratio (mul_nonneg hn (sq_nonneg _))
      _ = _ := by field_simp
  have hAg : 0 ≤ A / g := div_nonneg hA hg.le
  have hun : 0 ≤ U * n / X := div_nonneg (mul_nonneg hU.le hn) hX.le
  have hnorm : Real.sqrt ((A / g) * (U * n / X) / (32 * K) ^ 2) =
      Real.sqrt (A / g) * Real.sqrt (U * n / X) / (32 * K) := by
    rw [Real.sqrt_div (mul_nonneg hAg hun), Real.sqrt_mul hAg,
      Real.sqrt_sq_eq_abs, abs_of_pos (by positivity : 0 < 32 * K)]
  exact (Real.sqrt_le_sqrt hraw).trans_eq hnorm

theorem quotient_partition_count {L d : ℕ} (hd : 0 < d) (hsize : 3 * d ≤ 4 * L) :
    3 * ((L / d + 1) * d) ≤ 7 * L := by
  have hdiv := Nat.div_mul_le_self L d
  have hd0 : d ≠ 0 := hd.ne'
  nlinarith

theorem partition_average_factor {L R d A q : ℝ} (hL : 0 < L) (hR : 0 ≤ R)
    (hd : 0 < d) (hA : 0 ≤ A) (hq : 0 < q) (hsize : R * d ≤ A * L) :
    L ^ (-1 / q) * R ^ (1 / q) ≤ A ^ (1 / q) * d ^ (-1 / q) := by
  have hratio : R / L ≤ A / d := (div_le_div_iff₀ hL hd).mpr hsize
  calc
    _ = (R / L) ^ (1 / q) := by
      rw [neg_div, Real.rpow_neg_eq_inv_rpow, ← Real.mul_rpow (inv_nonneg.mpr hL.le) hR]
      congr 1
      ring
    _ ≤ (A / d) ^ (1 / q) := Real.rpow_le_rpow (div_nonneg hR hL.le) hratio (one_div_pos.mpr hq).le
    _ = _ := by
      rw [neg_div, Real.rpow_neg_eq_inv_rpow, ← Real.mul_rpow hA (inv_nonneg.mpr hd.le)]
      congr 1

theorem block_logarithm_absorption {K : ℝ} (hK : 1 ≤ K) :
    (Real.log (2 * K)) ^ (1 / 8 : ℝ) ≤
      (3 * (2 : ℝ) ^ (1 / 3 : ℝ)) ^ (1 / 8 : ℝ) * K ^ (1 / 24 : ℝ) := by
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hlog0 : 0 ≤ Real.log (2 * K) := Real.log_nonneg (by linarith)
  have hlog := Real.log_le_rpow_div (x := 2 * K) (by positivity) (by norm_num : (0 : ℝ) < 1 / 3)
  have hupper : Real.log (2 * K) ≤ (3 * (2 : ℝ) ^ (1 / 3 : ℝ)) * K ^ (1 / 3 : ℝ) := by
    calc
      _ ≤ (2 * K) ^ (1 / 3 : ℝ) / (1 / 3 : ℝ) := hlog
      _ = _ := by rw [Real.mul_rpow (by norm_num) hK0.le]; ring
  have h := Real.rpow_le_rpow hlog0 hupper (by norm_num : (0 : ℝ) ≤ 1 / 8)
  rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hK0.le _),
    ← Real.rpow_mul hK0.le] at h
  norm_num at h
  exact h

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/BlockComparisonScales.lean -/
section
/- # Converting the geometric and rational cases to a common Fourier scale -/

namespace Erdos12Proof

theorem density_amplitude_bound {u B : ℝ} (hu : 0 ≤ u) (huB : u ≤ B) :
    u ≤ Real.sqrt B * Real.sqrt u := by
  calc
    u = Real.sqrt u * Real.sqrt u := (Real.mul_self_sqrt hu).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt huB) (Real.sqrt_nonneg u)

theorem density_mean_amplitude_bound {u B K : ℝ} (hu : 0 ≤ u) (huB : u ≤ B) (hK : 0 < K) :
    u / (32 * K) ≤ (Real.sqrt B / 32) * (Real.sqrt u / K) := by
  calc
    _ ≤ (Real.sqrt B * Real.sqrt u) / (32 * K) :=
      div_le_div_of_nonneg_right (density_amplitude_bound hu huB) (by positivity)
    _ = _ := by ring

theorem denominator_partition_decay {L d K : ℕ} (hL : 0 < L) (hd : 0 < d) (hK : 0 < K)
    (hsize : 3 * d ≤ 4 * L) (hroot : Real.sqrt (K : ℝ) ≤ d) :
    (L : ℝ) ^ (-4 / 9 : ℝ) * ((L / d + 1 : ℕ) : ℝ) ^ (4 / 9 : ℝ) ≤
      (7 / 3 : ℝ) ^ (4 / 9 : ℝ) * (K : ℝ) ^ (-2 / 9 : ℝ) := by
  have hLR : 0 < (L : ℝ) := by exact_mod_cast hL
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hKR : 0 < (K : ℝ) := by exact_mod_cast hK
  have hcount := quotient_partition_count hd hsize
  have hcountR : 3 * (((L / d + 1 : ℕ) : ℝ) * d) ≤ 7 * (L : ℝ) := by exact_mod_cast hcount
  have hratio : ((L / d + 1 : ℕ) : ℝ) * d ≤ (7 / 3 : ℝ) * L := by linarith
  have hfactor := partition_average_factor hLR (Nat.cast_nonneg (L / d + 1)) hdR
    (by norm_num : (0 : ℝ) ≤ 7 / 3) (by norm_num : (0 : ℝ) < 9 / 4) hratio
  norm_num at hfactor
  have hden := Real.rpow_le_rpow_of_nonpos (Real.sqrt_pos.mpr hKR) hroot
    (by norm_num : (-4 / 9 : ℝ) ≤ 0)
  have hrootPower : (Real.sqrt (K : ℝ)) ^ (-4 / 9 : ℝ) = (K : ℝ) ^ (-2 / 9 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hKR.le]
    norm_num
  rw [hrootPower] at hden
  simp only [neg_div] at hden ⊢
  simpa only [Nat.cast_add, Nat.cast_one] using
    hfactor.trans (mul_le_mul_of_nonneg_left hden (by positivity))

theorem blockGrid_denominator_partition_decay {K d : ℕ} (hK : 1 ≤ K) (hd : 0 < d)
    (hdK : d ≤ 4 * K) (hroot : Real.sqrt (K : ℝ) ≤ d) :
    (blockGridLength K : ℝ) ^ (-4 / 9 : ℝ) *
      ((blockGridLength K / d + 1 : ℕ) : ℝ) ^ (4 / 9 : ℝ) ≤
        (7 / 3 : ℝ) ^ (4 / 9 : ℝ) * (K : ℝ) ^ (-2 / 9 : ℝ) := by
  have hlen := (blockGrid_length_bounds hK).1
  exact denominator_partition_decay (blockGrid_length_pos hK) hd (by omega) (by omega) hroot

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/GeometricComparisonScales.lean -/
section
/- # Geometric estimates on the common block-comparison scale -/

namespace Erdos12Proof

theorem normalizedBlockMass_bound (E : Finset ℕ) {U X K B : ℝ}
    (hU : 0 ≤ U) (hX : 0 < X) (hK : 0 < K) (hB : U * E.card / X ≤ B) :
    blockMass E (U / (32 * K * X)) ≤
      (Real.sqrt B / 32) * (Real.sqrt (U * E.card / X) / K) := by
  have hid : blockMass E (U / (32 * K * X)) = (U * E.card / X) / (32 * K) := by
    unfold blockMass
    ring
  rw [hid]
  exact density_mean_amplitude_bound
    (div_nonneg (mul_nonneg hU (Nat.cast_nonneg _)) hX.le) hB hK

theorem normalizedBlockMass_weak_bound (E : Finset ℕ) {U X K B : ℝ}
    (hU : 0 ≤ U) (hX : 0 < X) (hK : 0 < K) (hB : U * E.card / X ≤ B) :
    blockMass E (U / (32 * K * X)) ≤
      Real.sqrt B * (Real.sqrt (U * E.card / X) / K) := by
  exact (normalizedBlockMass_bound E hU hX hK hB).trans
    (mul_le_mul_of_nonneg_right (div_le_self (Real.sqrt_nonneg B) (by norm_num))
      (div_nonneg (Real.sqrt_nonneg _) hK.le))

theorem small_denominator_decay {K L d : ℝ} (hK : 1 ≤ K) (hKL : K ≤ L)
    (hd : d ≤ Real.sqrt K) : d / L ≤ K ^ (-2 / 9 : ℝ) := by
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hL : 0 < L := hK0.trans_le hKL
  calc
    d / L ≤ Real.sqrt K / L := div_le_div_of_nonneg_right hd hL.le
    _ ≤ Real.sqrt K / K := div_le_div_of_nonneg_left (Real.sqrt_nonneg K) hK0 hKL
    _ = K ^ (-1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_sub_one hK0.ne']
      norm_num
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hK (by norm_num)

theorem cell_denominator_decay {K L X d : ℝ} (hK : 1 ≤ K) (hKL : K ≤ L)
    (hKX : K ≤ X) (hd : d ≤ 4 * K) : d / (L * X) ≤ 4 * K ^ (-2 / 9 : ℝ) := by
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hL : 0 < L := hK0.trans_le hKL
  have hX : 0 < X := hK0.trans_le hKX
  have hden : K * K ≤ L * X := mul_le_mul hKL hKX hK0.le hL.le
  calc
    d / (L * X) ≤ (4 * K) / (L * X) := div_le_div_of_nonneg_right hd (mul_nonneg hL.le hX.le)
    _ ≤ (4 * K) / (K * K) := div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = 4 * K ^ (-1 : ℝ) := by rw [Real.rpow_neg_one]; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hK (by norm_num)) (by norm_num)

theorem no_return_cell_decay {K L X : ℝ} (hK : 1 ≤ K) (hKL : K ≤ L) (hX : 0 < X) :
    1 / (2 * L * X * (1 / (100 * X))) ≤ 50 * K ^ (-2 / 9 : ℝ) := by
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hL : 0 < L := hK0.trans_le hKL
  calc
    _ = 50 / L := by field_simp; norm_num
    _ ≤ 50 / K := div_le_div_of_nonneg_left (by norm_num) hK0 hKL
    _ = 50 * K ^ (-1 : ℝ) := by rw [Real.rpow_neg_one]; rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hK (by norm_num)) (by norm_num)

theorem large_phase_decay {K L X b : ℝ} (hK : 1 ≤ K) (hKL : K ≤ L)
    (hX : 0 < X) (hb : 0 < b) (hphase : K ^ (1 / 4 : ℝ) ≤ 32 * K * X * b) :
    1 / (2 * L * X * b) ≤ 16 * K ^ (-2 / 9 : ℝ) := by
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hL : 0 < L := hK0.trans_le hKL
  calc
    _ ≤ 1 / (2 * K * X * b) := one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hKL (by norm_num)) hX.le) hb.le)
    _ = 16 / (32 * K * X * b) := by field_simp; norm_num
    _ ≤ 16 / K ^ (1 / 4 : ℝ) := div_le_div_of_nonneg_left (by norm_num)
      (Real.rpow_pos_of_pos hK0 _) hphase
    _ = 16 * K ^ (-1 / 4 : ℝ) := by rw [neg_div, Real.rpow_neg hK0.le]; rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hK (by norm_num)) (by norm_num)

theorem small_phase_error_decay {K X b : ℝ} (hK : 1 ≤ K)
    (hphase : 32 * K * X * b ≤ K ^ (1 / 4 : ℝ)) :
    4 * Real.pi * X * b ≤ (Real.pi / 8) * K ^ (-2 / 9 : ℝ) := by
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hratio : X * b ≤ K ^ (1 / 4 : ℝ) / (32 * K) := by
    apply (le_div_iff₀ (by positivity : 0 < 32 * K)).mpr
    nlinarith
  calc
    _ ≤ 4 * Real.pi * (K ^ (1 / 4 : ℝ) / (32 * K)) := by
      nlinarith [Real.pi_pos]
    _ = (Real.pi / 8) * K ^ (-3 / 4 : ℝ) := by
      rw [show 4 * Real.pi * (K ^ (1 / 4 : ℝ) / (32 * K)) =
        (Real.pi / 8) * (K ^ (1 / 4 : ℝ) / K) by ring, ← Real.rpow_sub_one hK0.ne']
      norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hK (by norm_num)) (by positivity)

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/MeanNorms.lean -/
section
/- # Bounds for finite uniform means from counting-measure norms -/

namespace Erdos12Proof

theorem finiteMean_lq_bound {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℂ) {q : ℝ} (hq : 1 < q) :
    ‖finiteMean f‖ ≤ (Fintype.card Ω : ℝ) ^ (-1 / q) * finiteLqNorm Finset.univ f q := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hqm : 0 < q - 1 := sub_pos.mpr hq
  have hconj : q.HolderConjugate (q / (q - 1)) := by
    rw [Real.holderConjugate_iff]
    refine ⟨hq, ?_⟩
    field_simp
    ring
  have hexp : 1 / (q / (q - 1)) = (q - 1) / q := by field_simp
  have hconst : finiteLqNorm Finset.univ (fun _ : Ω => (1 : ℂ)) (q / (q - 1)) =
      (Fintype.card Ω : ℝ) ^ ((q - 1) / q) := by
    simp only [finiteLqNorm, norm_one, Real.one_rpow, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one, hexp]
  have hsum := finiteLqNorm_holder Finset.univ f (fun _ => 1) hconj
  simp only [mul_one, hconst] at hsum
  have hcard : 0 < (Fintype.card Ω : ℝ) := by exact_mod_cast Fintype.card_pos
  have hpower : (Fintype.card Ω : ℝ) ^ ((q - 1) / q) / Fintype.card Ω =
      (Fintype.card Ω : ℝ) ^ (-1 / q) := by
    rw [← Real.rpow_sub_one hcard.ne']
    congr 1
    field_simp
    ring
  calc
    _ = ‖∑ x, f x‖ / Fintype.card Ω := by
      rw [finiteMean, norm_div, Complex.norm_natCast]
    _ ≤ (finiteLqNorm Finset.univ f q * (Fintype.card Ω : ℝ) ^ ((q - 1) / q)) /
        Fintype.card Ω := div_le_div_of_nonneg_right hsum hcard.le
    _ = _ := by rw [mul_div_assoc, hpower, mul_comm]

theorem finiteSet_mean_lq_bound {κ : Type*} (S : Finset κ) (hS : S.Nonempty)
    (f : κ → ℂ) {q : ℝ} (hq : 1 < q) :
    ‖(S.card : ℂ)⁻¹ * ∑ i ∈ S, f i‖ ≤ (S.card : ℝ) ^ (-1 / q) * finiteLqNorm S f q := by
  let : Nonempty S := hS.to_subtype
  have h := finiteMean_lq_bound (fun i : S => f i) hq
  simp only [finiteMean, Fintype.card_coe, finiteLqNorm] at h
  rw [Finset.sum_coe_sort (s := S) (f := f),
    Finset.sum_coe_sort (s := S) (f := fun i : κ => ‖f i‖ ^ q)] at h
  simpa only [finiteLqNorm, div_eq_mul_inv, mul_comm, mul_one] using h

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/NaturalRestriction.lean -/
section
/- # Restriction estimates for natural-number sets and orbit averages -/

namespace Erdos12Proof

def naturalIntegerSet (E : Finset ℕ) : Finset ℤ :=
  E.map ⟨fun n : ℕ => (n : ℤ), Int.ofNat_injective⟩

theorem naturalIntegerSet_fourier (E : Finset ℕ) (w : ℂ) (t : ℝ) :
    finiteFourierSum (naturalIntegerSet E) (fun _ => w) t =
      w * ∑ a ∈ E, unitExp (t * a) := by
  unfold naturalIntegerSet finiteFourierSum
  rw [Finset.sum_map, Finset.mul_sum]
  simp only [Function.Embedding.coeFn_mk, Int.cast_natCast]

theorem naturalIntegerSet_energy (E : Finset ℕ) (w : ℂ) :
    coefficientEnergy (naturalIntegerSet E) (fun _ => w) = (E.card : ℝ) * ‖w‖ ^ 2 := by
  simp only [coefficientEnergy, Finset.sum_const, naturalIntegerSet, Finset.card_map, nsmul_eq_mul]

theorem naturalIntegerSet_interval (E : Finset ℕ) (N : ℝ) (hE : ∀ n ∈ E, (n : ℝ) ≤ N) :
    ∀ n ∈ naturalIntegerSet E, 0 ≤ (n : ℝ) ∧ (n : ℝ) ≤ N := by
  intro n hn
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hn
  simpa only [Function.Embedding.coeFn_mk, Int.cast_natCast] using
    And.intro (Nat.cast_nonneg a) (hE a ha)

theorem naturalIntegerSet_sifted {ι : Type*} (m : ι → ℕ)
    (hprime : ∀ i, (m i).Prime) (E : Finset ℕ) (D : ℝ)
    (hE : ∀ n ∈ E, Rough D n) (hmD : ∀ i, (m i : ℝ) ≤ D) :
    ∀ n ∈ naturalIntegerSet E, ∀ i, (n : ZMod (m i)) ≠ 0 := by
  intro n hn i hzero
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hn
  have hdiv : m i ∣ a := (ZMod.natCast_eq_zero_iff a (m i)).mp
    (by simpa only [Function.Embedding.coeFn_mk, Int.cast_natCast] using hzero)
  exact (not_lt_of_ge (hmD i)) (hE a ha (m i) (hprime i) hdiv)

theorem rough_natural_restriction_lq {ι κ : Type*} [Fintype ι] (m : ι → ℕ)
    (hprime : ∀ i, (m i).Prime) (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    (E : Finset ℕ) (D N : ℝ) (hE : ∀ n ∈ E, Rough D n) (hmD : ∀ i, (m i : ℝ) ≤ D)
    (hinterval : ∀ n ∈ E, (n : ℝ) ≤ N) (w : ℂ) (S : Finset κ) (a : κ → ℝ)
    (q : ℝ) (hq : 2 < q) (δ z : ℝ) (hδ : 0 < δ) (hz : 1 < z) (hzN : z ^ 4 ≤ N)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      δ ≤ dist (a i : UnitAddCircle) (a j : UnitAddCircle)) :
    finiteLqNorm S (fun i => w * ∑ n ∈ E, unitExp (a i * n)) q ≤
      (restrictionMomentConstant q) ^ (1 / q) *
        Real.sqrt (((N + δ⁻¹) / sieveMass m z) * ((E.card : ℝ) * ‖w‖ ^ 2)) := by
  have h := sifted_restriction_lq m S a (naturalIntegerSet E) (fun _ => w)
    hprime hcop q hq N δ z hδ hz hzN (naturalIntegerSet_interval E N hinterval)
    (naturalIntegerSet_sifted m hprime E D hE hmD) hsep
  simpa only [naturalIntegerSet_fourier, naturalIntegerSet_energy, finiteLqNorm] using h

theorem blockGridFourier_as_orbit_mean (E : Finset ℕ) (c : ℝ) (start length : ℕ) (t : ℝ) :
    blockGridFourier E c start length t = finiteMean (fun j : Fin length =>
      (c : ℂ) * ∑ a ∈ E, unitExp (((start + j.val : ℕ) : ℝ) * t * a)) := by
  unfold blockGridFourier gridPhaseAverage
  rw [← finiteMean_sum, ← finiteMean_const_mul]
  congr 1
  funext j
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  push_cast
  ring

theorem blockGridFourier_separated_bound {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hprime : ∀ i, (m i).Prime) (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    (E : Finset ℕ) (D N : ℝ) (hE : ∀ n ∈ E, Rough D n) (hmD : ∀ i, (m i : ℝ) ≤ D)
    (hinterval : ∀ n ∈ E, (n : ℝ) ≤ N) (c : ℝ) (start : ℕ) {length : ℕ} (hL : 0 < length)
    (t q : ℝ) (hq : 2 < q) (δ z : ℝ) (hδ : 0 < δ) (hz : 1 < z) (hzN : z ^ 4 ≤ N)
    (hsep : ∀ i j : Fin length, i ≠ j →
      δ ≤ dist ((((start + i.val : ℕ) : ℝ) * t : ℝ) : UnitAddCircle)
        ((((start + j.val : ℕ) : ℝ) * t : ℝ) : UnitAddCircle)) :
    ‖blockGridFourier E c start length t‖ ≤ (length : ℝ) ^ (-1 / q) *
      ((restrictionMomentConstant q) ^ (1 / q) *
        Real.sqrt (((N + δ⁻¹) / sieveMass m z) * ((E.card : ℝ) * c ^ 2))) := by
  let : NeZero length := ⟨hL.ne'⟩
  have hq1 : 1 < q := by linarith
  have hmean := finiteMean_lq_bound
    (fun j : Fin length => (c : ℂ) * ∑ a ∈ E, unitExp (((start + j.val : ℕ) : ℝ) * t * a)) hq1
  have hrestrict := rough_natural_restriction_lq m hprime hcop E D N hE hmD hinterval
    (c : ℂ) Finset.univ (fun j : Fin length => ((start + j.val : ℕ) : ℝ) * t)
    q hq δ z hδ hz hzN (fun i _ j _ hij => hsep i j hij)
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hrestrict
  simp only [Fintype.card_fin] at hmean
  rw [blockGridFourier_as_orbit_mean]
  exact hmean.trans
    (mul_le_mul_of_nonneg_left hrestrict (Real.rpow_nonneg (Nat.cast_nonneg length) _))

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/FiniteNormPartition.lean -/
section
/- # Combining counting-measure norm bounds over a finite partition -/

namespace Erdos12Proof

theorem finiteLqNorm_partition {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (colour : α → β) (f : α → ℂ) {q C : ℝ} (hq : 0 < q) (hC : 0 ≤ C)
    (hf : ∀ b, finiteLqNorm (Finset.univ.filter (fun a => colour a = b)) f q ≤ C) :
    finiteLqNorm Finset.univ f q ≤ (Fintype.card β : ℝ) ^ (1 / q) * C := by
  classical
  have hfibre (b : β) : (∑ a : α with colour a = b, ‖f a‖ ^ q) ≤ C ^ q := by
    have h := Real.rpow_le_rpow (finiteLqNorm_nonneg _ f q) (hf b) hq.le
    unfold finiteLqNorm at h
    rw [← Real.rpow_mul (Finset.sum_nonneg (fun a _ => Real.rpow_nonneg (norm_nonneg _) _)),
      one_div_mul_cancel hq.ne', Real.rpow_one] at h
    exact h
  have hsum_eq : (∑ b : β, ∑ a : α with colour a = b, ‖f a‖ ^ q) =
      ∑ a : α, ‖f a‖ ^ q := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    simp
  have hsum : (∑ a : α, ‖f a‖ ^ q) ≤ (Fintype.card β : ℝ) * C ^ q := by
    rw [← hsum_eq]
    have htotal := Finset.sum_le_sum (s := Finset.univ (α := β)) (fun b _ => hfibre b)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using htotal
  have h := Real.rpow_le_rpow
    (Finset.sum_nonneg (fun a _ => Real.rpow_nonneg (norm_nonneg _) _)) hsum (one_div_pos.mpr hq).le
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg hC q),
    ← Real.rpow_mul hC, mul_one_div_cancel hq.ne', Real.rpow_one] at h
  exact h

theorem finiteMean_partition_bound {α β : Type*} [Fintype α] [Nonempty α]
    [Fintype β] [DecidableEq β] (colour : α → β) (f : α → ℂ)
    {q C : ℝ} (hq : 1 < q) (hC : 0 ≤ C)
    (hf : ∀ b, finiteLqNorm (Finset.univ.filter (fun a => colour a = b)) f q ≤ C) :
    ‖finiteMean f‖ ≤ (Fintype.card α : ℝ) ^ (-1 / q) *
      ((Fintype.card β : ℝ) ^ (1 / q) * C) := by
  exact (finiteMean_lq_bound f hq).trans
    (mul_le_mul_of_nonneg_left (finiteLqNorm_partition colour f (by linarith) hC hf)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/OrbitSeparation.lean -/
section
/- # Separation of consecutive orbit frequencies -/

namespace Erdos12Proof

theorem natural_orbit_distance {k l : ℕ} (hkl : k ≤ l) (t : ℝ) :
    dist (((k : ℝ) * t : ℝ) : UnitAddCircle) (((l : ℝ) * t : ℝ) : UnitAddCircle) =
      ‖((((l - k : ℕ) : ℝ) * t : ℝ) : UnitAddCircle)‖ := by
  rw [dist_comm, dist_eq_norm, ← AddCircle.coe_sub, Nat.cast_sub hkl, sub_mul]

theorem natural_orbit_separated (S : Finset ℕ) {B : ℕ} {t δ : ℝ}
    (hwidth : ∀ k ∈ S, ∀ l ∈ S, k < l + B)
    (hreturn : ∀ h : ℕ, 0 < h → h < B → δ ≤ ‖(((h : ℝ) * t : ℝ) : UnitAddCircle)‖) :
    ∀ k ∈ S, ∀ l ∈ S, k ≠ l →
      δ ≤ dist (((k : ℝ) * t : ℝ) : UnitAddCircle) (((l : ℝ) * t : ℝ) : UnitAddCircle) := by
  intro k hk l hl hkl
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · rw [natural_orbit_distance hlt.le]
    apply hreturn (l - k) (Nat.sub_pos_of_lt hlt)
    have hw := hwidth l hl k hk
    omega
  · rw [dist_comm, natural_orbit_distance hgt.le]
    apply hreturn (k - l) (Nat.sub_pos_of_lt hgt)
    have hw := hwidth k hk l hl
    omega

theorem rational_orbit_interval_separated (q : ℚ) (start : ℕ) {β : ℝ}
    (hβ : |β| ≤ 1 / (2 * (q.den : ℝ) ^ 2)) :
    ∀ k ∈ Finset.Ico start (start + q.den),
      ∀ l ∈ Finset.Ico start (start + q.den), k ≠ l →
        1 / (2 * (q.den : ℝ)) ≤
          dist (((k : ℝ) * ((q : ℝ) + β) : ℝ) : UnitAddCircle)
            (((l : ℝ) * ((q : ℝ) + β) : ℝ) : UnitAddCircle) := by
  apply natural_orbit_separated (B := q.den)
  · intro k hk l hl
    have hk' := Finset.mem_Ico.mp hk
    have hl' := Finset.mem_Ico.mp hl
    omega
  · intro h hh hhd
    exact reduced_rational_orbit_spacing q hh hhd hβ

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/RationalOrbitFibres.lean -/
section
/- # Short-return and rational-orbit partitions of grid frequencies -/

namespace Erdos12Proof

theorem blockGrid_orbit_separated (K : ℕ) (t δ : ℝ)
    (hreturn : ∀ h : ℕ, 0 < h → h ≤ 4 * K → δ ≤ ‖(((h : ℝ) * t : ℝ) : UnitAddCircle)‖) :
    ∀ i j : Fin (blockGridLength K), i ≠ j →
      δ ≤ dist ((((blockGridStart K + i.val : ℕ) : ℝ) * t : ℝ) : UnitAddCircle)
        ((((blockGridStart K + j.val : ℕ) : ℝ) * t : ℝ) : UnitAddCircle) := by
  let S := Finset.Ico (blockGridStart K) (blockGridStart K + blockGridLength K)
  have hlength : blockGridLength K ≤ 4 * K + 1 := by unfold blockGridLength; omega
  have hsep := natural_orbit_separated S (B := 4 * K + 1)
    (fun k hk l hl => by
      have hk' := Finset.mem_Ico.mp hk
      have hl' := Finset.mem_Ico.mp hl
      omega)
    (fun h hh hlt => hreturn h hh (by omega))
  intro i j hij
  apply hsep (blockGridStart K + i.val) _ (blockGridStart K + j.val) _
  · intro heq
    apply hij
    apply Fin.ext
    omega
  · change _ ∈ Finset.Ico _ _
    have hi := i.isLt
    simp only [Finset.mem_Ico]
    omega
  · change _ ∈ Finset.Ico _ _
    have hj := j.isLt
    simp only [Finset.mem_Ico]
    omega

def quotientColour (d length : ℕ) (i : Fin length) : Fin (length / d + 1) :=
  ⟨i.val / d, by
    have h : i.val / d ≤ length / d := Nat.div_le_div_right i.isLt.le
    omega⟩

theorem same_quotient_gap_lt {a b d : ℕ} (hd : 0 < d) (hab : a ≤ b)
    (hquot : a / d = b / d) : b - a < d := by
  have ha := Nat.mod_lt a hd
  have hb := Nat.mod_lt b hd
  have ha' := Nat.mod_add_div a d
  have hb' := Nat.mod_add_div b d
  rw [hquot] at ha'
  omega

theorem rational_orbit_same_quotient (r : ℚ) (start : ℕ) {length : ℕ}
    {β : ℝ} (hβ : |β| ≤ 1 / (2 * (r.den : ℝ) ^ 2))
    {i j : Fin length} (hij : i ≠ j) (hquot : quotientColour r.den length i = quotientColour r.den length j) :
    1 / (2 * (r.den : ℝ)) ≤
      dist ((((start + i.val : ℕ) : ℝ) * ((r : ℝ) + β) : ℝ) : UnitAddCircle)
        ((((start + j.val : ℕ) : ℝ) * ((r : ℝ) + β) : ℝ) : UnitAddCircle) := by
  have hquot' : i.val / r.den = j.val / r.den := congrArg Fin.val hquot
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [natural_orbit_distance (Nat.add_le_add_left hlt.le start), Nat.add_sub_add_left]
    exact reduced_rational_orbit_spacing r (Nat.sub_pos_of_lt hlt)
      (same_quotient_gap_lt r.den_pos hlt.le hquot') hβ
  · rw [dist_comm, natural_orbit_distance (Nat.add_le_add_left hgt.le start), Nat.add_sub_add_left]
    exact reduced_rational_orbit_spacing r (Nat.sub_pos_of_lt hgt)
      (same_quotient_gap_lt r.den_pos hgt.le hquot'.symm) hβ

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/RationalGridRestriction.lean -/
section
/- # Restriction along a rational orbit, including repeated denominator blocks -/

namespace Erdos12Proof

theorem blockGridFourier_rational_bound {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hprime : ∀ i, (m i).Prime) (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    (E : Finset ℕ) (D N : ℝ) (hE : ∀ n ∈ E, Rough D n) (hmD : ∀ i, (m i : ℝ) ≤ D)
    (hinterval : ∀ n ∈ E, (n : ℝ) ≤ N) (c : ℝ) (start : ℕ) {length : ℕ} (hL : 0 < length)
    (r : ℚ) (β : ℝ) (hβ : |β| ≤ 1 / (2 * (r.den : ℝ) ^ 2))
    (q : ℝ) (hq : 2 < q) (z : ℝ) (hz : 1 < z) (hzN : z ^ 4 ≤ N) :
    ‖blockGridFourier E c start length ((r : ℝ) + β)‖ ≤
      (length : ℝ) ^ (-1 / q) * (((length / r.den + 1 : ℕ) : ℝ) ^ (1 / q) *
        ((restrictionMomentConstant q) ^ (1 / q) *
          Real.sqrt (((N + 2 * r.den) / sieveMass m z) * ((E.card : ℝ) * c ^ 2)))) := by
  classical
  let : NeZero length := ⟨hL.ne'⟩
  let f : Fin length → ℂ := fun j => (c : ℂ) *
    ∑ a ∈ E, unitExp (((start + j.val : ℕ) : ℝ) * ((r : ℝ) + β) * a)
  let C : ℝ := (restrictionMomentConstant q) ^ (1 / q) *
    Real.sqrt (((N + 2 * r.den) / sieveMass m z) * ((E.card : ℝ) * c ^ 2))
  have hC : 0 ≤ C := mul_nonneg
    (Real.rpow_nonneg (restrictionMomentConstant_pos hq).le _) (Real.sqrt_nonneg _)
  have hf (b : Fin (length / r.den + 1)) :
      finiteLqNorm (Finset.univ.filter (fun j => quotientColour r.den length j = b)) f q ≤ C := by
    have h := rough_natural_restriction_lq m hprime hcop E D N hE hmD hinterval (c : ℂ)
      (Finset.univ.filter (fun j : Fin length => quotientColour r.den length j = b))
      (fun j : Fin length => ((start + j.val : ℕ) : ℝ) * ((r : ℝ) + β)) q hq
      (1 / (2 * (r.den : ℝ))) z (by positivity) hz hzN
      (fun i hi j hj hij => rational_orbit_same_quotient r start hβ hij
        ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm))
    simpa only [f, C, Complex.norm_real, Real.norm_eq_abs, sq_abs, one_div, inv_inv] using h
  have h := finiteMean_partition_bound (quotientColour r.den length) f (by linarith : 1 < q) hC hf
  rw [blockGridFourier_as_orbit_mean]
  simpa only [Fintype.card_fin, f, C] using h

theorem blockGridFourier_no_short_return {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hprime : ∀ i, (m i).Prime) (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    (E : Finset ℕ) (D N : ℝ) (hE : ∀ n ∈ E, Rough D n) (hmD : ∀ i, (m i : ℝ) ≤ D)
    (hinterval : ∀ n ∈ E, (n : ℝ) ≤ N) (c : ℝ) {K : ℕ} (hK : 1 ≤ K)
    (t q : ℝ) (hq : 2 < q) (δ z : ℝ) (hδ : 0 < δ) (hz : 1 < z) (hzN : z ^ 4 ≤ N)
    (hreturn : ∀ h : ℕ, 0 < h → h ≤ 4 * K → δ ≤ ‖(((h : ℝ) * t : ℝ) : UnitAddCircle)‖) :
    ‖blockGridFourier E c (blockGridStart K) (blockGridLength K) t‖ ≤
      (blockGridLength K : ℝ) ^ (-1 / q) * ((restrictionMomentConstant q) ^ (1 / q) *
        Real.sqrt (((N + δ⁻¹) / sieveMass m z) * ((E.card : ℝ) * c ^ 2))) := by
  exact blockGridFourier_separated_bound m hprime hcop E D N hE hmD hinterval c
    (blockGridStart K) (blockGrid_length_pos hK) t q hq δ z hδ hz hzN
    (blockGrid_orbit_separated K t δ hreturn)

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/FrequencyDichotomy.lean -/
section
/- # The frequency cases used in the uniform Fourier comparison -/

namespace Erdos12Proof

theorem frequency_dichotomy (K : ℕ) (t δ : ℝ) :
    (∀ h : ℕ, 0 < h → h ≤ 4 * K → δ ≤ ‖(((h : ℝ) * t : ℝ) : UnitAddCircle)‖) ∨
      ∃ r : ℚ, r.den ≤ 4 * K ∧ |t - (r : ℝ)| ≤ δ / r.den := by
  classical
  by_cases hsep : ∀ h : ℕ, 0 < h → h ≤ 4 * K → δ ≤ ‖(((h : ℝ) * t : ℝ) : UnitAddCircle)‖
  · exact Or.inl hsep
  · push Not at hsep
    obtain ⟨h, hh, hK, hreturn⟩ := hsep
    obtain ⟨r, hdr, herr⟩ := reduced_approximation_of_short_return hh t δ hreturn.le
    exact Or.inr ⟨r, hdr.trans hK, herr⟩

theorem rational_approximation_block_bounds {X β : ℝ} (hX : 1 ≤ X) (d : ℕ) (hd : 0 < d)
    (hdX : (d : ℝ) ≤ 4 * X) (hβ : |β| ≤ (1 / (100 * X)) / d) :
    |β| ≤ 1 / (2 * (d : ℝ) ^ 2) ∧ |β| ≤ 1 / (2 * (d : ℝ)) ∧
      ∀ a : ℕ, (a : ℝ) ≤ 2 * X → |(a : ℝ) * β| ≤ 1 / (2 * (d : ℝ)) := by
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hβ' : |β| ≤ 1 / (100 * X * (d : ℝ)) := by simpa only [div_div] using hβ
  constructor
  · apply hβ'.trans
    apply one_div_le_one_div_of_le (by positivity)
    have hmul := mul_le_mul_of_nonneg_right hdX hdR.le
    nlinarith
  constructor
  · apply hβ'.trans
    apply one_div_le_one_div_of_le (by positivity)
    have hmul := mul_le_mul_of_nonneg_right hX hdR.le
    nlinarith
  · intro a ha
    calc
      _ = (a : ℝ) * |β| := by rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg a)]
      _ ≤ (2 * X) * (1 / (100 * X * (d : ℝ))) :=
        mul_le_mul ha hβ' (abs_nonneg β) (by positivity)
      _ = 1 / (50 * (d : ℝ)) := by field_simp; norm_num
      _ ≤ _ := one_div_le_one_div_of_le (by positivity) (by nlinarith)

theorem blockGridFourier_add_int (E : Finset ℕ) (c : ℝ) (start length : ℕ) (t : ℝ) (n : ℤ) :
    blockGridFourier E c start length (t + n) = blockGridFourier E c start length t := by
  simp only [blockGridFourier, gridPhaseAverage_add_int]

theorem blockCellFourier_add_int (E : Finset ℕ) (c : ℝ) (start length : ℕ) (t : ℝ) (n : ℤ) :
    blockCellFourier E c start length (t + n) = blockCellFourier E c start length t := by
  simp only [blockCellFourier, cellPhaseAverage_add_int]

theorem rational_den_one_lift (r : ℚ) (hr : r.den = 1) : (r : ℝ) = r.num := by
  rw [Rat.cast_def, hr, Nat.cast_one, div_one]

theorem blockGridFourier_den_one (E : Finset ℕ) (c : ℝ) (start length : ℕ)
    (r : ℚ) (hr : r.den = 1) (β : ℝ) :
    blockGridFourier E c start length ((r : ℝ) + β) = blockGridFourier E c start length β := by
  rw [rational_den_one_lift r hr, add_comm, blockGridFourier_add_int]

theorem blockCellFourier_den_one (E : Finset ℕ) (c : ℝ) (start length : ℕ)
    (r : ℚ) (hr : r.den = 1) (β : ℝ) :
    blockCellFourier E c start length ((r : ℝ) + β) = blockCellFourier E c start length β := by
  rw [rational_den_one_lift r hr, add_comm, blockCellFourier_add_int]

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/GeometricGridComparison.lean -/
section
/- # The geometric frequency cases in the grid comparison -/

namespace Erdos12Proof

theorem blockMass_nonneg (E : Finset ℕ) {c : ℝ} (hc : 0 ≤ c) : 0 ≤ blockMass E c :=
  mul_nonneg hc (Nat.cast_nonneg _)

theorem blockGrid_small_denominator_bound (E : Finset ℕ) {c D K : ℝ} (hc : 0 ≤ c)
    (hE : ∀ a ∈ E, Rough D a) (start : ℕ) {length : ℕ} (hL : 0 < length)
    (hK : 1 ≤ K) (hKL : K ≤ length) (r : ℚ) (hr : 1 < r.den)
    (hrD : (r.den : ℝ) ≤ D) (hroot : (r.den : ℝ) ≤ Real.sqrt K) (β : ℝ)
    (hβ : ∀ a ∈ E, |(a : ℝ) * β| ≤ 1 / (2 * (r.den : ℝ))) :
    ‖blockGridFourier E c start length ((r : ℝ) + β)‖ ≤ blockMass E c * K ^ (-2 / 9 : ℝ) := by
  have h := blockGridFourier_near_rational E hc hE start hL r hr hrD β hβ
  calc
    _ ≤ blockMass E c * (r.den : ℝ) / length := h
    _ = blockMass E c * ((r.den : ℝ) / length) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (small_denominator_decay hK hKL hroot) (blockMass_nonneg E hc)

theorem blockCell_rational_decay (E : Finset ℕ) {c X K : ℝ} (hc : 0 ≤ c)
    (hK : 1 ≤ K) (hKX : K ≤ X) (hE : ∀ a ∈ E, X ≤ (a : ℝ))
    (start : ℕ) {length : ℕ} (hL : 0 < length) (hKL : K ≤ length)
    (r : ℚ) (hr : 1 < r.den) (hrK : (r.den : ℝ) ≤ 4 * K)
    (β : ℝ) (hβ : |β| ≤ 1 / (2 * (r.den : ℝ))) :
    ‖blockCellFourier E c start length ((r : ℝ) + β)‖ ≤ 4 * blockMass E c * K ^ (-2 / 9 : ℝ) := by
  have hX : 0 < X := (zero_lt_one.trans_le hK).trans_le hKX
  have hLR : 0 < (length : ℝ) := by exact_mod_cast hL
  have hdR : 0 < (r.den : ℝ) := by exact_mod_cast r.den_pos
  have hnorm := circle_norm_rational_unit_perturbation r (a := 1)
    (Nat.coprime_one_left _) hr β (by simpa only [Nat.cast_one, one_mul] using hβ)
  simp only [Nat.cast_one, one_mul] at hnorm
  have h := blockCellFourier_far E hc hX hE start hL ((r : ℝ) + β) (by positivity) hnorm
  calc
    _ ≤ blockMass E c / (2 * (length : ℝ) * X * (1 / (2 * (r.den : ℝ)))) := h
    _ = blockMass E c * ((r.den : ℝ) / ((length : ℝ) * X)) := by field_simp
    _ ≤ blockMass E c * (4 * K ^ (-2 / 9 : ℝ)) :=
      mul_le_mul_of_nonneg_left (cell_denominator_decay hK hKL hKX hrK) (blockMass_nonneg E hc)
    _ = _ := by ring

theorem blockCell_no_return_decay (E : Finset ℕ) {c X K : ℝ} (hc : 0 ≤ c)
    (hX : 0 < X) (hE : ∀ a ∈ E, X ≤ (a : ℝ)) (start : ℕ)
    {length : ℕ} (hL : 0 < length) (hK : 1 ≤ K) (hKL : K ≤ length) (t : ℝ)
    (ht : 1 / (100 * X) ≤ ‖(t : UnitAddCircle)‖) :
    ‖blockCellFourier E c start length t‖ ≤ 50 * blockMass E c * K ^ (-2 / 9 : ℝ) := by
  have h := blockCellFourier_far E hc hX hE start hL t (by positivity) ht
  calc
    _ ≤ blockMass E c / (2 * (length : ℝ) * X * (1 / (100 * X))) := h
    _ = blockMass E c * (1 / (2 * (length : ℝ) * X * (1 / (100 * X)))) := by ring
    _ ≤ blockMass E c * (50 * K ^ (-2 / 9 : ℝ)) :=
      mul_le_mul_of_nonneg_left (no_return_cell_decay hK hKL hX) (blockMass_nonneg E hc)
    _ = _ := by ring

theorem blockGridCell_large_phase (E : Finset ℕ) {c X K : ℝ} (hc : 0 ≤ c)
    (hX : 0 < X) (hE : ∀ a ∈ E, X ≤ (a : ℝ)) (start : ℕ)
    {length : ℕ} (hL : 0 < length) (hK : 1 ≤ K) (hKL : K ≤ length) (t : ℝ)
    (htsmall : |t| ≤ 1 / 2) (hsmall : ∀ a ∈ E, (a : ℝ) * |t| ≤ 1 / 2)
    (hphase : K ^ (1 / 4 : ℝ) ≤ 32 * K * X * |t|) :
    ‖blockGridFourier E c start length t‖ + ‖blockCellFourier E c start length t‖ ≤
      32 * blockMass E c * K ^ (-2 / 9 : ℝ) := by
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have ht : 0 < |t| := by
    by_contra! hn
    have heq : |t| = 0 := le_antisymm hn (abs_nonneg t)
    rw [heq, mul_zero] at hphase
    exact (not_le_of_gt (Real.rpow_pos_of_pos hK0 (1 / 4 : ℝ))) hphase
  have hnorm : ‖(t : UnitAddCircle)‖ = |t| :=
    (AddCircle.norm_coe_eq_abs_iff (p := 1) one_ne_zero).mpr (by simpa only [abs_one] using htsmall)
  have hgrid := blockGridFourier_small_phase E hc hX hE start hL t ht hsmall
  have hcell := blockCellFourier_far E hc hX hE start hL t ht hnorm.symm.le
  have hα : 0 ≤ blockMass E c := blockMass_nonneg E hc
  calc
    _ ≤ blockMass E c / (2 * (length : ℝ) * X * |t|) +
        blockMass E c / (2 * (length : ℝ) * X * |t|) := add_le_add hgrid hcell
    _ = (2 * blockMass E c) * (1 / (2 * (length : ℝ) * X * |t|)) := by ring
    _ ≤ (2 * blockMass E c) * (16 * K ^ (-2 / 9 : ℝ)) :=
      mul_le_mul_of_nonneg_left (large_phase_decay hK hKL hX ht hphase) (by positivity)
    _ = _ := by ring

theorem blockGridCell_small_phase (E : Finset ℕ) {c X K : ℝ} (hc : 0 ≤ c)
    (hE : ∀ a ∈ E, 0 < a ∧ (a : ℝ) ≤ 2 * X) (start : ℕ)
    {length : ℕ} (hL : 0 < length) (hK : 1 ≤ K) (t : ℝ)
    (hphase : 32 * K * X * |t| ≤ K ^ (1 / 4 : ℝ)) :
    ‖blockGridFourier E c start length t - blockCellFourier E c start length t‖ ≤
      (Real.pi / 8) * blockMass E c * K ^ (-2 / 9 : ℝ) := by
  have h := blockGridCellFourier_close E hc hE start hL t
  calc
    _ ≤ blockMass E c * (2 * Real.pi * (2 * X) * |t|) := h
    _ = blockMass E c * (4 * Real.pi * X * |t|) := by ring
    _ ≤ blockMass E c * ((Real.pi / 8) * K ^ (-2 / 9 : ℝ)) :=
      mul_le_mul_of_nonneg_left (small_phase_error_decay hK hphase) (blockMass_nonneg E hc)
    _ = _ := by ring

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/ScaledGridRestriction.lean -/
section
/- # Grid restriction estimates at the normalized rough-block scale -/

namespace Erdos12Proof

noncomputable def gridRestrictionScale (g : ℝ) : ℝ :=
  (restrictionMomentConstant (9 / 4)) ^ (4 / 9 : ℝ) * Real.sqrt (102 / g) / 32

theorem gridRestrictionScale_nonneg (g : ℝ) : 0 ≤ gridRestrictionScale g := by
  have hconst := restrictionMomentConstant_pos (q := 9 / 4) (by norm_num)
  unfold gridRestrictionScale
  positivity

theorem scaled_grid_no_short_return {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hprime : ∀ i, (m i).Prime) (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    (E : Finset ℕ) (D U g : ℝ) (hU : 0 < U) (hg : 0 < g)
    (hE : ∀ n ∈ E, Rough D n) (hmD : ∀ i, (m i : ℝ) ≤ D)
    {X K : ℕ} (hX : 0 < X) (hK : 1 ≤ K)
    (hinterval : ∀ n ∈ E, (n : ℝ) ≤ 2 * X)
    (z : ℝ) (hz : 1 < z) (hzN : z ^ 4 ≤ 2 * X) (hG : g * U ≤ sieveMass m z)
    (t : ℝ) (hreturn : ∀ h : ℕ, 0 < h → h ≤ 4 * K →
      1 / (100 * (X : ℝ)) ≤ ‖(((h : ℝ) * t : ℝ) : UnitAddCircle)‖) :
    ‖blockGridFourier E (U / (32 * (K : ℝ) * X)) (blockGridStart K) (blockGridLength K) t‖ ≤
      gridRestrictionScale g * (Real.sqrt (U * E.card / X) / K) * (K : ℝ) ^ (-4 / 9 : ℝ) := by
  have hXR : 0 < (X : ℝ) := by exact_mod_cast hX
  have hKR : 0 < (K : ℝ) := by exact_mod_cast (show 0 < K by omega)
  have hq : (2 : ℝ) < 9 / 4 := by norm_num
  have hraw := blockGridFourier_no_short_return m hprime hcop E D (2 * X) hE hmD hinterval
    (U / (32 * (K : ℝ) * X)) hK t (9 / 4) hq (1 / (100 * (X : ℝ))) z
    (by positivity) hz hzN hreturn
  rw [show (-1 / (9 / 4 : ℝ)) = -4 / 9 by norm_num,
    show (1 / (9 / 4 : ℝ)) = 4 / 9 by norm_num] at hraw
  have hscale := normalized_restriction_scale hg (by norm_num : (0 : ℝ) ≤ 102) hU hXR hKR
    (Nat.cast_nonneg E.card) hG
    (R := 2 * X + (1 / (100 * (X : ℝ)))⁻¹) (by simp only [one_div, inv_inv]; linarith)
  have hlen : (K : ℝ) ≤ blockGridLength K := by
    have h := (blockGrid_length_bounds hK).1
    exact_mod_cast (show K ≤ blockGridLength K by omega)
  have hpower := Real.rpow_le_rpow_of_nonpos hKR hlen (by norm_num : (-4 / 9 : ℝ) ≤ 0)
  have hC : 0 ≤ (restrictionMomentConstant (9 / 4)) ^ (4 / 9 : ℝ) :=
    Real.rpow_nonneg (restrictionMomentConstant_pos (q := 9 / 4) (by norm_num)).le _
  have hcombined := mul_le_mul hpower (mul_le_mul_of_nonneg_left hscale hC)
    (mul_nonneg hC (Real.sqrt_nonneg _)) (Real.rpow_nonneg hKR.le (-4 / 9 : ℝ))
  calc
    _ ≤ _ := hraw.trans hcombined
    _ = _ := by unfold gridRestrictionScale; ring

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/ScaledRationalGrid.lean -/
section
/- # The large-denominator case at the normalized block scale -/

namespace Erdos12Proof

theorem scaled_grid_large_denominator {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hprime : ∀ i, (m i).Prime) (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    (E : Finset ℕ) (D U g : ℝ) (hU : 0 < U) (hg : 0 < g)
    (hE : ∀ n ∈ E, Rough D n) (hmD : ∀ i, (m i : ℝ) ≤ D)
    {X K : ℕ} (hX : 0 < X) (hK : 1 ≤ K) (hKX : K ≤ X)
    (hinterval : ∀ n ∈ E, (n : ℝ) ≤ 2 * X)
    (z : ℝ) (hz : 1 < z) (hzN : z ^ 4 ≤ 2 * X) (hG : g * U ≤ sieveMass m z)
    (r : ℚ) (β : ℝ) (hβ : |β| ≤ 1 / (2 * (r.den : ℝ) ^ 2))
    (hdK : r.den ≤ 4 * K) (hroot : Real.sqrt (K : ℝ) ≤ r.den) :
    ‖blockGridFourier E (U / (32 * (K : ℝ) * X)) (blockGridStart K) (blockGridLength K)
      ((r : ℝ) + β)‖ ≤
        gridRestrictionScale g * (7 / 3 : ℝ) ^ (4 / 9 : ℝ) *
          (Real.sqrt (U * E.card / X) / K) * (K : ℝ) ^ (-2 / 9 : ℝ) := by
  have hXR : 0 < (X : ℝ) := by exact_mod_cast hX
  have hKR : 0 < (K : ℝ) := by exact_mod_cast (show 0 < K by omega)
  have hq : (2 : ℝ) < 9 / 4 := by norm_num
  have hraw := blockGridFourier_rational_bound m hprime hcop E D (2 * X) hE hmD hinterval
    (U / (32 * (K : ℝ) * X)) (blockGridStart K) (blockGrid_length_pos hK)
    r β hβ (9 / 4) hq z hz hzN
  rw [show (-1 / (9 / 4 : ℝ)) = -4 / 9 by norm_num,
    show (1 / (9 / 4 : ℝ)) = 4 / 9 by norm_num, ← mul_assoc] at hraw
  have hdXR : (r.den : ℝ) ≤ 4 * X := by
    have h1 : (r.den : ℝ) ≤ 4 * K := by exact_mod_cast hdK
    have h2 : (K : ℝ) ≤ X := by exact_mod_cast hKX
    linarith
  have hscale := normalized_restriction_scale hg (by norm_num : (0 : ℝ) ≤ 102) hU hXR hKR
    (Nat.cast_nonneg E.card) hG (R := 2 * X + 2 * r.den) (by linarith)
  have hpartition := blockGrid_denominator_partition_decay hK r.den_pos hdK hroot
  have hC : 0 ≤ (restrictionMomentConstant (9 / 4)) ^ (4 / 9 : ℝ) :=
    Real.rpow_nonneg (restrictionMomentConstant_pos (q := 9 / 4) hq).le _
  have hcombined := mul_le_mul hpartition (mul_le_mul_of_nonneg_left hscale hC)
    (mul_nonneg hC (Real.sqrt_nonneg _)) (by positivity)
  calc
    _ ≤ _ := hraw.trans hcombined
    _ = _ := by unfold gridRestrictionScale; ring

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/UniformBlockComparison.lean -/
section
/- # The uniform Fourier comparison for a rough block -/

namespace Erdos12Proof

noncomputable def uniformBlockComparisonConstant (g B : ℝ) : ℝ :=
  gridRestrictionScale g * (1 + (7 / 3 : ℝ) ^ (4 / 9 : ℝ)) + (100 + Real.pi) * Real.sqrt B

theorem uniformBlockComparisonConstant_nonneg (g B : ℝ) :
    0 ≤ uniformBlockComparisonConstant g B := by
  have h := gridRestrictionScale_nonneg g
  unfold uniformBlockComparisonConstant
  positivity

theorem uniformBlockComparison_coefficients (g B a C : ℝ)
    (ha : a ≤ 1 + (7 / 3 : ℝ) ^ (4 / 9 : ℝ)) (hC : C ≤ 100 + Real.pi) :
    gridRestrictionScale g * a + C * Real.sqrt B ≤ uniformBlockComparisonConstant g B := by
  exact add_le_add (mul_le_mul_of_nonneg_left ha (gridRestrictionScale_nonneg g))
    (mul_le_mul_of_nonneg_right hC (Real.sqrt_nonneg B))

theorem uniform_block_fourier_comparison {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hprime : ∀ i, (m i).Prime) (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    (E : Finset ℕ) (D U g B : ℝ) (hU : 0 < U) (hg : 0 < g)
    (hE : ∀ n ∈ E, Rough D n) (hmD : ∀ i, (m i : ℝ) ≤ D)
    {X K : ℕ} (hX : 0 < X) (hK : 1 ≤ K) (hKX : K ≤ X) (hKD : (4 * K : ℕ) ≤ D)
    (hinterval : ∀ n ∈ E, (X : ℝ) ≤ n ∧ (n : ℝ) ≤ 2 * X)
    (hDensity : U * E.card / X ≤ B)
    (z : ℝ) (hz : 1 < z) (hzN : z ^ 4 ≤ 2 * X) (hG : g * U ≤ sieveMass m z) (t : ℝ) :
    ‖blockGridFourier E (U / (32 * (K : ℝ) * X)) (blockGridStart K) (blockGridLength K) t -
      blockCellFourier E (U / (32 * (K : ℝ) * X)) (blockGridStart K) (blockGridLength K) t‖ ≤
        uniformBlockComparisonConstant g B * (Real.sqrt (U * E.card / X) / K) *
          (K : ℝ) ^ (-2 / 9 : ℝ) := by
  classical
  let c : ℝ := U / (32 * (K : ℝ) * X)
  let α : ℝ := blockMass E c
  let W : ℝ := Real.sqrt (U * E.card / X) / K
  let P : ℝ := (K : ℝ) ^ (-2 / 9 : ℝ)
  let start := blockGridStart K
  let length := blockGridLength K
  have hXR : 0 < (X : ℝ) := by exact_mod_cast hX
  have hKR : 0 < (K : ℝ) := by exact_mod_cast (show 0 < K by omega)
  have hKR1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hXR1 : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hKXR : (K : ℝ) ≤ X := by exact_mod_cast hKX
  have hc : 0 ≤ c := div_nonneg hU.le (by positivity)
  have hα : 0 ≤ α := blockMass_nonneg E hc
  have hW : 0 ≤ W := div_nonneg (Real.sqrt_nonneg _) hKR.le
  have hP : 0 ≤ P := Real.rpow_nonneg hKR.le _
  have hαW : α ≤ Real.sqrt B * W := normalizedBlockMass_weak_bound E hU.le hXR hKR hDensity
  have hL : 0 < length := blockGrid_length_pos hK
  have hKL : (K : ℝ) ≤ length := by
    have h := (blockGrid_length_bounds hK).1
    exact_mod_cast (show K ≤ length by dsimp [length]; omega)
  have hLower : ∀ a ∈ E, (X : ℝ) ≤ a := fun a ha => (hinterval a ha).1
  have hUpper : ∀ a ∈ E, (a : ℝ) ≤ 2 * X := fun a ha => (hinterval a ha).2
  have hPos : ∀ a ∈ E, 0 < a ∧ (a : ℝ) ≤ 2 * X := by
    intro a ha
    exact ⟨by exact_mod_cast hXR.trans_le (hLower a ha), hUpper a ha⟩
  have hmixed (a C : ℝ) (ha : a ≤ 1 + (7 / 3 : ℝ) ^ (4 / 9 : ℝ))
      (hC0 : 0 ≤ C) (hC : C ≤ 100 + Real.pi)
      (hgrid : ‖blockGridFourier E c start length t‖ ≤ gridRestrictionScale g * a * W * P)
      (hcell : ‖blockCellFourier E c start length t‖ ≤ C * α * P) :
      ‖blockGridFourier E c start length t - blockCellFourier E c start length t‖ ≤
        uniformBlockComparisonConstant g B * W * P := by
    calc
      _ ≤ ‖blockGridFourier E c start length t‖ + ‖blockCellFourier E c start length t‖ := norm_sub_le _ _
      _ ≤ gridRestrictionScale g * a * W * P + C * α * P := add_le_add hgrid hcell
      _ ≤ gridRestrictionScale g * a * W * P + C * (Real.sqrt B * W) * P :=
        add_le_add_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hαW hC0) hP) _
      _ = (gridRestrictionScale g * a + C * Real.sqrt B) * W * P := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (uniformBlockComparison_coefficients g B a C ha hC) hW) hP
  have hgeom (C : ℝ) (hC0 : 0 ≤ C) (hC : C ≤ 100 + Real.pi)
      (hbound : ‖blockGridFourier E c start length t - blockCellFourier E c start length t‖ ≤ C * α * P) :
      ‖blockGridFourier E c start length t - blockCellFourier E c start length t‖ ≤
        uniformBlockComparisonConstant g B * W * P := by
    calc
      _ ≤ C * α * P := hbound
      _ ≤ C * (Real.sqrt B * W) * P :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hαW hC0) hP
      _ = (gridRestrictionScale g * 0 + C * Real.sqrt B) * W * P := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (uniformBlockComparison_coefficients g B 0 C (by positivity) hC) hW) hP
  rcases frequency_dichotomy K t (1 / (100 * (X : ℝ))) with hreturn | ⟨r, hdK, herr⟩
  · apply hmixed 1 50
      (by linarith [Real.rpow_nonneg (show (0 : ℝ) ≤ 7 / 3 by norm_num) (4 / 9 : ℝ)])
      (by norm_num) (by nlinarith [Real.pi_pos])
    · have h := scaled_grid_no_short_return m hprime hcop E D U g hU hg hE hmD
        hX hK hUpper z hz hzN hG t hreturn
      have hdecay : (K : ℝ) ^ (-4 / 9 : ℝ) ≤ P :=
        Real.rpow_le_rpow_of_exponent_le hKR1 (by norm_num)
      simpa only [mul_one] using h.trans (mul_le_mul_of_nonneg_left hdecay
        (mul_nonneg (gridRestrictionScale_nonneg g) hW))
    · have ht := hreturn 1 (by norm_num) (by omega)
      simp only [Nat.cast_one, one_mul] at ht
      exact blockCell_no_return_decay E hc hXR hLower start hL hKR1 hKL t ht
  · let β : ℝ := t - r
    have ht : t = (r : ℝ) + β := by dsimp [β]; ring
    have hdXR : (r.den : ℝ) ≤ 4 * X := by
      have h1 : (r.den : ℝ) ≤ 4 * K := by exact_mod_cast hdK
      linarith
    have herrors := rational_approximation_block_bounds hXR1 r.den r.den_pos hdXR
      (show |β| ≤ (1 / (100 * (X : ℝ))) / r.den from herr)
    by_cases hr1 : r.den = 1
    · have hGridEq : blockGridFourier E c start length t = blockGridFourier E c start length β := by
        rw [ht, blockGridFourier_den_one E c start length r hr1 β]
      have hCellEq : blockCellFourier E c start length t = blockCellFourier E c start length β := by
        rw [ht, blockCellFourier_den_one E c start length r hr1 β]
      have hb : |β| ≤ 1 / 2 := by simpa only [hr1, Nat.cast_one, mul_one] using herrors.2.1
      have hsmall : ∀ a ∈ E, (a : ℝ) * |β| ≤ 1 / 2 := by
        intro a ha
        have h := herrors.2.2 a (hUpper a ha)
        simpa only [hr1, Nat.cast_one, mul_one, abs_mul,
          abs_of_nonneg (show (0 : ℝ) ≤ (a : ℝ) from Nat.cast_nonneg a)] using h
      by_cases hphase : (K : ℝ) ^ (1 / 4 : ℝ) ≤ 32 * (K : ℝ) * X * |β|
      · apply hgeom 32 (by norm_num) (by nlinarith [Real.pi_pos])
        rw [hGridEq, hCellEq]
        exact (norm_sub_le _ _).trans
          (blockGridCell_large_phase E hc hXR hLower start hL hKR1 hKL β hb hsmall hphase)
      · apply hgeom (Real.pi / 8) (by positivity) (by nlinarith [Real.pi_pos])
        rw [hGridEq, hCellEq]
        exact blockGridCell_small_phase E hc hPos start hL hKR1 β (lt_of_not_ge hphase).le
    · have hr : 1 < r.den := by have h := r.den_pos; omega
      have hcell : ‖blockCellFourier E c start length t‖ ≤ 4 * α * P := by
        have h := blockCell_rational_decay E hc hKR1 hKXR hLower start hL hKL r hr
          (by exact_mod_cast hdK) β herrors.2.1
        rwa [← ht] at h
      by_cases hroot : (r.den : ℝ) ≤ Real.sqrt (K : ℝ)
      · have hgrid : ‖blockGridFourier E c start length t‖ ≤ α * P := by
          have hrD : (r.den : ℝ) ≤ D := (by exact_mod_cast hdK : (r.den : ℝ) ≤ (4 * K : ℕ)).trans hKD
          have h := blockGrid_small_denominator_bound E hc hE start hL hKR1 hKL r hr hrD hroot β
            (fun a ha => herrors.2.2 a (hUpper a ha))
          rwa [← ht] at h
        apply hgeom 5 (by norm_num) (by nlinarith [Real.pi_pos])
        calc
          _ ≤ ‖blockGridFourier E c start length t‖ + ‖blockCellFourier E c start length t‖ := norm_sub_le _ _
          _ ≤ α * P + 4 * α * P := add_le_add hgrid hcell
          _ = _ := by ring
      · apply hmixed ((7 / 3 : ℝ) ^ (4 / 9 : ℝ)) 4 (by linarith) (by norm_num) (by nlinarith [Real.pi_pos])
        · have h := scaled_grid_large_denominator m hprime hcop E D U g hU hg hE hmD
            hX hK hKX hUpper z hz hzN hG r β herrors.1 hdK (lt_of_not_ge hroot).le
          rwa [← ht] at h
        · exact hcell

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/ScaledBlockNorms.lean -/
section
/- # Fourier norms of the large block and the comparison density -/

namespace Erdos12Proof

theorem blockModulus_cast (X K : ℕ) : (blockModulus X K : ℝ) = 32 * (K : ℝ) * X := by
  simp only [blockModulus, Nat.cast_mul, Nat.cast_ofNat]

theorem earlier_block_mass (E : Finset ℕ) (U : ℝ) (X K : ℕ) :
    blockMass E (U / blockModulus X K) = (U * E.card / X) / (32 * (K : ℝ)) := by
  rw [blockModulus_cast]
  unfold blockMass
  ring

theorem later_block_mass (T : Finset ℕ) (U : ℝ) (X K : ℕ) :
    blockMass T (U / blockModulus X K) = (U * T.card / ((K : ℝ) * X)) / 32 := by
  rw [blockModulus_cast]
  unfold blockMass
  ring

noncomputable def blockRestrictionNormConstant (g : ℝ) : ℝ :=
  (restrictionMomentConstant (9 / 4)) ^ (4 / 9 : ℝ) * Real.sqrt (2 / g)

theorem blockRestrictionNormConstant_nonneg (g : ℝ) : 0 ≤ blockRestrictionNormConstant g := by
  have h := restrictionMomentConstant_pos (q := 9 / 4) (by norm_num)
  unfold blockRestrictionNormConstant
  positivity

theorem scaled_later_block_norm {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hprime : ∀ i, (m i).Prime) (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    (T : Finset ℕ) (D U g : ℝ) (hU : 0 < U) (hg : 0 < g)
    (hT : ∀ n ∈ T, Rough D n) (hmD : ∀ i, (m i : ℝ) ≤ D)
    {X K : ℕ} [NeZero (blockModulus X K)] (hX : 0 < X) (hK : 0 < K)
    (hbound : ∀ n ∈ T, n < blockModulus X K)
    (z : ℝ) (hz : 1 < z) (hzM : z ^ 4 ≤ blockModulus X K) (hG : g * U ≤ sieveMass m z) :
    finiteLqNorm Finset.univ
      (cyclicFourier (fun x : ZMod (blockModulus X K) => (cyclicSetDensity T U x : ℂ))) (9 / 4) ≤
        blockRestrictionNormConstant g * Real.sqrt (U * T.card / ((K : ℝ) * X)) := by
  let α : ℝ := blockMass T (U / blockModulus X K)
  let v : ℝ := U * T.card / ((K : ℝ) * X)
  have hM : 0 < (blockModulus X K : ℝ) := by exact_mod_cast blockModulus_pos hX hK
  have hα : 0 ≤ α := blockMass_nonneg T (div_nonneg hU.le hM.le)
  have hv : 0 ≤ v := by positivity
  have hαv : α ≤ v := by
    change blockMass T (U / blockModulus X K) ≤ v
    rw [later_block_mass]
    exact div_le_self hv (by norm_num)
  have hq : (2 : ℝ) < 9 / 4 := by norm_num
  have hraw := roughSet_restriction m hprime hcop T D hT hmD hbound U hU.le (9 / 4) hq z hz hzM
  rw [show (1 / (9 / 4 : ℝ)) = 4 / 9 by norm_num] at hraw
  have hscale := (sieve_sqrt_scale hg hU hα hG).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hαv) (Real.sqrt_nonneg (2 / g)))
  have hC : 0 ≤ (restrictionMomentConstant (9 / 4)) ^ (4 / 9 : ℝ) :=
    Real.rpow_nonneg (restrictionMomentConstant_pos hq).le _
  exact (hraw.trans (mul_le_mul_of_nonneg_left hscale hC)).trans_eq (by
    unfold blockRestrictionNormConstant
    ring)

theorem scaled_comparison_density_norm (E : Finset ℕ) (U B : ℝ) (hU : 0 < U)
    {X K : ℕ} [NeZero (blockModulus X K)] (hX : 0 < X) (hK : 1 ≤ K)
    (hE : ∀ a ∈ E, X ≤ a ∧ a < 2 * X) (hDensity : U * E.card / X ≤ B) :
    finiteLqNorm Finset.univ
      (cyclicFourier (fun x : ZMod (blockModulus X K) =>
        (cyclicCellDensity E U (blockGridStart K) (blockGridLength K) x : ℂ))) (9 / 4) ≤
          8 * Real.sqrt B * (Real.sqrt (U * E.card / X) / K) := by
  let α : ℝ := blockMass E (U / blockModulus X K)
  have hKR : 0 < (K : ℝ) := by exact_mod_cast (show 0 < K by omega)
  have hXR : 0 < (X : ℝ) := by exact_mod_cast hX
  have hM : 0 < (blockModulus X K : ℝ) := by exact_mod_cast blockModulus_pos hX (by omega)
  have hL : 0 < blockGridLength K := blockGrid_length_pos hK
  have hLR : 0 < (blockGridLength K : ℝ) := by exact_mod_cast hL
  have hKL : (K : ℝ) ≤ blockGridLength K := by
    have h := (blockGrid_length_bounds hK).1
    exact_mod_cast (show K ≤ blockGridLength K by omega)
  have hα : 0 ≤ α := blockMass_nonneg E (div_nonneg hU.le hM.le)
  have hratio : (blockModulus X K : ℝ) / ((blockGridLength K : ℝ) * X) ≤ 64 := by
    apply (div_le_iff₀ (mul_pos hLR hXR)).mpr
    rw [blockModulus_cast]
    have hprod := mul_le_mul_of_nonneg_right hKL hXR.le
    nlinarith
  have hpoint (x : ZMod (blockModulus X K)) :
      cyclicCellDensity E U (blockGridStart K) (blockGridLength K) x ≤ 64 * α := by
    have h := cyclicCellDensity_upper E hU.le hXR (fun a ha => by exact_mod_cast (hE a ha).1)
      (blockGridStart K) hL (fun a ha n => blockCell_no_wrap hX hK (hE a ha).2 n.isLt) x
    have heq : blockMass E U / ((blockGridLength K : ℝ) * X) =
        ((blockModulus X K : ℝ) / ((blockGridLength K : ℝ) * X)) * α := by
      dsimp [α, blockMass]
      field_simp
    exact h.trans (heq ▸ mul_le_mul_of_nonneg_right hratio hα)
  have hEpos : ∀ a ∈ E, 0 < a := fun a ha => hX.trans_le (hE a ha).1
  have hmean := cyclicCellDensity_mean (M := blockModulus X K) E U hEpos (blockGridStart K) hL
  have hraw := cyclic_real_lq_bound
    (cyclicCellDensity (M := blockModulus X K) E U (blockGridStart K) (blockGridLength K)) (64 * α)
    (cyclicCellDensity_nonneg E hU.le _ _) hpoint (by norm_num : (2 : ℝ) < 9 / 4)
  rw [hmean, cell_sqrt_scale hα] at hraw
  have hαW : α ≤ Real.sqrt B * (Real.sqrt (U * E.card / X) / K) := by
    change blockMass E (U / blockModulus X K) ≤ _
    rw [blockModulus_cast]
    exact normalizedBlockMass_weak_bound E hU.le hXR hKR hDensity
  exact hraw.trans (by nlinarith)

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/ScaledGridNorms.lean -/
section
/- # The prime-band norm of the grid and the norm of its Fourier difference -/

namespace Erdos12Proof

theorem scaled_rough_grid_norm {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hprime : ∀ i, (m i).Prime) (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    (E : Finset ℕ) (D U g : ℝ) (hU : 0 < U) (hg : 0 < g)
    (hE : ∀ n ∈ E, Rough D n)
    {X K : ℕ} [NeZero (blockModulus X K)] (hX : 0 < X) (hK : 16 ≤ K)
    (hD : (4 * K : ℕ) ≤ D) (hinterval : ∀ a ∈ E, X ≤ a ∧ a < 2 * X)
    (hband : ∀ i, 4 * (K : ℝ) < m i ∧ (m i : ℝ) ≤ D)
    (z : ℝ) (hz : 1 < z) (hzM : z ^ 4 ≤ blockModulus X K)
    (hG : g * U / Real.log (2 * (K : ℝ)) ≤ sieveMass m z) :
    finiteLqNorm Finset.univ
      (cyclicFourier (fun x : ZMod (blockModulus X K) =>
        (cyclicGridDensity E U (blockGridStart K) (blockGridLength K) x : ℂ))) (9 / 4) ≤
      blockRestrictionNormConstant g * (Real.sqrt (U * E.card / X) / K) *
        Real.sqrt (Real.log (2 * (K : ℝ))) := by
  let α : ℝ := blockMass E (U / blockModulus X K)
  let u : ℝ := U * E.card / X
  have hK1 : 1 ≤ K := by omega
  have hKR : 0 < (K : ℝ) := by exact_mod_cast (show 0 < K by omega)
  have hKR1 : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hXR : 0 < (X : ℝ) := by exact_mod_cast hX
  have hM : 0 < (blockModulus X K : ℝ) := by exact_mod_cast blockModulus_pos hX (by omega)
  have hL : 0 < blockGridLength K := blockGrid_length_pos hK1
  have hKL : (K : ℝ) ≤ blockGridLength K := by
    have h := (blockGrid_length_bounds hK1).1
    exact_mod_cast (show K ≤ blockGridLength K by omega)
  have hα : 0 ≤ α := blockMass_nonneg E (div_nonneg hU.le hM.le)
  have hu : 0 ≤ u := by positivity
  have hαu : α ≤ u / K := by
    change blockMass E (U / blockModulus X K) ≤ u / K
    rw [earlier_block_mass]
    exact div_le_div_of_nonneg_left hu hKR (by nlinarith)
  have hlog : 0 < Real.log (2 * (K : ℝ)) := Real.log_pos (by nlinarith)
  have hsmooth : ∀ j : Fin (blockGridLength K), Smooth (4 * (K : ℝ)) (2 * (blockGridStart K + j.val)) := by
    intro j
    apply Smooth.mul
    · apply smooth_of_le (a := 2) (by norm_num)
      norm_num
      linarith
    · exact blockGrid_multiplier_smooth hK (by norm_cast) j
  have hbound : ∀ a ∈ E, ∀ j : Fin (blockGridLength K),
      2 * a * (blockGridStart K + j.val) < blockModulus X K := by
    intro a ha j
    exact blockGrid_no_wrap hX hK1 (hinterval a ha).1 (hinterval a ha).2 j
  have hq : (2 : ℝ) < 9 / 4 := by norm_num
  have hraw := roughGrid_restriction m hprime hcop E D (4 * (K : ℝ)) (by exact_mod_cast hD)
    hE (fun a ha => hX.trans_le (hinterval a ha).1) U hU.le (blockGridStart K) hL
    hsmooth hbound hband (9 / 4) hq z hz hzM
  rw [show (1 / (9 / 4 : ℝ)) = 4 / 9 by norm_num] at hraw
  have hscale := band_sqrt_scale hg hU hα hu hKR hKL hlog hαu hG
  have hC : 0 ≤ (restrictionMomentConstant (9 / 4)) ^ (4 / 9 : ℝ) :=
    Real.rpow_nonneg (restrictionMomentConstant_pos hq).le _
  exact (hraw.trans (mul_le_mul_of_nonneg_left hscale hC)).trans_eq (by
    unfold blockRestrictionNormConstant
    ring)

noncomputable def blockDifferenceNormConstant (C B : ℝ) : ℝ :=
  C + 8 * Real.sqrt B / Real.sqrt (Real.log 2)

theorem blockDifferenceNormConstant_nonneg {C : ℝ} (hC : 0 ≤ C) (B : ℝ) :
    0 ≤ blockDifferenceNormConstant C B := by
  unfold blockDifferenceNormConstant
  positivity

theorem block_difference_norm {κ : Type*} (S : Finset κ) (f g : κ → ℂ)
    {C B W K : ℝ} (hW : 0 ≤ W) (hK : 1 ≤ K)
    (hf : finiteLqNorm S f (9 / 4) ≤ C * W * Real.sqrt (Real.log (2 * K)))
    (hg : finiteLqNorm S g (9 / 4) ≤ 8 * Real.sqrt B * W) :
    finiteLqNorm S (fun k => f k - g k) (9 / 4) ≤
      blockDifferenceNormConstant C B * W * Real.sqrt (Real.log (2 * K)) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hsqrt2 : 0 < Real.sqrt (Real.log (2 : ℝ)) := Real.sqrt_pos.mpr hlog2
  have hsqrt : Real.sqrt (Real.log (2 : ℝ)) ≤ Real.sqrt (Real.log (2 * K)) :=
    Real.sqrt_le_sqrt (Real.log_le_log (by norm_num) (by linarith))
  have hsecond : 8 * Real.sqrt B * W ≤
      (8 * Real.sqrt B / Real.sqrt (Real.log 2)) * W * Real.sqrt (Real.log (2 * K)) := by
    calc
      _ = (8 * Real.sqrt B / Real.sqrt (Real.log 2)) * W * Real.sqrt (Real.log 2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hsqrt (by positivity)
  calc
    _ ≤ finiteLqNorm S f (9 / 4) + finiteLqNorm S g (9 / 4) := finiteLqNorm_sub_le S f g (by norm_num)
    _ ≤ C * W * Real.sqrt (Real.log (2 * K)) +
        (8 * Real.sqrt B / Real.sqrt (Real.log 2)) * W * Real.sqrt (Real.log (2 * K)) :=
      add_le_add hf (hg.trans hsecond)
    _ = _ := by unfold blockDifferenceNormConstant; ring

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/BlockInterpolation.lean -/
section
/- # The ninth-moment comparison obtained from the two Fourier estimates -/

namespace Erdos12Proof

noncomputable def interpolatedComparisonConstant (Csup Cq : ℝ) : ℝ :=
  Csup ^ (3 / 4 : ℝ) * Cq ^ (1 / 4 : ℝ) *
    (3 * (2 : ℝ) ^ (1 / 3 : ℝ)) ^ (1 / 8 : ℝ)

theorem interpolatedComparisonConstant_nonneg {Csup Cq : ℝ} (hs : 0 ≤ Csup) (hq : 0 ≤ Cq) :
    0 ≤ interpolatedComparisonConstant Csup Cq := by
  unfold interpolatedComparisonConstant
  positivity

theorem block_fourier_ninth_moment {κ : Type*} (S : Finset κ) (f : κ → ℂ)
    {Csup Cq W K : ℝ} (hs : 0 ≤ Csup) (hq : 0 ≤ Cq) (hW : 0 ≤ W) (hK : 1 ≤ K)
    (hsup : ∀ i ∈ S, ‖f i‖ ≤ Csup * W * K ^ (-2 / 9 : ℝ))
    (hsmall : finiteLqNorm S f (9 / 4) ≤ Cq * W * (Real.log (2 * K)) ^ (1 / 2 : ℝ)) :
    finiteLqNorm S f 9 ≤ interpolatedComparisonConstant Csup Cq * W * K ^ (-1 / 8 : ℝ) := by
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hlog0 : 0 ≤ Real.log (2 * K) := Real.log_nonneg (by linarith)
  have hU : 0 ≤ Csup * W * K ^ (-2 / 9 : ℝ) := by positivity
  have hinterp := finiteLqNorm_interpolate S f (p := 9) (q := 9 / 4)
    (by norm_num) (by norm_num) hU hsup
  norm_num at hinterp
  have hquarter := Real.rpow_le_rpow (finiteLqNorm_nonneg S f (9 / 4)) hsmall
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hraw : finiteLqNorm S f 9 ≤
      (Csup * W * K ^ (-2 / 9 : ℝ)) ^ (3 / 4 : ℝ) *
        (Cq * W * (Real.log (2 * K)) ^ (1 / 2 : ℝ)) ^ (1 / 4 : ℝ) := by
    apply hinterp.trans
    simpa only [neg_div] using
      (mul_le_mul_of_nonneg_left hquarter (Real.rpow_nonneg hU (3 / 4 : ℝ)))
  have hWpowers : W ^ (3 / 4 : ℝ) * W ^ (1 / 4 : ℝ) = W := by
    rw [← Real.rpow_add' hW (by norm_num)]
    norm_num
  have hKpowers : (K ^ (-2 / 9 : ℝ)) ^ (3 / 4 : ℝ) = K ^ (-1 / 6 : ℝ) := by
    rw [← Real.rpow_mul hK0.le]
    norm_num
  have hlogpowers : ((Real.log (2 * K)) ^ (1 / 2 : ℝ)) ^ (1 / 4 : ℝ) =
      (Real.log (2 * K)) ^ (1 / 8 : ℝ) := by
    rw [← Real.rpow_mul hlog0]
    norm_num
  have hfactor : (Csup * W * K ^ (-2 / 9 : ℝ)) ^ (3 / 4 : ℝ) *
      (Cq * W * (Real.log (2 * K)) ^ (1 / 2 : ℝ)) ^ (1 / 4 : ℝ) =
        (Csup ^ (3 / 4 : ℝ) * Cq ^ (1 / 4 : ℝ) * W) *
          (K ^ (-1 / 6 : ℝ) * (Real.log (2 * K)) ^ (1 / 8 : ℝ)) := by
    rw [Real.mul_rpow (mul_nonneg hs hW) (Real.rpow_nonneg hK0.le _),
      Real.mul_rpow hs hW, hKpowers,
      Real.mul_rpow (mul_nonneg hq hW) (Real.rpow_nonneg hlog0 _),
      Real.mul_rpow hq hW, hlogpowers]
    calc
      _ = (Csup ^ (3 / 4 : ℝ) * Cq ^ (1 / 4 : ℝ)) *
          (W ^ (3 / 4 : ℝ) * W ^ (1 / 4 : ℝ)) *
          (K ^ (-1 / 6 : ℝ) * (Real.log (2 * K)) ^ (1 / 8 : ℝ)) := by ring
      _ = _ := by rw [hWpowers]
  rw [hfactor] at hraw
  have hdecay : K ^ (-1 / 6 : ℝ) * (Real.log (2 * K)) ^ (1 / 8 : ℝ) ≤
      (3 * (2 : ℝ) ^ (1 / 3 : ℝ)) ^ (1 / 8 : ℝ) * K ^ (-1 / 8 : ℝ) := by
    calc
      _ ≤ K ^ (-1 / 6 : ℝ) *
          ((3 * (2 : ℝ) ^ (1 / 3 : ℝ)) ^ (1 / 8 : ℝ) * K ^ (1 / 24 : ℝ)) :=
        mul_le_mul_of_nonneg_left (block_logarithm_absorption hK) (Real.rpow_nonneg hK0.le _)
      _ = (3 * (2 : ℝ) ^ (1 / 3 : ℝ)) ^ (1 / 8 : ℝ) *
          (K ^ (-1 / 6 : ℝ) * K ^ (1 / 24 : ℝ)) := by ring
      _ = _ := by rw [← Real.rpow_add hK0]; norm_num
  have h := hraw.trans (mul_le_mul_of_nonneg_left hdecay (by positivity))
  simpa only [interpolatedComparisonConstant, mul_assoc, mul_left_comm, mul_comm] using h

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/BlockFourierNine.lean -/
section
/- # The ninth-moment Fourier bound for the actual two-block comparison -/

namespace Erdos12Proof

noncomputable def blockNinthMomentConstant (gFull gBand B : ℝ) : ℝ :=
  interpolatedComparisonConstant (uniformBlockComparisonConstant gFull B)
    (blockDifferenceNormConstant (blockRestrictionNormConstant gBand) B)

theorem blockNinthMomentConstant_nonneg (gFull gBand B : ℝ) :
    0 ≤ blockNinthMomentConstant gFull gBand B := by
  apply interpolatedComparisonConstant_nonneg
  · exact uniformBlockComparisonConstant_nonneg _ _
  · exact blockDifferenceNormConstant_nonneg (blockRestrictionNormConstant_nonneg _) _

theorem roughBlock_fourier_nine {ι κ : Type*} [Fintype ι] [Fintype κ]
    (mFull : ι → ℕ) (mBand : κ → ℕ)
    (hFullPrime : ∀ i, (mFull i).Prime) (hFullCop : ∀ i j, i ≠ j → (mFull i).Coprime (mFull j))
    (hBandPrime : ∀ i, (mBand i).Prime) (hBandCop : ∀ i j, i ≠ j → (mBand i).Coprime (mBand j))
    (E : Finset ℕ) (D U gFull gBand B : ℝ) (hU : 0 < U) (hgFull : 0 < gFull) (hgBand : 0 < gBand)
    (hE : ∀ n ∈ E, Rough D n) (hmFull : ∀ i, (mFull i : ℝ) ≤ D)
    {X K : ℕ} [NeZero (blockModulus X K)] (hX : 0 < X) (hK : 16 ≤ K) (hKX : K ≤ X)
    (hKD : (4 * K : ℕ) ≤ D) (hinterval : ∀ a ∈ E, X ≤ a ∧ a < 2 * X)
    (hDensity : U * E.card / X ≤ B)
    (hmBand : ∀ i, 4 * (K : ℝ) < mBand i ∧ (mBand i : ℝ) ≤ D)
    (zFull zBand : ℝ) (hzFull : 1 < zFull) (hzBand : 1 < zBand)
    (hzFullN : zFull ^ 4 ≤ 2 * X) (hzBandM : zBand ^ 4 ≤ blockModulus X K)
    (hGFull : gFull * U ≤ sieveMass mFull zFull)
    (hGBand : gBand * U / Real.log (2 * (K : ℝ)) ≤ sieveMass mBand zBand) :
    finiteLqNorm Finset.univ
      (fun k : ZMod (blockModulus X K) =>
        cyclicFourier (fun x => (cyclicGridDensity E U (blockGridStart K) (blockGridLength K) x : ℂ)) k -
        cyclicFourier (fun x => (cyclicCellDensity E U (blockGridStart K) (blockGridLength K) x : ℂ)) k) 9 ≤
      blockNinthMomentConstant gFull gBand B * (Real.sqrt (U * E.card / X) / K) *
        (K : ℝ) ^ (-1 / 8 : ℝ) := by
  have hK1 : 1 ≤ K := by omega
  have hKR : 0 < (K : ℝ) := by exact_mod_cast (show 0 < K by omega)
  have hKR1 : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hW : 0 ≤ Real.sqrt (U * E.card / X) / (K : ℝ) := div_nonneg (Real.sqrt_nonneg _) hKR.le
  have hgrid := scaled_rough_grid_norm mBand hBandPrime hBandCop E D U gBand hU hgBand hE
    hX hK hKD hinterval hmBand zBand hzBand hzBandM hGBand
  have hcell := scaled_comparison_density_norm E U B hU hX hK1 hinterval hDensity
  have hdiff := block_difference_norm Finset.univ
    (cyclicFourier (fun x : ZMod (blockModulus X K) =>
      (cyclicGridDensity E U (blockGridStart K) (blockGridLength K) x : ℂ)))
    (cyclicFourier (fun x : ZMod (blockModulus X K) =>
      (cyclicCellDensity E U (blockGridStart K) (blockGridLength K) x : ℂ))) hW hKR1 hgrid hcell
  rw [Real.sqrt_eq_rpow (Real.log (2 * (K : ℝ)))] at hdiff
  have hsup (k : ZMod (blockModulus X K)) :
      ‖cyclicFourier (fun x => (cyclicGridDensity E U (blockGridStart K) (blockGridLength K) x : ℂ)) k -
        cyclicFourier (fun x => (cyclicCellDensity E U (blockGridStart K) (blockGridLength K) x : ℂ)) k‖ ≤
      uniformBlockComparisonConstant gFull B * (Real.sqrt (U * E.card / X) / K) *
        (K : ℝ) ^ (-2 / 9 : ℝ) := by
    rw [cyclicGridDensity_fourier, cyclicCellDensity_fourier, blockModulus_cast]
    apply uniform_block_fourier_comparison mFull hFullPrime hFullCop E D U gFull B hU hgFull
      hE hmFull hX hK1 hKX hKD _ hDensity zFull hzFull hzFullN hGFull
    intro a ha
    exact ⟨by exact_mod_cast (hinterval a ha).1, by exact_mod_cast (hinterval a ha).2.le⟩
  have h := block_fourier_ninth_moment Finset.univ _
    (uniformBlockComparisonConstant_nonneg gFull B)
    (blockDifferenceNormConstant_nonneg (blockRestrictionNormConstant_nonneg gBand) B)
    hW hKR1 (fun k _ => hsup k) hdiff
  exact h

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/CyclicNormBounds.lean -/
section
/- # Norm bounds for the cyclic correlation identity -/

namespace Erdos12Proof

theorem finiteLqNorm_square {κ : Type*} (S : Finset κ) (f : κ → ℂ) {q : ℝ} (hq : 0 < q) :
    finiteLqNorm S (fun i => f i ^ 2) (q / 2) = (finiteLqNorm S f q) ^ 2 := by
  have hsum : (∑ i ∈ S, ‖f i ^ 2‖ ^ (q / 2)) = ∑ i ∈ S, ‖f i‖ ^ q := by
    apply Finset.sum_congr rfl
    intro i _
    rw [norm_pow, ← Real.rpow_two, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    ring
  have hnonneg : 0 ≤ ∑ i ∈ S, ‖f i‖ ^ q :=
    Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)
  unfold finiteLqNorm
  rw [hsum, ← Real.rpow_two, ← Real.rpow_mul hnonneg]
  congr 1
  field_simp

variable {M : ℕ} [NeZero M]

theorem cyclicLqNorm_neg (f : ZMod M → ℂ) (q : ℝ) :
    finiteLqNorm Finset.univ (fun k => f (-k)) q = finiteLqNorm Finset.univ f q := by
  unfold finiteLqNorm
  congr 1
  exact Fintype.sum_equiv (Equiv.neg (ZMod M)) _ _ (fun k => rfl)

theorem cyclicFourier_sub (f g : ZMod M → ℂ) (k : ZMod M) :
    cyclicFourier (fun x => f x - g x) k = cyclicFourier f k - cyclicFourier g k := by
  unfold cyclicFourier
  change (M : ℂ)⁻¹ * ZMod.dft (f - g) k = _
  rw [map_sub, Pi.sub_apply, mul_sub]

theorem cyclicCorrelation_sub (f g h₁ h₂ : ZMod M → ℂ) :
    cyclicCorrelation f g h₁ - cyclicCorrelation f g h₂ =
      cyclicCorrelation f g (fun x => h₁ x - h₂ x) := by
  simp only [cyclicCorrelation, finiteMean, mul_sub, Finset.sum_sub_distrib, sub_div]

theorem cyclicCorrelation_bound (f h : ZMod M → ℂ) :
    ‖cyclicCorrelation f f h‖ ≤ finiteLqNorm Finset.univ (cyclicFourier h) 9 *
      (finiteLqNorm Finset.univ (cyclicFourier f) (9 / 4)) ^ 2 := by
  have hpq : (9 : ℝ).HolderConjugate (9 / 8) :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hbound := finiteLqNorm_holder Finset.univ (cyclicFourier h)
    (fun k => (cyclicFourier f (-k)) ^ 2) hpq
  have hsquare : finiteLqNorm Finset.univ (fun k => (cyclicFourier f (-k)) ^ 2) (9 / 8) =
      (finiteLqNorm Finset.univ (fun k => cyclicFourier f (-k)) (9 / 4)) ^ 2 := by
    simpa only [show (9 / 4 : ℝ) / 2 = 9 / 8 by norm_num] using
      finiteLqNorm_square Finset.univ (fun k => cyclicFourier f (-k)) (by norm_num : (0 : ℝ) < 9 / 4)
  rw [hsquare, cyclicLqNorm_neg] at hbound
  rw [cyclicCorrelation_fourier]
  simpa only [pow_two, mul_assoc] using hbound

theorem cyclicCorrelation_replacement_bound (f b b₀ : ZMod M → ℂ) :
    ‖cyclicCorrelation f f b - cyclicCorrelation f f b₀‖ ≤
      finiteLqNorm Finset.univ (fun k => cyclicFourier b k - cyclicFourier b₀ k) 9 *
        (finiteLqNorm Finset.univ (cyclicFourier f) (9 / 4)) ^ 2 := by
  rw [cyclicCorrelation_sub]
  have h := cyclicCorrelation_bound f (fun x => b x - b₀ x)
  have hFourier : cyclicFourier (fun x => b x - b₀ x) =
      (fun k => cyclicFourier b k - cyclicFourier b₀ k) := funext (cyclicFourier_sub b b₀)
  rw [hFourier] at h
  exact h

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/CyclicPositiveComparison.lean -/
section
/- # Positive comparison functions for the forbidden cyclic correlation -/

namespace Erdos12Proof

variable {M : ℕ} [NeZero M]

theorem cyclicCorrelation_ofReal (t b : ZMod M → ℝ) :
    cyclicCorrelation (fun x => (t x : ℂ)) (fun x => (t x : ℂ)) (fun x => (b x : ℂ)) =
      ((finiteMean (fun x => finiteMean (fun y => t x * t y * b (x + y))) : ℝ) : ℂ) := by
  unfold cyclicCorrelation
  simp only [← Complex.ofReal_mul, finiteMean_complexCast]

theorem cyclicCorrelation_positive_lower (t b : ZMod M → ℝ) (c : ℝ)
    (ht : ∀ x, 0 ≤ t x)
    (hb : ∀ x y, t x ≠ 0 → t y ≠ 0 → c ≤ b (x + y)) :
    c * (finiteMean t) ^ 2 ≤
      finiteMean (fun x => finiteMean (fun y => t x * t y * b (x + y))) := by
  have hpoint (x y : ZMod M) : t x * t y * c ≤ t x * t y * b (x + y) := by
    by_cases hx : t x = 0
    · simp only [hx, zero_mul, le_refl]
    by_cases hy : t y = 0
    · simp only [hy, mul_zero, zero_mul, le_refl]
    exact mul_le_mul_of_nonneg_left (hb x y hx hy) (mul_nonneg (ht x) (ht y))
  have hmean := finiteMean_mono (fun x => finiteMean_mono (fun y => hpoint x y))
  have hid : finiteMean (fun x => finiteMean (fun y => t x * t y * c)) =
      c * (finiteMean t) ^ 2 := by
    simp only [finiteMean_mul_const, finiteMean_const_mul]
    ring
  rwa [hid] at hmean

theorem cyclicCorrelation_positive_norm_lower (t b : ZMod M → ℝ) (c : ℝ)
    (ht : ∀ x, 0 ≤ t x)
    (hb : ∀ x y, t x ≠ 0 → t y ≠ 0 → c ≤ b (x + y)) :
    c * (finiteMean t) ^ 2 ≤
      ‖cyclicCorrelation (fun x => (t x : ℂ)) (fun x => (t x : ℂ)) (fun x => (b x : ℂ))‖ := by
  rw [cyclicCorrelation_ofReal, Complex.norm_real, Real.norm_eq_abs]
  exact (cyclicCorrelation_positive_lower t b c ht hb).trans (le_abs_self _)

theorem cyclic_positive_comparison_bound (t b₀ : ZMod M → ℝ) (b : ZMod M → ℂ) (c : ℝ)
    (ht : ∀ x, 0 ≤ t x)
    (hb₀ : ∀ x y, t x ≠ 0 → t y ≠ 0 → c ≤ b₀ (x + y))
    (hzero : cyclicCorrelation (fun x => (t x : ℂ)) (fun x => (t x : ℂ)) b = 0) :
    c * (finiteMean t) ^ 2 ≤
      finiteLqNorm Finset.univ
        (fun k => cyclicFourier b k - cyclicFourier (fun x => (b₀ x : ℂ)) k) 9 *
      (finiteLqNorm Finset.univ (cyclicFourier (fun x => (t x : ℂ))) (9 / 4)) ^ 2 := by
  have hupper := cyclicCorrelation_replacement_bound (fun x => (t x : ℂ)) b
    (fun x => (b₀ x : ℂ))
  rw [hzero, zero_sub, norm_neg] at hupper
  exact (cyclicCorrelation_positive_norm_lower t b₀ c ht hb₀).trans hupper

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/TwoBlockTransfer.lean -/
section
/- # Converting the Fourier comparison into the two-block density bound -/

namespace Erdos12Proof

theorem two_block_scalar_transfer {u v K Cb Ct : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hK : 0 < K) (hCb : 0 ≤ Cb)
    (h : (u / (32 * K)) * (v / 32) ^ 2 ≤
      (Cb * (Real.sqrt u / K) * K ^ (-1 / 8 : ℝ)) * (Ct * Real.sqrt v) ^ 2) :
    Real.sqrt u * v ≤ 32768 * Cb * Ct ^ 2 * K ^ (-1 / 8 : ℝ) := by
  by_cases hu0 : u = 0
  · rw [hu0, Real.sqrt_zero, zero_mul]
    positivity
  by_cases hv0 : v = 0
  · rw [hv0, mul_zero]
    positivity
  have huPos : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
  have hvPos : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0)
  have hroot : 0 < Real.sqrt u * v := mul_pos (Real.sqrt_pos.mpr huPos) hvPos
  rw [mul_pow, Real.sq_sqrt hv] at h
  have hscaled := mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ 32768 * K)
  have hscaled' : u * v ^ 2 ≤
      (32768 * Cb * Ct ^ 2 * K ^ (-1 / 8 : ℝ)) * (Real.sqrt u * v) := by
    convert hscaled using 1 <;> field_simp
    norm_num
  have hsquare : (Real.sqrt u * v) ^ 2 ≤
      (32768 * Cb * Ct ^ 2 * K ^ (-1 / 8 : ℝ)) * (Real.sqrt u * v) := by
    simpa only [mul_pow, Real.sq_sqrt hu] using hscaled'
  by_contra! hbad
  have hpositive := mul_pos hroot (sub_pos.mpr hbad)
  nlinarith

theorem two_block_density_from_fourier {M : ℕ} [NeZero M]
    (t b₀ : ZMod M → ℝ) (b : ZMod M → ℂ) {u v K Cb Ct : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hK : 0 < K) (hCb : 0 ≤ Cb)
    (ht : ∀ x, 0 ≤ t x) (hmean : finiteMean t = v / 32)
    (hb₀ : ∀ x y, t x ≠ 0 → t y ≠ 0 → u / (32 * K) ≤ b₀ (x + y))
    (hzero : cyclicCorrelation (fun x => (t x : ℂ)) (fun x => (t x : ℂ)) b = 0)
    (hsmall : finiteLqNorm Finset.univ (cyclicFourier (fun x => (t x : ℂ))) (9 / 4) ≤
      Ct * Real.sqrt v)
    (hcomparison : finiteLqNorm Finset.univ
      (fun k => cyclicFourier b k - cyclicFourier (fun x => (b₀ x : ℂ)) k) 9 ≤
        Cb * (Real.sqrt u / K) * K ^ (-1 / 8 : ℝ)) :
    Real.sqrt u * v ≤ 32768 * Cb * Ct ^ 2 * K ^ (-1 / 8 : ℝ) := by
  have hcorrelation := cyclic_positive_comparison_bound t b₀ b (u / (32 * K)) ht hb₀ hzero
  rw [hmean] at hcorrelation
  have hpower := pow_le_pow_left₀
    (finiteLqNorm_nonneg Finset.univ (cyclicFourier (fun x => (t x : ℂ))) (9 / 4)) hsmall 2
  have hupper := mul_le_mul hcomparison hpower
    (sq_nonneg (finiteLqNorm Finset.univ (cyclicFourier (fun x => (t x : ℂ))) (9 / 4)))
    (by positivity : 0 ≤ Cb * (Real.sqrt u / K) * K ^ (-1 / 8 : ℝ))
  exact two_block_scalar_transfer hu hv hK hCb (hcorrelation.trans hupper)

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/RoughBlockCorrelation.lean -/
section
/- # Positivity and vanishing for the concrete rough-block correlation -/

namespace Erdos12Proof

theorem Rough.odd {D : ℝ} {n : ℕ} (hn : Rough D n) (hD : 2 ≤ D) : Odd n := by
  apply Nat.not_even_iff_odd.mp
  intro heven
  exact (not_lt_of_ge hD) (hn 2 Nat.prime_two (even_iff_two_dvd.mp heven))

theorem roughBlock_comparison_positive (E T : Finset ℕ) (D U : ℝ) (hU : 0 ≤ U)
    {X K : ℕ} (hX : 0 < X) (hK : 1 ≤ K) (hD : 2 ≤ D)
    (hE : ∀ a ∈ E, X ≤ a ∧ a < 2 * X)
    (hT : ∀ n ∈ T, K * X ≤ n ∧ n < 2 * (K * X))
    (hrough : ∀ n ∈ T, Rough D n)
    (x y : ZMod (blockModulus X K))
    (hx : cyclicSetDensity T U x ≠ 0) (hy : cyclicSetDensity T U y ≠ 0) :
    blockMass E (U / blockModulus X K) ≤
      cyclicCellDensity E U (blockGridStart K) (blockGridLength K) (x + y) := by
  obtain ⟨n, hn, hxn⟩ := cyclicSetDensity_support T U x hx
  obtain ⟨m, hm, hym⟩ := cyclicSetDensity_support T U y hy
  have heven := (Rough.odd (hrough n hn) hD).add_odd (Rough.odd (hrough m hm) hD)
  obtain ⟨ℓ, hℓ⟩ := heven
  have hsum : n + m = 2 * ℓ := by omega
  have hbounds : K * X ≤ ℓ ∧ ℓ ≤ 2 * (K * X) := by
    have hn' := hT n hn
    have hm' := hT m hm
    omega
  have hxy : x + y = ((2 * ℓ : ℕ) : ZMod (blockModulus X K)) := by
    rw [hxn, hym, ← Nat.cast_add, hsum]
  have hEpos : ∀ a ∈ E, 0 < a ∧ (a : ℝ) ≤ 2 * X := by
    intro a ha
    exact ⟨hX.trans_le (hE a ha).1, by exact_mod_cast (hE a ha).2.le⟩
  have hwindow := fun a ha => blockCell_covers_middle hX (hE a ha).1 (hE a ha).2 hbounds.1 hbounds.2
  have hcell := cyclicCellDensity_lower (M := blockModulus X K) E hU hEpos
    (blockGridStart K) (blockGrid_length_pos hK) ℓ hwindow
  have hXR : 0 < (X : ℝ) := by exact_mod_cast hX
  have hLR : 0 < (blockGridLength K : ℝ) := by exact_mod_cast blockGrid_length_pos hK
  have hKR : 0 < (K : ℝ) := by exact_mod_cast (show 0 < K by omega)
  have hlen : (blockGridLength K : ℝ) ≤ 5 * K := by exact_mod_cast (blockGrid_length_bounds hK).2
  have hden : (blockGridLength K : ℝ) * (2 * X) ≤ blockModulus X K := by
    rw [blockModulus_cast]
    have hmul := mul_le_mul_of_nonneg_right hlen (show (0 : ℝ) ≤ 2 * X by positivity)
    nlinarith
  have hmass : blockMass E (U / blockModulus X K) = blockMass E U / blockModulus X K := by
    unfold blockMass
    ring
  rw [hxy, hmass]
  exact (div_le_div_of_nonneg_left (blockMass_nonneg E hU) (by positivity) hden).trans hcell

theorem roughBlock_correlation_zero {A : Set ℕ} (hA : PropertyP A) (E T : Finset ℕ)
    (hEA : ∀ a ∈ E, a ∈ A) (hTA : ∀ n ∈ T, n ∈ A) (D U : ℝ)
    {X K : ℕ} [NeZero (blockModulus X K)] (hX : 0 < X) (hK : 16 ≤ K)
    (hKD : (4 * K : ℕ) ≤ D)
    (hE : ∀ a ∈ E, X ≤ a ∧ a < 2 * X)
    (hT : ∀ n ∈ T, K * X ≤ n ∧ n < 2 * (K * X))
    (hrough : ∀ n ∈ T, Rough D n) :
    cyclicCorrelation
      (fun x : ZMod (blockModulus X K) => (cyclicSetDensity T U x : ℂ))
      (fun x => (cyclicSetDensity T U x : ℂ))
      (fun x => (cyclicGridDensity E U (blockGridStart K) (blockGridLength K) x : ℂ)) = 0 := by
  have hK1 : 1 ≤ K := by omega
  exact rough_grid_correlation_zero hA E T hEA hTA D hrough (blockGridStart K) (blockGridLength K)
    (by have h := blockGrid_start_ge_four hK; omega)
    (blockGrid_multiplier_smooth hK hKD)
    (fun a ha n hn => block_earlier_lt_later (by omega) (hE a ha).2 (hT n hn).1)
    (fun n hn m hm => block_later_sum_no_wrap hX (by omega) (hT n hn).2 (hT m hm).2)
    (fun a ha j => blockGrid_no_wrap hX hK1 (hE a ha).1 (hE a ha).2 j) U U

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/TwoBlockAssembly.lean -/
section
/- # The two-block estimate from the verified sieve mass bounds -/

namespace Erdos12Proof

noncomputable def twoBlockTransferConstant (gFull gBand B : ℝ) : ℝ :=
  32768 * blockNinthMomentConstant gFull gBand B * (blockRestrictionNormConstant gFull) ^ 2

theorem twoBlockTransferConstant_nonneg (gFull gBand B : ℝ) :
    0 ≤ twoBlockTransferConstant gFull gBand B := by
  have h := blockNinthMomentConstant_nonneg gFull gBand B
  unfold twoBlockTransferConstant
  positivity

theorem two_block_estimate_of_sieve_masses {ι κ : Type*} [Fintype ι] [Fintype κ]
    (mFull : ι → ℕ) (mBand : κ → ℕ)
    (hFullPrime : ∀ i, (mFull i).Prime) (hFullCop : ∀ i j, i ≠ j → (mFull i).Coprime (mFull j))
    (hBandPrime : ∀ i, (mBand i).Prime) (hBandCop : ∀ i j, i ≠ j → (mBand i).Coprime (mBand j))
    {A : Set ℕ} (hA : PropertyP A) (E T : Finset ℕ)
    (hEA : ∀ a ∈ E, a ∈ A) (hTA : ∀ a ∈ T, a ∈ A)
    (D U gFull gBand B : ℝ) (hU : 0 < U) (hgFull : 0 < gFull) (hgBand : 0 < gBand)
    (hE : ∀ n ∈ E, Rough D n) (hT : ∀ n ∈ T, Rough D n)
    (hmFull : ∀ i, (mFull i : ℝ) ≤ D)
    {X K : ℕ} [NeZero (blockModulus X K)] (hX : 0 < X) (hK : 16 ≤ K) (hKX : K ≤ X)
    (hKD : (4 * K : ℕ) ≤ D) (hEinterval : ∀ a ∈ E, X ≤ a ∧ a < 2 * X)
    (hTinterval : ∀ n ∈ T, K * X ≤ n ∧ n < 2 * (K * X))
    (hDensity : U * E.card / X ≤ B)
    (hmBand : ∀ i, 4 * (K : ℝ) < mBand i ∧ (mBand i : ℝ) ≤ D)
    (zSmall zLarge zBand : ℝ) (hzSmall : 1 < zSmall) (hzLarge : 1 < zLarge) (hzBand : 1 < zBand)
    (hzSmallN : zSmall ^ 4 ≤ 2 * X) (hzLargeM : zLarge ^ 4 ≤ blockModulus X K)
    (hzBandM : zBand ^ 4 ≤ blockModulus X K)
    (hGSmall : gFull * U ≤ sieveMass mFull zSmall)
    (hGLarge : gFull * U ≤ sieveMass mFull zLarge)
    (hGBand : gBand * U / Real.log (2 * (K : ℝ)) ≤ sieveMass mBand zBand) :
    Real.sqrt (U * E.card / X) * (U * T.card / ((K : ℝ) * X)) ≤
      twoBlockTransferConstant gFull gBand B * (K : ℝ) ^ (-1 / 8 : ℝ) := by
  let u : ℝ := U * E.card / X
  let v : ℝ := U * T.card / ((K : ℝ) * X)
  let t : ZMod (blockModulus X K) → ℝ := cyclicSetDensity T U
  let b₀ : ZMod (blockModulus X K) → ℝ :=
    cyclicCellDensity E U (blockGridStart K) (blockGridLength K)
  let b : ZMod (blockModulus X K) → ℂ :=
    fun x => (cyclicGridDensity E U (blockGridStart K) (blockGridLength K) x : ℂ)
  have hK1 : 1 ≤ K := by omega
  have hK0 : 0 < K := by omega
  have hKR : 0 < (K : ℝ) := by exact_mod_cast hK0
  have hu : 0 ≤ u := by positivity
  have hv : 0 ≤ v := by positivity
  have hD2 : 2 ≤ D := by
    have hKReal : (16 : ℝ) ≤ K := by exact_mod_cast hK
    have hKDReal : 4 * (K : ℝ) ≤ D := by exact_mod_cast hKD
    linarith
  have ht : ∀ x, 0 ≤ t x := cyclicSetDensity_nonneg T hU.le
  have hmean : finiteMean t = v / 32 := by
    rw [cyclicSetDensity_mean, later_block_mass]
  have hlower : ∀ x y, t x ≠ 0 → t y ≠ 0 → u / (32 * (K : ℝ)) ≤ b₀ (x + y) := by
    intro x y hx hy
    have h := roughBlock_comparison_positive E T D U hU.le hX hK1 hD2
      hEinterval hTinterval hT x y hx hy
    rwa [earlier_block_mass] at h
  have hzero : cyclicCorrelation (fun x => (t x : ℂ)) (fun x => (t x : ℂ)) b = 0 :=
    roughBlock_correlation_zero hA E T hEA hTA D U hX hK hKD hEinterval hTinterval hT
  have hTbound : ∀ n ∈ T, n < blockModulus X K := by
    intro n hn
    have hupper := (hTinterval n hn).2
    have hpos := Nat.mul_pos hK0 hX
    unfold blockModulus
    nlinarith
  have hTnorm := scaled_later_block_norm mFull hFullPrime hFullCop T D U gFull hU hgFull
    hT hmFull hX hK0 hTbound zLarge hzLarge hzLargeM hGLarge
  have hcomparison := roughBlock_fourier_nine mFull mBand hFullPrime hFullCop hBandPrime hBandCop
    E D U gFull gBand B hU hgFull hgBand hE hmFull hX hK hKX hKD hEinterval hDensity hmBand
    zSmall zBand hzSmall hzBand hzSmallN hzBandM hGSmall hGBand
  have h := two_block_density_from_fourier t b₀ b hu hv hKR
    (blockNinthMomentConstant_nonneg gFull gBand B) ht hmean hlower hzero hTnorm hcomparison
  exact h

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/TwoBlock.lean -/
section
/- # A uniform interaction bound for separated rough blocks -/

namespace Erdos12Proof

noncomputable def roughTwoBlockConstant : ℝ :=
  twoBlockTransferConstant (fullSieveDensityConstant / 8) (primeBandDensityConstant / 16)
    (2 * roughCardinalityConstant)

theorem roughTwoBlockConstant_nonneg : 0 ≤ roughTwoBlockConstant :=
  twoBlockTransferConstant_nonneg _ _ _

theorem rough_two_block_bound {A : Set ℕ} (hA : PropertyP A)
    (D : ℝ) (hD : roughSieveThreshold ≤ D) (X K : ℕ) (hDX : D ≤ X) (hK : 16 ≤ K)
    (hKrange : (K : ℝ) ≤ D ^ roughSieveExponent) (E T : Finset ℕ)
    (hEA : ∀ a ∈ E, a ∈ A) (hTA : ∀ n ∈ T, n ∈ A)
    (hEinterval : ∀ a ∈ E, X ≤ a ∧ a < 2 * X)
    (hTinterval : ∀ n ∈ T, K * X ≤ n ∧ n < 2 * (K * X))
    (hErough : ∀ a ∈ E, Rough D a) (hTrough : ∀ n ∈ T, Rough D n) :
    Real.sqrt (roughBlockDensity E D X) * roughBlockDensity T D (K * X) ≤
      roughTwoBlockConstant * (K : ℝ) ^ (-1 / 8 : ℝ) := by
  have hD0 : 0 < D := lt_of_lt_of_le roughSieveThreshold_pos hD
  have hXR : 0 < (X : ℝ) := hD0.trans_le hDX
  have hX : 0 < X := by exact_mod_cast hXR
  have hK0 : 0 < K := by omega
  have hKR : (16 : ℝ) ≤ K := by exact_mod_cast hK
  let : NeZero (blockModulus X K) := ⟨(blockModulus_pos hX hK0).ne'⟩
  have hlogs := roughSieveThreshold_log hD
  have hU : 0 < Real.log D := by linarith [hlogs.1]
  have hDM : D ≤ (blockModulus X K : ℝ) := by
    rw [blockModulus_cast]
    have hcoef : (1 : ℝ) ≤ 32 * (K : ℝ) := by linarith
    have hprod := mul_le_mul_of_nonneg_right hcoef hXR.le
    simp only [one_mul] at hprod
    exact hDX.trans hprod
  have hDsmall : D ≤ 2 * (X : ℝ) := by linarith
  let zSmall := restrictionSieveLevel D (2 * X)
  let zLarge := restrictionSieveLevel D (blockModulus X K)
  obtain ⟨hzSmall, _, hzSmallN, _⟩ := restrictionSieveLevel_properties D (2 * X) hD0 hDsmall hlogs.1
  obtain ⟨hzLarge, hzLargeD, hzLargeM, _⟩ :=
    restrictionSieveLevel_properties D (blockModulus X K) hD0 hDM hlogs.1
  have hfit := roughSieve_prime_band_fits hD hDM hKR hKrange
  have hpow : zLarge ^ sieveMassExponent ≤ zLarge :=
    Real.rpow_le_self_of_one_le hzLarge.le sieveMassExponent_le_one
  have h4K : 4 * (K : ℝ) ≤ D := hfit.trans (hpow.trans hzLargeD)
  have hKD : (4 * K : ℕ) ≤ D := by exact_mod_cast h4K
  have hKX : K ≤ X := by
    have hreal : (K : ℝ) ≤ X := by linarith
    exact_mod_cast hreal
  let mFull : primesThrough D → ℕ := fun p => p.val
  let mBand : primeBand (4 * (K : ℝ)) D → ℕ := fun p => p.val
  have hFullPrime : ∀ i, (mFull i).Prime := fun p => (Finset.mem_filter.mp p.property).2
  have hFullCop : ∀ i j, i ≠ j → (mFull i).Coprime (mFull j) := by
    intro p q hpq
    exact (Nat.coprime_primes (hFullPrime p) (hFullPrime q)).mpr (fun h => hpq (Subtype.ext h))
  have hmFull : ∀ i, (mFull i : ℝ) ≤ D := fun p => ((mem_primesThrough hD0.le).mp p.property).2
  have hBandPrime : ∀ i, (mBand i).Prime := by
    intro p
    exact ((mem_primesThrough hD0.le).mp (Finset.mem_filter.mp p.property).1).1
  have hBandCop : ∀ i j, i ≠ j → (mBand i).Coprime (mBand j) := by
    intro p q hpq
    exact (Nat.coprime_primes (hBandPrime p) (hBandPrime q)).mpr (fun h => hpq (Subtype.ext h))
  have hmBand : ∀ i, 4 * (K : ℝ) < mBand i ∧ (mBand i : ℝ) ≤ D := by
    intro p
    have hp := Finset.mem_filter.mp p.property
    exact ⟨hp.2, ((mem_primesThrough hD0.le).mp hp.1).2⟩
  have hgFull : 0 < fullSieveDensityConstant / 8 := div_pos fullSieveDensityConstant_pos (by norm_num)
  have hgBand : 0 < primeBandDensityConstant / 16 := div_pos primeBandDensityConstant_pos (by norm_num)
  have hGSmall : (fullSieveDensityConstant / 8) * Real.log D ≤ sieveMass mFull zSmall := by
    change _ ≤ sieveMass (fun p : primesThrough D => (p : ℕ)) _
    rw [finitePrimeSieveMass_eq]
    exact fullSieve_density_rough D (2 * X) hD hDsmall
  have hGLarge : (fullSieveDensityConstant / 8) * Real.log D ≤ sieveMass mFull zLarge := by
    change _ ≤ sieveMass (fun p : primesThrough D => (p : ℕ)) _
    rw [finitePrimeSieveMass_eq]
    exact fullSieve_density_rough D (blockModulus X K) hD hDM
  have hGBand : (primeBandDensityConstant / 16) * Real.log D / Real.log (2 * (K : ℝ)) ≤
      sieveMass mBand zLarge := by
    change _ ≤ sieveMass (fun p : primeBand (4 * (K : ℝ)) D => (p : ℕ)) _
    rw [finitePrimeSieveMass_eq]
    exact primeBand_density_rough D (blockModulus X K) K hD hDM hKR hKrange
  have hDensity : Real.log D * E.card / X ≤ 2 * roughCardinalityConstant := by
    exact roughBlockDensity_bound E D X hD hDX hErough
      (fun a ha => by exact_mod_cast (hEinterval a ha).2.le)
  have h := two_block_estimate_of_sieve_masses mFull mBand hFullPrime hFullCop hBandPrime hBandCop
    hA E T hEA hTA D (Real.log D) (fullSieveDensityConstant / 8) (primeBandDensityConstant / 16)
    (2 * roughCardinalityConstant) hU hgFull hgBand hErough hTrough hmFull hX hK hKX hKD
    hEinterval hTinterval hDensity hmBand zSmall zLarge zLarge hzSmall hzLarge hzLarge hzSmallN
    hzLargeM hzLargeM hGSmall hGLarge hGBand
  simpa only [roughBlockDensity, Nat.cast_mul, roughTwoBlockConstant] using h

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/DyadicBlockInteraction.lean -/
section
/- # Integer-power forms of the interaction bound for dyadic blocks -/

namespace Erdos12Proof

def dyadicBin (Q : Finset ℕ) (j : ℕ) : Finset ℕ :=
  Q.filter (fun p => 2 ^ j ≤ p ∧ p < 2 ^ (j + 1))

theorem dyadicBin_subset (Q : Finset ℕ) (j : ℕ) : dyadicBin Q j ⊆ Q :=
  Finset.filter_subset _ _

theorem dyadicBin_interval (Q : Finset ℕ) (j : ℕ) {p : ℕ} (hp : p ∈ dyadicBin Q j) :
    2 ^ j ≤ p ∧ p < 2 * 2 ^ j := by
  have h := (Finset.mem_filter.mp hp).2
  simpa only [pow_succ, Nat.mul_comm] using h

theorem prime_rough_of_lt {p : ℕ} (hp : p.Prime) {D : ℝ} (hD : D < p) : Rough D p := by
  intro r hr hrp
  rcases (Nat.dvd_prime hp).mp hrp with h | h
  · exact (hr.ne_one h).elim
  · simpa only [h] using hD

theorem block_interaction_eighth_power {u v K C : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hK : 0 < K)
    (h : Real.sqrt u * v ≤ C * K ^ (-1 / 8 : ℝ)) :
    u ^ 4 * v ^ 8 * K ≤ C ^ 8 := by
  have hsqrt : Real.sqrt u ^ 8 = u ^ 4 := by
    calc
      _ = (Real.sqrt u ^ 2) ^ 4 := by ring
      _ = _ := by rw [Real.sq_sqrt hu]
  have hrpow : (K ^ (-1 / 8 : ℝ)) ^ 8 = K⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hK.le]
    norm_num
    exact Real.rpow_neg_one K
  have hp := pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg u) hv) h 8
  rw [mul_pow, mul_pow, hsqrt, hrpow] at hp
  have hmul := mul_le_mul_of_nonneg_right hp hK.le
  simpa only [mul_assoc, inv_mul_cancel₀ hK.ne', mul_one] using hmul

theorem exists_blockPackingExponent : ∃ n : ℕ, roughTwoBlockConstant ^ 8 ≤ (2 : ℝ) ^ n := by
  obtain ⟨n, _, hn⟩ := exists_nat_pow_near (le_max_left 1 (roughTwoBlockConstant ^ 8))
    (by norm_num : (1 : ℝ) < 2)
  exact ⟨n + 1, (le_max_right 1 (roughTwoBlockConstant ^ 8)).trans hn.le⟩

noncomputable def blockPackingExponent : ℕ := Classical.choose exists_blockPackingExponent

theorem blockPackingExponent_bound : roughTwoBlockConstant ^ 8 ≤ (2 : ℝ) ^ blockPackingExponent :=
  Classical.choose_spec exists_blockPackingExponent

theorem dyadic_block_interaction (Q : Finset ℕ) (hQ : PropertyP (Q : Set ℕ))
    (D : ℝ) (hD : roughSieveThreshold ≤ D) (i j : ℕ) (hij : i + 4 ≤ j)
    (hDi : D ≤ (2 : ℝ) ^ i) (hscale : ((2 : ℝ) ^ (j - i)) ≤ D ^ roughSieveExponent)
    (hiRough : ∀ p ∈ dyadicBin Q i, Rough D p)
    (hjRough : ∀ p ∈ dyadicBin Q j, Rough D p) :
    (roughBlockDensity (dyadicBin Q i) D (2 ^ i)) ^ 4 *
      (roughBlockDensity (dyadicBin Q j) D (2 ^ j)) ^ 8 * (2 : ℝ) ^ (j - i) ≤
        (2 : ℝ) ^ blockPackingExponent := by
  have hij' : i ≤ j := by omega
  have hK : 16 ≤ (2 : ℕ) ^ (j - i) := by
    have h := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (show 4 ≤ j - i by omega)
    norm_num at h
    exact h
  have hproduct : (2 : ℕ) ^ (j - i) * 2 ^ i = 2 ^ j := by
    rw [← pow_add, Nat.sub_add_cancel hij']
  have h := rough_two_block_bound hQ D hD (2 ^ i) (2 ^ (j - i))
    (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hDi) hK
    (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hscale)
    (dyadicBin Q i) (dyadicBin Q j) (fun p hp => dyadicBin_subset Q i hp)
    (fun p hp => dyadicBin_subset Q j hp) (fun _ hp => dyadicBin_interval Q i hp)
    (by simpa only [hproduct] using fun p (hp : p ∈ dyadicBin Q j) => dyadicBin_interval Q j hp)
    hiRough hjRough
  rw [hproduct] at h
  have hlog : 0 ≤ Real.log D := by linarith [(roughSieveThreshold_log hD).1]
  have hi0 : 0 ≤ roughBlockDensity (dyadicBin Q i) D (2 ^ i) := by
    unfold roughBlockDensity
    positivity
  have hj0 : 0 ≤ roughBlockDensity (dyadicBin Q j) D (2 ^ j) := by
    unfold roughBlockDensity
    positivity
  have hp := block_interaction_eighth_power hi0 hj0
    (by positivity : (0 : ℝ) < ((2 : ℕ) ^ (j - i) : ℕ)) h
  have hp' : (roughBlockDensity (dyadicBin Q i) D (2 ^ i)) ^ 4 *
      (roughBlockDensity (dyadicBin Q j) D (2 ^ j)) ^ 8 * (2 : ℝ) ^ (j - i) ≤
        roughTwoBlockConstant ^ 8 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hp
  exact hp'.trans blockPackingExponent_bound

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/DyadicDecomposition.lean -/
section
/- # Exact finite decomposition into dyadic bins -/

namespace Erdos12Proof

theorem dyadicBin_eq_filter_log (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 0 < p) (j : ℕ) :
    dyadicBin Q j = Q.filter (fun p => Nat.log2 p = j) := by
  ext p
  simp only [dyadicBin, Finset.mem_filter]
  constructor
  · rintro ⟨hp, hlo, hhi⟩
    refine ⟨hp, ?_⟩
    rw [Nat.log2_eq_log_two]
    exact Nat.log_eq_of_pow_le_of_lt_pow hlo hhi
  · rintro ⟨hp, hlog⟩
    have hp0 : p ≠ 0 := (hQ p hp).ne'
    rw [Nat.log2_eq_log_two] at hlog
    refine ⟨hp, ?_, ?_⟩
    · simpa only [hlog] using Nat.pow_log_le_self 2 hp0
    · simpa only [hlog] using Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) p

theorem harmonic_dyadic_decomposition (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 0 < p) :
    harmonic Q = ∑ j ∈ Q.image Nat.log2, harmonic (dyadicBin Q j) := by
  simp_rw [dyadicBin_eq_filter_log Q hQ]
  unfold harmonic
  exact (Finset.sum_fiberwise_of_maps_to (fun p hp => Finset.mem_image_of_mem Nat.log2 hp)
    (fun p => (1 / p : ℝ))).symm

theorem harmonic_dyadic_subfamily (Q S : Finset ℕ) (hQ : ∀ p ∈ Q, 0 < p) :
    (∑ j ∈ S, harmonic (dyadicBin Q j)) = harmonic (Q.filter (fun p => Nat.log2 p ∈ S)) := by
  simp_rw [dyadicBin_eq_filter_log Q hQ]
  exact Finset.sum_fiberwise_eq_sum_filter Q S Nat.log2 (fun p => (1 / p : ℝ))

theorem dyadic_index_lower {p J : ℕ} (h : 2 ^ J ≤ p) : J ≤ Nat.log2 p := by
  rw [Nat.log2_eq_log_two]
  exact Nat.le_log_of_pow_le (by decide) h

theorem dyadic_index_upper {p J : ℕ} (hp : 0 < p) (h : p < 2 ^ J) : Nat.log2 p < J := by
  rw [Nat.log2_eq_log_two]
  exact Nat.log_lt_of_lt_pow hp.ne' h

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/PrimeTailSplit.lean -/
section
/- # A finite four-range decomposition for the prime-tail argument -/

namespace Erdos12Proof

theorem prime_tail_four_ranges (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 0 < p)
    (J B M : ℕ) (hJB : J ≤ B) :
    harmonic Q ≤
      (∑ i ∈ (Q.image Nat.log2).filter (fun i => i < J), harmonic (dyadicBin Q i)) +
      (∑ i ∈ (Q.image Nat.log2).filter (fun i => J ≤ i ∧ i < B), harmonic (dyadicBin Q i)) +
      (∑ i ∈ (Q.image Nat.log2).filter (fun i => B ≤ i ∧ 2 ^ i < M ^ 2), harmonic (dyadicBin Q i)) +
      harmonic (Q.filter (fun p => M ^ 2 ≤ p)) := by
  classical
  let I := Q.image Nat.log2
  let f := fun i => harmonic (dyadicBin Q i)
  let I₁ := I.filter (fun i => ¬i < J)
  let I₂ := I₁.filter (fun i => ¬i < B)
  let F := I₂.filter (fun i => ¬2 ^ i < M ^ 2)
  have h1 := Finset.sum_filter_add_sum_filter_not I (fun i => i < J) f
  have h2 := Finset.sum_filter_add_sum_filter_not I₁ (fun i => i < B) f
  have h3 := Finset.sum_filter_add_sum_filter_not I₂ (fun i => 2 ^ i < M ^ 2) f
  have hnear : I₁.filter (fun i => i < B) = I.filter (fun i => J ≤ i ∧ i < B) := by
    dsimp only [I₁]
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro i _
    simp only [not_lt]
  have hmiddle : I₂.filter (fun i => 2 ^ i < M ^ 2) =
      I.filter (fun i => B ≤ i ∧ 2 ^ i < M ^ 2) := by
    dsimp only [I₂, I₁]
    rw [Finset.filter_filter, Finset.filter_filter]
    apply Finset.filter_congr
    intro i _
    simp only [not_lt]
    omega
  have hfar : (∑ i ∈ F, f i) ≤ harmonic (Q.filter (fun p => M ^ 2 ≤ p)) := by
    rw [harmonic_dyadic_subfamily Q F hQ]
    apply harmonic_mono
    intro p hp
    obtain ⟨hpQ, hpF⟩ := Finset.mem_filter.mp hp
    have hpF' : ¬2 ^ Nat.log2 p < M ^ 2 := (Finset.mem_filter.mp hpF).2
    have hpPow : 2 ^ Nat.log2 p ≤ p := by
      rw [Nat.log2_eq_log_two]
      exact Nat.pow_log_le_self 2 (hQ p hpQ).ne'
    exact Finset.mem_filter.mpr ⟨hpQ, (Nat.le_of_not_gt hpF').trans hpPow⟩
  rw [hnear] at h2
  rw [hmiddle] at h3
  have hsum := harmonic_dyadic_decomposition Q hQ
  change harmonic Q = ∑ i ∈ I, f i at hsum
  change _ + ∑ i ∈ F, f i = _ at h3
  change harmonic Q ≤ _
  linarith

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/DyadicWeightSummation.lean -/
section
/- # Summing finite weights from dyadic level counts -/

namespace Erdos12Proof

theorem exists_dyadic_weight_level {B w : ℝ} (hw : 0 < w) (hwB : w ≤ B) :
    ∃ j : ℕ, B * (1 / 2 : ℝ) ^ j ≤ w ∧ w ≤ 2 * B * (1 / 2 : ℝ) ^ j := by
  have hB : 0 < B := hw.trans_le hwB
  have hratio : (1 : ℝ) ≤ B / w := (le_div_iff₀ hw).mpr (by simpa using hwB)
  obtain ⟨j, hjlo, hjhi⟩ := exists_nat_pow_near hratio (by norm_num : (1 : ℝ) < 2)
  refine ⟨j + 1, ?_, ?_⟩
  · have h := (div_lt_iff₀ hw).mp hjhi
    have hpow : (0 : ℝ) < 2 ^ (j + 1) := by positivity
    rw [one_div_pow, mul_one_div]
    exact (div_le_iff₀ hpow).mpr (by nlinarith)
  · have h := (le_div_iff₀ hw).mp hjlo
    have hpow : (0 : ℝ) < 2 ^ j := by positivity
    have hle : w ≤ B / 2 ^ j := (le_div_iff₀ hpow).mpr (by nlinarith)
    calc
      w ≤ B / 2 ^ j := hle
      _ = _ := by rw [pow_succ, one_div_pow]; field_simp

theorem weighted_geometric_stage_sum (k : ℕ) :
    HasSum (fun j : ℕ => (1 / 2 : ℝ) ^ j * (1 + (k : ℝ) + j)) (4 + 2 * k) := by
  have hs := hasSum_stage_budget.add
    ((hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_right (k : ℝ))
  convert hs using 1
  · funext j
    ring
  · norm_num

theorem finite_weight_sum_of_level_counts {κ : Type*} (S : Finset κ) (w : κ → ℝ)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 < B) (k : ℕ)
    (hw : ∀ i ∈ S, 0 ≤ w i ∧ w i ≤ B * (1 / 2 : ℝ) ^ k)
    (hcounts : ∀ j : ℕ,
      ((S.filter (fun i => B * (1 / 2 : ℝ) ^ (k + j) ≤ w i)).card : ℝ) ≤
        A * (1 + (k : ℝ) + j)) :
    (∑ i ∈ S, w i) ≤ 8 * A * B * (1 / 2 : ℝ) ^ k * (1 + k) := by
  classical
  let P := S.filter (fun i => 0 < w i)
  let D := B * (1 / 2 : ℝ) ^ k
  have hD : 0 < D := mul_pos hB (by positivity)
  have hex : ∀ i : κ, ∃ j : ℕ, i ∈ P → D * (1 / 2 : ℝ) ^ j ≤ w i ∧
      w i ≤ 2 * D * (1 / 2 : ℝ) ^ j := by
    intro i
    by_cases hi : i ∈ P
    · obtain ⟨j, hj⟩ := exists_dyadic_weight_level (Finset.mem_filter.mp hi).2
        (hw i (Finset.mem_filter.mp hi).1).2
      exact ⟨j, fun _ => hj⟩
    · exact ⟨0, fun h => (hi h).elim⟩
  choose level hlevel using hex
  let L := P.image level
  have hzero : (∑ i ∈ S, w i) = ∑ i ∈ P, w i := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hni
    have hn : ¬0 < w i := fun h => hni (Finset.mem_filter.mpr ⟨hi, h⟩)
    exact le_antisymm (le_of_not_gt hn) (hw i hi).1
  have hfibre (j : ℕ) : ((P.filter (fun i => level i = j)).card : ℝ) ≤
      A * (1 + (k : ℝ) + j) := by
    apply le_trans _ (hcounts j)
    exact_mod_cast Finset.card_le_card (show P.filter (fun i => level i = j) ⊆
      S.filter (fun i => B * (1 / 2 : ℝ) ^ (k + j) ≤ w i) from by
        intro i hi
        obtain ⟨hiP, hij⟩ := Finset.mem_filter.mp hi
        refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hiP).1, ?_⟩
        have h := (hlevel i hiP).1
        simpa only [D, hij, pow_add, mul_assoc] using h)
  have hinner (j : ℕ) : (∑ i ∈ P with level i = j, w i) ≤
      2 * D * (1 / 2 : ℝ) ^ j * (A * (1 + (k : ℝ) + j)) := by
    calc
      _ ≤ ∑ _i ∈ P.filter (fun i => level i = j), 2 * D * (1 / 2 : ℝ) ^ j := by
        apply Finset.sum_le_sum
        intro i hi
        obtain ⟨hiP, hij⟩ := Finset.mem_filter.mp hi
        simpa only [hij] using (hlevel i hiP).2
      _ = 2 * D * (1 / 2 : ℝ) ^ j * (P.filter (fun i => level i = j)).card := by
        simp only [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hfibre j) (by positivity)
  have hgeom : (∑ j ∈ L, (1 / 2 : ℝ) ^ j * (1 + (k : ℝ) + j)) ≤ 4 * (1 + k) := by
    have hs := weighted_geometric_stage_sum k
    have h := hs.summable.sum_le_tsum L (fun j _ => by positivity)
    rw [hs.tsum_eq] at h
    linarith
  calc
    _ = ∑ j ∈ L, ∑ i ∈ P with level i = j, w i := by
      rw [hzero]
      exact (Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem level hi) w).symm
    _ ≤ ∑ j ∈ L, 2 * D * (1 / 2 : ℝ) ^ j * (A * (1 + (k : ℝ) + j)) :=
      Finset.sum_le_sum (fun j _ => hinner j)
    _ = 2 * A * D * ∑ j ∈ L, (1 / 2 : ℝ) ^ j * (1 + (k : ℝ) + j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ 2 * A * D * (4 * (1 + k)) := mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = _ := by dsimp only [D]; ring

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/DyadicDensityPacking.lean -/
section
/- # A density-level packing bound from dyadic block interaction -/

namespace Erdos12Proof

theorem dyadic_density_level_card (S : Finset ℕ) (w : ℕ → ℝ)
    (A k l : ℕ) (B : ℝ) (hB : 1 ≤ B)
    (hpair : ∀ i ∈ S, ∀ j ∈ S, i + 4 ≤ j →
      w i ^ 4 * w j ^ 8 * (2 : ℝ) ^ (j - i) ≤ (2 : ℝ) ^ A) :
    ((S.filter (fun i => B * (1 / 2 : ℝ) ^ (k + l) ≤ w i)).card : ℝ) ≤
      ((A : ℝ) + 16) * (1 + (k : ℝ) + l) := by
  classical
  let T := S.filter (fun i => B * (1 / 2 : ℝ) ^ (k + l) ≤ w i)
  let t : ℝ := (1 / 2 : ℝ) ^ (k + l)
  have ht : 0 ≤ t := by positivity
  have hT : ∀ i ∈ T, i ∈ S ∧ t ≤ w i := by
    intro i hi
    obtain ⟨hiS, hiw⟩ := Finset.mem_filter.mp hi
    refine ⟨hiS, ?_⟩
    have hscale : t ≤ B * t := le_mul_of_one_le_left ht hB
    exact hscale.trans hiw
  by_cases hne : T.Nonempty
  · let i := T.min' hne
    let j := T.max' hne
    have hi : i ∈ T := Finset.min'_mem T hne
    have hj : j ∈ T := Finset.max'_mem T hne
    have hij : i ≤ j := Finset.min'_le_max' T hne
    have hwidth : j - i ≤ A + (k + l) * 12 + 3 := by
      by_cases hgap : i + 4 ≤ j
      · have hp := hpair i (hT i hi).1 j (hT j hj).1 hgap
        have hlower : t ^ 12 ≤ w i ^ 4 * w j ^ 8 := by
          calc
            _ = t ^ 4 * t ^ 8 := by ring
            _ ≤ _ := mul_le_mul (pow_le_pow_left₀ ht (hT i hi).2 4)
              (pow_le_pow_left₀ ht (hT j hj).2 8) (by positivity) (by positivity)
        have hp' : t ^ 12 * (2 : ℝ) ^ (j - i) ≤ (2 : ℝ) ^ A :=
          (mul_le_mul_of_nonneg_right hlower (by positivity)).trans hp
        have hinverse : t ^ 12 * (2 : ℝ) ^ ((k + l) * 12) = 1 := by
          dsimp only [t]
          rw [← pow_mul, one_div_pow]
          field_simp
        have hexp : (2 : ℝ) ^ (j - i) ≤ (2 : ℝ) ^ (A + (k + l) * 12) := by
          calc
            _ = (t ^ 12 * (2 : ℝ) ^ (j - i)) * (2 : ℝ) ^ ((k + l) * 12) := by
              rw [mul_assoc, mul_comm ((2 : ℝ) ^ (j - i)), ← mul_assoc, hinverse, one_mul]
            _ ≤ (2 : ℝ) ^ A * (2 : ℝ) ^ ((k + l) * 12) :=
              mul_le_mul_of_nonneg_right hp' (by positivity)
            _ = _ := (pow_add _ _ _).symm
        have hn := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hexp
        omega
      · omega
    have hcard : T.card ≤ j + 1 - i := by
      calc
        _ ≤ (Finset.Icc i j).card := Finset.card_le_card (show T ⊆ Finset.Icc i j from by
          intro n hn
          exact Finset.mem_Icc.mpr ⟨Finset.min'_le T n hn, Finset.le_max' T n hn⟩)
        _ = _ := Nat.card_Icc _ _
    have hnat : T.card ≤ A + (k + l) * 12 + 4 := by omega
    have hreal : (T.card : ℝ) ≤ (A : ℝ) + (k + l) * 12 + 4 := by exact_mod_cast hnat
    change (T.card : ℝ) ≤ _
    have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg A
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    nlinarith
  · have hzero : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    change (T.card : ℝ) ≤ _
    rw [hzero, Finset.card_empty, Nat.cast_zero]
    positivity

theorem dyadic_density_sum (S : Finset ℕ) (w : ℕ → ℝ)
    (A k : ℕ) (B : ℝ) (hB : 1 ≤ B)
    (hw : ∀ i ∈ S, 0 ≤ w i ∧ w i ≤ B * (1 / 2 : ℝ) ^ k)
    (hpair : ∀ i ∈ S, ∀ j ∈ S, i + 4 ≤ j →
      w i ^ 4 * w j ^ 8 * (2 : ℝ) ^ (j - i) ≤ (2 : ℝ) ^ A) :
    (∑ i ∈ S, w i) ≤ 8 * ((A : ℝ) + 16) * B * (1 / 2 : ℝ) ^ k * (1 + k) := by
  apply finite_weight_sum_of_level_counts S w ((A : ℝ) + 16) B (by positivity)
    (lt_of_lt_of_le zero_lt_one hB) k hw
  exact fun l => dyadic_density_level_card S w A k l B hB hpair

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/FinitePrimeRemoval.lean -/
section
/- # The exact Euler-product cost of deleting a finite set of primes -/

namespace Erdos12Proof

theorem finitePrimeSieveMass_remove (P R : Finset ℕ) (hRP : R ⊆ P)
    (hP : ∀ p ∈ P, p.Prime) (z : ℝ) :
    finitePrimeSieveMass P z ≤ finitePrimeSieveMass (P \ R) z *
      ∏ p ∈ R, (1 + sieveLocalWeight p) := by
  let w : ℕ → ℝ := fun p => max 0 (sieveLocalWeight p)
  let F : Finset (Finset ℕ) := P.powerset.filter (fun s => ((∏ p ∈ s, p : ℕ) : ℝ) < z)
  have hw : ∀ p, 0 ≤ w p := fun p => le_max_left _ _
  have hagree (p : ℕ) (hp : p ∈ P) : w p = sieveLocalWeight p :=
    max_eq_right (sieveLocalWeight_pos (hP p hp).one_lt).le
  have hweight (s : Finset ℕ) (hs : s ⊆ P) : tensorWeight w s = tensorWeight sieveLocalWeight s := by
    apply Finset.prod_congr rfl
    intro p hp
    exact hagree p (hs hp)
  have hmass (Q : Finset ℕ) (hQ : Q ⊆ P) :
      selbergMass w (Q.powerset.filter (fun s => ((∏ p ∈ s, p : ℕ) : ℝ) < z)) =
        finitePrimeSieveMass Q z := by
    unfold selbergMass finitePrimeSieveMass
    apply Finset.sum_congr rfl
    intro s hs
    exact hweight s ((Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1).trans hQ)
  have hdown : ∀ s ∈ F, ∀ t : Finset ℕ, t ⊆ s → t ∈ F := by
    intro s hs t hts
    obtain ⟨hsP, hsbound⟩ := Finset.mem_filter.mp hs
    have hsP' := Finset.mem_powerset.mp hsP
    have hprod : (∏ p ∈ t, p : ℕ) ≤ ∏ p ∈ s, p :=
      Finset.prod_le_prod_of_subset_of_one_le hts (fun p hp _ => (hP p (hsP' hp)).one_lt.le)
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hts.trans hsP'),
      lt_of_le_of_lt (by exact_mod_cast hprod) hsbound⟩
  have hfilter : F.filter (fun s => Disjoint s R) =
      (P \ R).powerset.filter (fun s => ((∏ p ∈ s, p : ℕ) : ℝ) < z) := by
    ext s
    simp only [F, Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨⟨hsP, hprod⟩, hdis⟩
      exact ⟨fun p hp => Finset.mem_sdiff.mpr ⟨hsP hp,
        fun hpR => Finset.disjoint_left.mp hdis hp hpR⟩, hprod⟩
    · rintro ⟨hsPR, hprod⟩
      refine ⟨⟨fun p hp => (Finset.mem_sdiff.mp (hsPR hp)).1, hprod⟩, ?_⟩
      exact Finset.disjoint_left.mpr (fun p hp hpR => (Finset.mem_sdiff.mp (hsPR hp)).2 hpR)
  have h := selbergMass_remove_bound w hw F R hdown
  rw [hfilter] at h
  dsimp only [F] at h
  rw [hmass P Finset.Subset.rfl, hmass (P \ R) Finset.sdiff_subset] at h
  have hproduct : (∏ p ∈ R, (1 + w p)) = ∏ p ∈ R, (1 + sieveLocalWeight p) := by
    apply Finset.prod_congr rfl
    intro p hp
    rw [hagree p (hRP hp)]
  rwa [hproduct] at h

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/PrimeSieveEulerCost.lean -/
section
/- # Euler factors for sieve exclusions -/

namespace Erdos12Proof

noncomputable def primeSieveEulerCost (P : Finset ℕ) : ℝ :=
  ∏ p ∈ P, (1 + sieveLocalWeight p)

theorem primeSieveEulerCost_pos (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    0 < primeSieveEulerCost P := by
  apply Finset.prod_pos
  intro p hp
  exact add_pos_of_pos_of_nonneg zero_lt_one (sieveLocalWeight_pos (hP p hp).one_lt).le

theorem primeSieveEulerCost_mono {P Q : Finset ℕ} (hPQ : P ⊆ Q)
    (hQ : ∀ p ∈ Q, p.Prime) : primeSieveEulerCost P ≤ primeSieveEulerCost Q := by
  apply Finset.prod_le_prod_of_subset_of_one_le₀ hPQ
  · intro p hp
    exact add_nonneg zero_le_one (sieveLocalWeight_pos (hQ p (hPQ hp)).one_lt).le
  · intro p hp _
    exact le_add_of_nonneg_right (sieveLocalWeight_pos (hQ p hp).one_lt).le

theorem primeSieveEulerCost_ratio (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    primeSieveEulerCost P = ((∏ p ∈ P, p : ℕ) : ℝ) / (∏ p ∈ P, ((p : ℝ) - 1)) := by
  unfold primeSieveEulerCost
  rw [Nat.cast_prod, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpR : 1 < (p : ℝ) := by exact_mod_cast (hP p hp).one_lt
  have hden : (p : ℝ) - 1 ≠ 0 := by linarith
  unfold sieveLocalWeight
  field_simp
  ring

theorem finitePrimeSieveMass_nonneg (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (z : ℝ) :
    0 ≤ finitePrimeSieveMass P z := by
  unfold finitePrimeSieveMass selbergMass
  apply Finset.sum_nonneg
  intro s hs
  apply Finset.prod_nonneg
  intro p hp
  have hpP := (Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1) hp
  exact (sieveLocalWeight_pos (hP p hpP).one_lt).le

theorem finitePrimeSieveMass_remove_external (P R : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hR : ∀ p ∈ R, p.Prime) (z : ℝ) :
    finitePrimeSieveMass P z ≤ finitePrimeSieveMass (P \ R) z * primeSieveEulerCost R := by
  have h := finitePrimeSieveMass_remove P (P ∩ R) Finset.inter_subset_left hP z
  have hset : P \ (P ∩ R) = P \ R := by
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  rw [hset] at h
  have hcost := primeSieveEulerCost_mono (P := P ∩ R) (Q := R) Finset.inter_subset_right hR
  have hnonneg := finitePrimeSieveMass_nonneg (P \ R) (fun p hp => hP p (Finset.mem_sdiff.mp hp).1) z
  exact h.trans (mul_le_mul_of_nonneg_left hcost hnonneg)

theorem finitePrimeSieveMass_remove_two (P R S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hR : ∀ p ∈ R, p.Prime) (hS : ∀ p ∈ S, p.Prime) (z : ℝ) :
    finitePrimeSieveMass P z ≤ finitePrimeSieveMass ((P \ R) \ S) z *
      (primeSieveEulerCost R * primeSieveEulerCost S) := by
  have hfirst := finitePrimeSieveMass_remove_external P R hP hR z
  have hsecond := finitePrimeSieveMass_remove_external (P \ R) S
    (fun p hp => hP p (Finset.mem_sdiff.mp hp).1) hS z
  calc
    _ ≤ finitePrimeSieveMass (P \ R) z * primeSieveEulerCost R := hfirst
    _ ≤ (finitePrimeSieveMass ((P \ R) \ S) z * primeSieveEulerCost S) * primeSieveEulerCost R :=
      mul_le_mul_of_nonneg_right hsecond (primeSieveEulerCost_pos R hR).le
    _ = _ := by ring

theorem finitePrimeSieveMass_exclusion_lower (P R S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hR : ∀ p ∈ R, p.Prime) (hS : ∀ p ∈ S, p.Prime)
    (z c : ℝ) (hc : c ≤ finitePrimeSieveMass P z) :
    c / (primeSieveEulerCost R * primeSieveEulerCost S) ≤ finitePrimeSieveMass ((P \ R) \ S) z := by
  apply (div_le_iff₀ (mul_pos (primeSieveEulerCost_pos R hR) (primeSieveEulerCost_pos S hS))).mpr
  exact hc.trans (finitePrimeSieveMass_remove_two P R S hP hR hS z)

noncomputable def smallPrimeSieveCost : ℝ := primeSieveEulerCost (primesThrough 24)

theorem smallPrimeSieveCost_pos : 0 < smallPrimeSieveCost := by
  apply primeSieveEulerCost_pos
  intro p hp
  exact (Finset.mem_filter.mp hp).2

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/ProgressionSieveMass.lean -/
section
/- # Sieve mass after excluding small primes and progression divisors -/

namespace Erdos12Proof

noncomputable def progressionSievePrimes (D : ℝ) (R : Finset ℕ) : Finset ℕ :=
  (primesThrough D \ primesThrough 24) \ R

theorem progressionSievePrimes_properties {D : ℝ} (hD : 0 ≤ D) (R : Finset ℕ)
    {p : ℕ} (hp : p ∈ progressionSievePrimes D R) :
    p.Prime ∧ 25 ≤ p ∧ (p : ℝ) ≤ D ∧ p ∉ R := by
  obtain ⟨hpSmall, hpR⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨hpD, hp24⟩ := Finset.mem_sdiff.mp hpSmall
  obtain ⟨hprime, hbound⟩ := (mem_primesThrough hD).mp hpD
  have hlarge : 25 ≤ p := by
    by_contra! hsmall
    apply hp24
    apply (mem_primesThrough (by norm_num : (0 : ℝ) ≤ 24)).mpr
    refine ⟨hprime, ?_⟩
    exact_mod_cast (show p ≤ 24 by omega)
  exact ⟨hprime, hlarge, hbound, hpR⟩

theorem prime_dvd_prime_product_iff (R : Finset ℕ) (hR : ∀ q ∈ R, q.Prime)
    {p : ℕ} (hp : p.Prime) : p ∣ ∏ q ∈ R, q ↔ p ∈ R := by
  constructor
  · intro hdiv
    obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff (S := R) hp.prime (fun q : ℕ => q)).mp hdiv
    have heq := (Nat.prime_dvd_prime_iff_eq hp (hR q hq)).mp hpq
    simpa only [heq] using hq
  · intro hpR
    exact Finset.dvd_prod_of_mem (fun q : ℕ => q) hpR

theorem progressionSievePrimes_not_dvd {D : ℝ} (hD : 0 ≤ D) (R : Finset ℕ)
    (hR : ∀ q ∈ R, q.Prime) {p : ℕ} (hp : p ∈ progressionSievePrimes D R) :
    ¬p ∣ ∏ q ∈ R, q := by
  have hprops := progressionSievePrimes_properties hD R hp
  exact fun hdiv => hprops.2.2.2 ((prime_dvd_prime_product_iff R hR hprops.1).mp hdiv)

theorem progression_sieve_mass_lower (D N : ℝ) (hD : roughSieveThreshold ≤ D)
    (hDN : D ≤ N) (R : Finset ℕ) (hR : ∀ p ∈ R, p.Prime) :
    ((fullSieveDensityConstant / 8) * Real.log D) /
      (smallPrimeSieveCost * primeSieveEulerCost R) ≤
        finitePrimeSieveMass (progressionSievePrimes D R) (restrictionSieveLevel D N) := by
  apply finitePrimeSieveMass_exclusion_lower (primesThrough D) (primesThrough 24) R
    (fun p hp => (Finset.mem_filter.mp hp).2)
    (fun p hp => (Finset.mem_filter.mp hp).2) hR
  exact fullSieve_density_rough D N hD hDN

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/TranslatedSieve.lean -/
section
/- # Sifted dual bounds on intervals with arbitrary starting point -/

open MeasureTheory FourierTransform
open scoped SchwartzMap

namespace Erdos12Proof

theorem exists_translated_interval_majorant (N η a : ℝ) (hN : 0 ≤ N) (hη : 0 < η) :
    ∃ f : 𝓢(ℝ, ℂ), (∀ x, (f x).im = 0) ∧ (∀ x, 0 ≤ (f x).re) ∧
      (∀ x, a ≤ x → x ≤ a + N → 1 ≤ (f x).re) ∧
      (∀ ξ, η < |ξ| → 𝓕 f ξ = 0) ∧
      (∫ x, (f x).re) ≤ intervalMajorantConstant * (N + η⁻¹) := by
  obtain ⟨f, hreal, hpos, hmajorant, hband, hintegral⟩ :=
    (Classical.choose_spec exists_interval_majorant).2 N η hN hη
  let g : 𝓢(ℝ, ℂ) := f.compSubConstCLM ℂ a
  have hg (x : ℝ) : g x = f (x - a) := rfl
  refine ⟨g, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [hg]
    exact hreal (x - a)
  · intro x
    rw [hg]
    exact hpos (x - a)
  · intro x hax hxa
    rw [hg]
    exact hmajorant (x - a) (by linarith) (by linarith)
  · intro ξ hξ
    rw [SchwartzMap.fourier_coe]
    change 𝓕 (fun x : ℝ => f (x - a)) ξ = 0
    rw [fourier_translate]
    have hf : 𝓕 (fun x : ℝ => f x) ξ = 0 := by
      simpa only [SchwartzMap.fourier_coe] using hband ξ hξ
    rw [hf, smul_zero]
  · calc
      (∫ x, (g x).re) = ∫ x, (f (x - a)).re := rfl
      _ = ∫ x, (f x).re := integral_sub_right_eq_self (fun x : ℝ => (f x).re) a
      _ ≤ _ := hintegral

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
variable (m : ι → ℕ) [∀ i, NeZero (m i)]

theorem translated_sifted_dual_bound (S : Finset κ) (c : κ → ℂ) (a : κ → ℝ)
    (T : Finset ℤ) (hm : ∀ i, 25 ≤ m i)
    (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    (q : ℝ) (hq : 0 < q) (hmq : ∀ i, q ^ 2 ≤ (m i : ℝ))
    (N δ z L : ℝ) (hδ : 0 < δ) (hz : 1 < z) (hN : z ^ 4 ≤ N)
    (hinterval : ∀ n ∈ T, L ≤ (n : ℝ) ∧ (n : ℝ) ≤ L + N)
    (hsifted : ∀ n ∈ T, ∀ i, (n : ZMod (m i)) ≠ 0)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      δ ≤ dist (a i : UnitAddCircle) (a j : UnitAddCircle)) :
    (∑ n ∈ T, ‖trigPolynomial S c a n‖ ^ 2) ≤
      (5 * intervalMajorantConstant * (N + δ⁻¹) / sieveMass m z) *
        ((∑ i ∈ S, ‖c i‖ ^ 2) + (∑ i ∈ S, ‖c i‖) ^ 2 / q) := by
  obtain ⟨η, hη, hηhalf, hspacing, hηδ, hmass⟩ := exists_dual_bandwidth N δ z hδ hz hN
  have hN0 : 0 ≤ N := (pow_nonneg (by linarith : (0 : ℝ) ≤ z) 4).trans hN
  obtain ⟨f, hreal, hpos, hmajorant, hband, hintegral⟩ :=
    exists_translated_interval_majorant N η L hN0 hη
  have hbase := sifted_dual_bound m S c a T hm hcop q hq hmq z η hz hηhalf hspacing
    f hband hreal hpos (fun n hn => hmajorant n (hinterval n hn).1 (hinterval n hn).2)
      hsifted (fun i hi j hj hij => hηδ.trans_le (hsep i hi j hj hij))
  have hm1 : ∀ i, 1 < m i := by intro i; have := hm i; omega
  have hG := sieveMass_pos hm1 hz
  have hI : (∫ x, (f x).re) ≤ 5 * intervalMajorantConstant * (N + δ⁻¹) := by
    calc
      _ ≤ intervalMajorantConstant * (N + η⁻¹) := hintegral
      _ ≤ intervalMajorantConstant * (5 * (N + δ⁻¹)) :=
        mul_le_mul_of_nonneg_left hmass intervalMajorantConstant_pos.le
      _ = _ := by ring
  apply hbase.trans
  apply mul_le_mul_of_nonneg_right ((div_le_div_iff_of_pos_right hG).mpr hI)
  exact add_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg ‖c i‖)
    (div_nonneg (sq_nonneg _) hq.le)

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/TranslatedSiftedCounting.lean -/
section
/- # Counting sifted integers in an interval with arbitrary origin -/

namespace Erdos12Proof

noncomputable def translatedSieveCardinalityConstant : ℝ := 10 * intervalMajorantConstant

theorem translatedSieveCardinalityConstant_pos : 0 < translatedSieveCardinalityConstant :=
  mul_pos (by norm_num) intervalMajorantConstant_pos

theorem translated_sifted_cardinality {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hm : ∀ i, 25 ≤ m i) (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    (T : Finset ℤ) (N z L : ℝ) (hz : 1 < z) (hN : z ^ 4 ≤ N)
    (hinterval : ∀ n ∈ T, L ≤ (n : ℝ) ∧ (n : ℝ) ≤ L + N)
    (hsifted : ∀ n ∈ T, ∀ i, (n : ZMod (m i)) ≠ 0) :
    (T.card : ℝ) ≤ translatedSieveCardinalityConstant * (N + 1) / sieveMass m z := by
  classical
  let : ∀ i, NeZero (m i) := fun i => ⟨by have h := hm i; omega⟩
  have hmq : ∀ i, (1 : ℝ) ^ 2 ≤ m i := by
    intro i
    norm_num
    exact_mod_cast (show 1 ≤ m i by have h := hm i; omega)
  have h := translated_sifted_dual_bound m (Finset.univ : Finset Unit)
    (fun _ => (1 : ℂ)) (fun _ => (0 : ℝ)) T hm hcop 1 (by norm_num) hmq
    N 1 z L (by norm_num) hz hN hinterval hsifted
    (fun i _ j _ hij => False.elim (hij (Subsingleton.elim i j)))
  simp [trigPolynomial, unitExp] at h
  norm_num at h
  calc
    (T.card : ℝ) ≤ (5 * intervalMajorantConstant * (N + 1) / sieveMass m z) * 2 := h
    _ = _ := by unfold translatedSieveCardinalityConstant; ring

theorem translated_sifted_cardinality_linear {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hm : ∀ i, 25 ≤ m i) (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    (T : Finset ℤ) (N z L : ℝ) (hz : 1 < z) (hN : z ^ 4 ≤ N)
    (hinterval : ∀ n ∈ T, L ≤ (n : ℝ) ∧ (n : ℝ) ≤ L + N)
    (hsifted : ∀ n ∈ T, ∀ i, (n : ZMod (m i)) ≠ 0) :
    (T.card : ℝ) ≤ 2 * translatedSieveCardinalityConstant * N / sieveMass m z := by
  have hG : 0 < sieveMass m z := sieveMass_pos (fun i => by have h := hm i; omega) hz
  have hN1 : 1 ≤ N := (one_lt_pow₀ hz (by norm_num : (4 : ℕ) ≠ 0)).le.trans hN
  have h := translated_sifted_cardinality m hm hcop T N z L hz hN hinterval hsifted
  apply h.trans
  apply (div_le_div_iff_of_pos_right hG).mpr
  nlinarith [translatedSieveCardinalityConstant_pos]

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/ResidueAvoidingCount.lean -/
section
/- # Interval counts when one residue class is forbidden at each prime -/

namespace Erdos12Proof

theorem exists_integer_residue_vector {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    (r : ∀ i, ZMod (m i)) : ∃ R : ℤ, ∀ i, (R : ZMod (m i)) = r i := by
  classical
  let : ∀ i, NeZero (m i) := fun i => ⟨(hm i).ne'⟩
  have hpair : Set.Pairwise (↑(Finset.univ : Finset ι)) (fun i j => (m i).Coprime (m j)) := by
    intro i _ j _ hij
    exact hcop i j hij
  let n := Nat.chineseRemainderOfFinset (fun i => (r i).val) m Finset.univ
    (fun i _ => (hm i).ne') hpair
  refine ⟨(n.val : ℤ), ?_⟩
  intro i
  have hi : n.val % m i = (r i).val % m i := n.property i (Finset.mem_univ i)
  rw [Nat.mod_eq_of_lt (ZMod.val_lt (r i))] at hi
  apply ZMod.val_injective (m i)
  simpa only [Int.cast_natCast, ZMod.val_natCast] using hi

theorem residue_avoiding_cardinality {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hm : ∀ i, 25 ≤ m i) (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    (r : ∀ i, ZMod (m i)) (T : Finset ℤ) (N z L : ℝ) (hz : 1 < z) (hN : z ^ 4 ≤ N)
    (hinterval : ∀ n ∈ T, L ≤ (n : ℝ) ∧ (n : ℝ) ≤ L + N)
    (havoid : ∀ n ∈ T, ∀ i, (n : ZMod (m i)) ≠ r i) :
    (T.card : ℝ) ≤ 2 * translatedSieveCardinalityConstant * N / sieveMass m z := by
  classical
  obtain ⟨R, hR⟩ := exists_integer_residue_vector m (fun i => by have h := hm i; omega) hcop r
  let e : ℤ ↪ ℤ := ⟨fun n => n - R, by
    intro a b hab
    change a - R = b - R at hab
    omega⟩
  let S := T.map e
  have hSinterval : ∀ n ∈ S, L - R ≤ (n : ℝ) ∧ (n : ℝ) ≤ (L - R) + N := by
    intro n hn
    obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hn
    have h := hinterval k hk
    change L - R ≤ ((k - R : ℤ) : ℝ) ∧ ((k - R : ℤ) : ℝ) ≤ L - R + N
    push_cast
    constructor <;> linarith
  have hSsifted : ∀ n ∈ S, ∀ i, (n : ZMod (m i)) ≠ 0 := by
    intro n hn i hzero
    obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hn
    apply havoid k hk i
    have hsub : (k : ZMod (m i)) - r i = 0 := by
      change ((k - R : ℤ) : ZMod (m i)) = 0 at hzero
      simpa only [Int.cast_sub, hR i] using hzero
    exact sub_eq_zero.mp hsub
  have hcount := translated_sifted_cardinality_linear m hm hcop S N z (L - R) hz hN hSinterval hSsifted
  simpa only [S, Finset.card_map] using hcount

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/AffineSieve.lean -/
section
/- # Sieve counts for values of an affine integer function -/

namespace Erdos12Proof

theorem affine_sifted_cardinality {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hprime : ∀ i, (m i).Prime) (hm : ∀ i, 25 ≤ m i)
    (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    (a d : ℤ) (hd : ∀ i, ¬(m i : ℤ) ∣ d)
    (T : Finset ℤ) (N z L : ℝ) (hz : 1 < z) (hN : z ^ 4 ≤ N)
    (hinterval : ∀ n ∈ T, L ≤ (n : ℝ) ∧ (n : ℝ) ≤ L + N)
    (hvalues : ∀ n ∈ T, ∀ i, ((a + d * n : ℤ) : ZMod (m i)) ≠ 0) :
    (T.card : ℝ) ≤ 2 * translatedSieveCardinalityConstant * N / sieveMass m z := by
  classical
  let : ∀ i, Fact (m i).Prime := fun i => ⟨hprime i⟩
  let r : ∀ i, ZMod (m i) := fun i => -(a : ZMod (m i)) / (d : ZMod (m i))
  have hd0 (i : ι) : (d : ZMod (m i)) ≠ 0 := by
    intro hzero
    exact hd i ((ZMod.intCast_zmod_eq_zero_iff_dvd d (m i)).mp hzero)
  apply residue_avoiding_cardinality m hm hcop r T N z L hz hN hinterval
  intro n hn i hni
  apply hvalues n hn i
  push_cast
  rw [hni]
  dsimp only [r]
  field_simp [hd0 i]
  ring

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/ProgressionSieve.lean -/
section
/- # Sieve counts in one arithmetic progression -/

namespace Erdos12Proof

def progressionQuotients (P : Finset ℕ) (d : ℕ) : Finset ℤ :=
  P.image (fun p : ℕ => ((p / d : ℕ) : ℤ))

theorem progressionQuotients_card (P : Finset ℕ) (a d : ℕ)
    (hresidue : ∀ p ∈ P, p % d = a) : (progressionQuotients P d).card = P.card := by
  unfold progressionQuotients
  apply Finset.card_image_iff.mpr
  intro p hp q hq hpq
  change ((p / d : ℕ) : ℤ) = ((q / d : ℕ) : ℤ) at hpq
  have hquot : p / d = q / d := by exact_mod_cast hpq
  have hpId : a + d * (p / d) = p := by simpa only [hresidue p hp] using Nat.mod_add_div p d
  have hqId : a + d * (q / d) = q := by simpa only [hresidue q hq] using Nat.mod_add_div q d
  rw [hquot] at hpId
  exact hpId.symm.trans hqId

theorem progressionQuotients_interval (P : Finset ℕ) (a d : ℕ) (hd : 0 < d) (x : ℝ)
    (hresidue : ∀ p ∈ P, p % d = a) (hinterval : ∀ p ∈ P, x ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * x) :
    ∀ n ∈ progressionQuotients P d,
      (x - a) / d ≤ (n : ℝ) ∧ (n : ℝ) ≤ (x - a) / d + x / d := by
  intro n hn
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hpId : a + d * (p / d) = p := by simpa only [hresidue p hp] using Nat.mod_add_div p d
  have hpReal : (a : ℝ) + (d : ℝ) * (p / d : ℕ) = p := by exact_mod_cast hpId
  have hpBounds := hinterval p hp
  simp only [Int.cast_natCast]
  constructor
  · apply (div_le_iff₀ hdR).mpr
    nlinarith
  · rw [show (x - (a : ℝ)) / d + x / d = (2 * x - a) / d by ring]
    apply (le_div_iff₀ hdR).mpr
    nlinarith

theorem progression_sifted_cardinality {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hprime : ∀ i, (m i).Prime) (hm : ∀ i, 25 ≤ m i)
    (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    (P : Finset ℕ) (a d : ℕ) (hd : 0 < d) (hndiv : ∀ i, ¬m i ∣ d)
    (hresidue : ∀ p ∈ P, p % d = a) (x z : ℝ)
    (hinterval : ∀ p ∈ P, x ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * x)
    (havoid : ∀ p ∈ P, ∀ i, (p : ZMod (m i)) ≠ 0) (hz : 1 < z) (hN : z ^ 4 ≤ x / d) :
    (P.card : ℝ) ≤ 2 * translatedSieveCardinalityConstant * (x / d) / sieveMass m z := by
  have hvalues : ∀ n ∈ progressionQuotients P d, ∀ i,
      (((a : ℤ) + (d : ℤ) * n : ℤ) : ZMod (m i)) ≠ 0 := by
    intro n hn i
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    have hpId : a + d * (p / d) = p := by simpa only [hresidue p hp] using Nat.mod_add_div p d
    have hpInt : (a : ℤ) + (d : ℤ) * ((p / d : ℕ) : ℤ) = p := by exact_mod_cast hpId
    simpa only [hpInt, Int.cast_natCast] using havoid p hp i
  have h := affine_sifted_cardinality m hprime hm hcop a d
    (fun i hdiv => hndiv i (Int.natCast_dvd_natCast.mp hdiv))
    (progressionQuotients P d) (x / d) z ((x - a) / d) hz hN
    (progressionQuotients_interval P a d hd x hresidue hinterval) hvalues
  simpa only [progressionQuotients_card P a d hresidue] using h

theorem prime_progression_sieve_count {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hprime : ∀ i, (m i).Prime) (hm : ∀ i, 25 ≤ m i)
    (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (a d : ℕ) (hd : 0 < d) (hndiv : ∀ i, ¬m i ∣ d)
    (hresidue : ∀ p ∈ P, p % d = a) (x z : ℝ)
    (hinterval : ∀ p ∈ P, x ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * x)
    (hsmall : ∀ i, (m i : ℝ) < x) (hz : 1 < z) (hN : z ^ 4 ≤ x / d) :
    (P.card : ℝ) ≤ 2 * translatedSieveCardinalityConstant * (x / d) / sieveMass m z := by
  apply progression_sifted_cardinality m hprime hm hcop P a d hd hndiv hresidue x z hinterval _ hz hN
  intro p hp i hzero
  have hdiv := (ZMod.natCast_eq_zero_iff p (m i)).mp hzero
  have heq := (Nat.prime_dvd_prime_iff_eq (hprime i) (hP p hp)).mp hdiv
  have hlt := hsmall i
  rw [heq] at hlt
  linarith [(hinterval p hp).1]

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/IntervalCounting.lean -/
section
/- # Elementary counts of integers in real intervals -/

namespace Erdos12Proof

theorem integer_interval_cardinality_bound (T : Finset ℤ) (L N : ℝ) (hN : 0 ≤ N)
    (hinterval : ∀ n ∈ T, L ≤ (n : ℝ) ∧ (n : ℝ) ≤ L + N) :
    (T.card : ℝ) ≤ N + 1 := by
  classical
  by_cases hT : T.Nonempty
  · let a := T.min' hT
    let b := T.max' hT
    have hab : a ≤ b := Finset.min'_le_max' T hT
    have hsub : T ⊆ Finset.Icc a b := by
      intro n hn
      exact Finset.mem_Icc.mpr ⟨Finset.min'_le T n hn, Finset.le_max' T n hn⟩
    have hcardZ : (T.card : ℤ) ≤ (Finset.Icc a b).card := by
      exact_mod_cast Finset.card_le_card hsub
    rw [Int.card_Icc_of_le a b (by omega : a ≤ b + 1)] at hcardZ
    have hcardR : (T.card : ℝ) ≤ (b : ℝ) + 1 - a := by exact_mod_cast hcardZ
    have hlo := (hinterval a (T.min'_mem hT)).1
    have hhi := (hinterval b (T.max'_mem hT)).2
    linarith
  · have hempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    simp only [hempty, Finset.card_empty, Nat.cast_zero]
    linarith

theorem progression_cardinality_bound (P : Finset ℕ) (a d : ℕ) (hd : 0 < d)
    (hresidue : ∀ p ∈ P, p % d = a) (x : ℝ) (hx : 0 ≤ x)
    (hinterval : ∀ p ∈ P, x ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * x) :
    (P.card : ℝ) ≤ x / d + 1 := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have h := integer_interval_cardinality_bound (progressionQuotients P d) ((x - a) / d) (x / d)
    (div_nonneg hx hdR.le) (progressionQuotients_interval P a d hd x hresidue hinterval)
  simpa only [progressionQuotients_card P a d hresidue] using h

theorem progression_cardinality_linear (P : Finset ℕ) (a d : ℕ) (hd : 0 < d)
    (hresidue : ∀ p ∈ P, p % d = a) (x : ℝ) (hx : 0 ≤ x) (hN : 1 ≤ x / d)
    (hinterval : ∀ p ∈ P, x ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * x) :
    (P.card : ℝ) ≤ 2 * (x / d) := by
  have h := progression_cardinality_bound P a d hd hresidue x hx hinterval
  linarith

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/ProgressionPrimeCount.lean -/
section
/- # A prime-progression count from the finite Selberg sieve -/

namespace Erdos12Proof

def primeModulus (R : Finset ℕ) : ℕ := ∏ p ∈ R, p

theorem primeModulus_pos (R : Finset ℕ) (hR : ∀ p ∈ R, p.Prime) : 0 < primeModulus R := by
  exact Finset.prod_pos (fun p hp => (hR p hp).pos)

noncomputable def progressionPrimeCountConstant : ℝ :=
  16 * translatedSieveCardinalityConstant * smallPrimeSieveCost / fullSieveDensityConstant

theorem progressionPrimeCountConstant_pos : 0 < progressionPrimeCountConstant := by
  have h1 := translatedSieveCardinalityConstant_pos
  have h2 := smallPrimeSieveCost_pos
  have h3 := fullSieveDensityConstant_pos
  unfold progressionPrimeCountConstant
  positivity

theorem prime_progression_large_parameter_count (R : Finset ℕ) (hR : ∀ p ∈ R, p.Prime)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (a : ℕ) (x : ℝ) (hx : 0 < x)
    (hresidue : ∀ p ∈ P, p % primeModulus R = a)
    (hinterval : ∀ p ∈ P, x ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * x)
    (hlarge : roughSieveThreshold ≤ (x / primeModulus R) / 2) :
    (P.card : ℝ) ≤ progressionPrimeCountConstant * (x / primeModulus R) *
      primeSieveEulerCost R / Real.log ((x / primeModulus R) / 2) := by
  let N : ℝ := x / primeModulus R
  let D : ℝ := N / 2
  let z : ℝ := restrictionSieveLevel D N
  have hd : 0 < primeModulus R := primeModulus_pos R hR
  have hdR : 0 < (primeModulus R : ℝ) := by exact_mod_cast hd
  have hN : 0 < N := div_pos hx hdR
  have hDN : D ≤ N := by dsimp [D]; linarith
  have hD : roughSieveThreshold ≤ D := hlarge
  have hD0 : 0 < D := lt_of_lt_of_le roughSieveThreshold_pos hD
  have hDx : D < x := by
    have hNx : N ≤ x := div_le_self hx.le (by exact_mod_cast (show 1 ≤ primeModulus R by omega))
    dsimp [D]
    linarith
  have hlogs := roughSieveThreshold_log hD
  have hlog : 0 < Real.log D := by linarith [hlogs.1]
  obtain ⟨hz, _, hzN, _⟩ := restrictionSieveLevel_properties D N hD0 hDN hlogs.1
  let m : progressionSievePrimes D R → ℕ := fun p => p.val
  have hprime : ∀ i, (m i).Prime := fun p => (progressionSievePrimes_properties hD0.le R p.property).1
  have hm : ∀ i, 25 ≤ m i := fun p => (progressionSievePrimes_properties hD0.le R p.property).2.1
  have hcop : ∀ i j, i ≠ j → (m i).Coprime (m j) := by
    intro p q hpq
    exact (Nat.coprime_primes (hprime p) (hprime q)).mpr (fun h => hpq (Subtype.ext h))
  have hndiv : ∀ i, ¬m i ∣ primeModulus R := by
    intro p
    exact progressionSievePrimes_not_dvd hD0.le R hR p.property
  have hsmall : ∀ i, (m i : ℝ) < x := fun p =>
    (progressionSievePrimes_properties hD0.le R p.property).2.2.1.trans_lt hDx
  have hraw := prime_progression_sieve_count m hprime hm hcop P hP a (primeModulus R) hd hndiv
    hresidue x z hinterval hsmall hz hzN
  have hmass : ((fullSieveDensityConstant / 8) * Real.log D) /
      (smallPrimeSieveCost * primeSieveEulerCost R) ≤ sieveMass m z := by
    change _ ≤ sieveMass (fun p : progressionSievePrimes D R => (p : ℕ)) z
    rw [finitePrimeSieveMass_eq]
    exact progression_sieve_mass_lower D N hD hDN R hR
  have hden : 0 < ((fullSieveDensityConstant / 8) * Real.log D) /
      (smallPrimeSieveCost * primeSieveEulerCost R) := by
    exact div_pos (mul_pos (div_pos fullSieveDensityConstant_pos (by norm_num)) hlog)
      (mul_pos smallPrimeSieveCost_pos (primeSieveEulerCost_pos R hR))
  calc
    _ ≤ 2 * translatedSieveCardinalityConstant * N / sieveMass m z := hraw
    _ ≤ 2 * translatedSieveCardinalityConstant * N /
        (((fullSieveDensityConstant / 8) * Real.log D) /
          (smallPrimeSieveCost * primeSieveEulerCost R)) :=
      div_le_div_of_nonneg_left
        (mul_nonneg (mul_nonneg (by norm_num) translatedSieveCardinalityConstant_pos.le) hN.le) hden hmass
    _ = _ := by unfold progressionPrimeCountConstant; dsimp [D, N]; field_simp; ring

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/BrunTitchmarsh.lean -/
section
/- # A uniform prime-progression bound for squarefree moduli -/

namespace Erdos12Proof

theorem primeSieveEulerCost_ge_one (R : Finset ℕ) (hR : ∀ p ∈ R, p.Prime) :
    1 ≤ primeSieveEulerCost R := by
  apply Finset.one_le_prod₀
  intro p hp
  exact le_add_of_nonneg_right (sieveLocalWeight_pos (hR p hp).one_lt).le

theorem progression_threshold_log_pos : 0 < Real.log (2 * roughSieveThreshold) := by
  have h := (roughSieveThreshold_log (D := roughSieveThreshold) le_rfl).1
  rw [Real.log_mul (by norm_num) roughSieveThreshold_pos.ne']
  linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

noncomputable def brunTitchmarshConstant : ℝ :=
  4 * (progressionPrimeCountConstant + Real.log (2 * roughSieveThreshold))

theorem brunTitchmarshConstant_pos : 0 < brunTitchmarshConstant := by
  unfold brunTitchmarshConstant
  exact mul_pos (by norm_num) (add_pos progressionPrimeCountConstant_pos progression_threshold_log_pos)

theorem prime_progression_count_euler (R : Finset ℕ) (hR : ∀ p ∈ R, p.Prime)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (a : ℕ) (x : ℝ) (hx : 2 ≤ x)
    (hmodulus : (primeModulus R : ℝ) ^ 2 ≤ x)
    (hresidue : ∀ p ∈ P, p % primeModulus R = a)
    (hinterval : ∀ p ∈ P, x ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * x) :
    (P.card : ℝ) ≤ brunTitchmarshConstant * (x / primeModulus R) *
      primeSieveEulerCost R / Real.log x := by
  let d := primeModulus R
  let N : ℝ := x / d
  let D : ℝ := N / 2
  have hd : 0 < d := primeModulus_pos R hR
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hdR1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hx0 : 0 < x := by linarith
  have hN0 : 0 < N := div_pos hx0 hdR
  have hD0 : 0 < D := div_pos hN0 (by norm_num)
  have hdN : (d : ℝ) ≤ N := by
    apply (le_div_iff₀ hdR).mpr
    nlinarith [hmodulus]
  have hN1 : 1 ≤ N := hdR1.trans hdN
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hxId : x = (d : ℝ) * N := by dsimp [N]; field_simp
  have hlogxN : Real.log x ≤ 2 * Real.log N := by
    rw [hxId, Real.log_mul hdR.ne' hN0.ne']
    linarith [Real.log_le_log hdR hdN]
  have hcost : 1 ≤ primeSieveEulerCost R := primeSieveEulerCost_ge_one R hR
  have hcost0 := primeSieveEulerCost_pos R hR
  by_cases hlarge : roughSieveThreshold ≤ D
  · have hraw := prime_progression_large_parameter_count R hR P hP a x hx0 hresidue hinterval hlarge
    have hlogD : 0 < Real.log D := by linarith [(roughSieveThreshold_log hlarge).1]
    have hNId : N = 2 * D := by dsimp [D]; ring
    have hlogN : Real.log N = Real.log 2 + Real.log D := by
      rw [hNId, Real.log_mul (by norm_num) hD0.ne']
    have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h
      exact h
    have hlogBound : Real.log x ≤ 4 * Real.log D := by
      linarith [(roughSieveThreshold_log hlarge).1]
    have hC : 4 * progressionPrimeCountConstant ≤ brunTitchmarshConstant := by
      unfold brunTitchmarshConstant
      linarith [progression_threshold_log_pos]
    calc
      _ ≤ progressionPrimeCountConstant * N * primeSieveEulerCost R / Real.log D := hraw
      _ ≤ (4 * progressionPrimeCountConstant) * N * primeSieveEulerCost R / Real.log x := by
        apply (div_le_div_iff₀ hlogD hlogx).mpr
        calc
          _ ≤ (progressionPrimeCountConstant * N * primeSieveEulerCost R) * (4 * Real.log D) :=
            mul_le_mul_of_nonneg_left hlogBound
              (mul_nonneg (mul_nonneg progressionPrimeCountConstant_pos.le hN0.le) hcost0.le)
          _ = _ := by ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hN0.le) hcost0.le) hlogx.le
  · have hDlt : D < roughSieveThreshold := lt_of_not_ge hlarge
    have hNbound : N ≤ 2 * roughSieveThreshold := by dsimp [D] at hDlt; linarith
    have hlogBound : Real.log x ≤ 2 * Real.log (2 * roughSieveThreshold) := by
      linarith [Real.log_le_log hN0 hNbound]
    have hC : 2 * Real.log x ≤ brunTitchmarshConstant := by
      unfold brunTitchmarshConstant
      linarith [progressionPrimeCountConstant_pos]
    have hraw := progression_cardinality_linear P a d hd hresidue x hx0.le hN1 hinterval
    apply hraw.trans
    apply (le_div_iff₀ hlogx).mpr
    calc
      (2 * N) * Real.log x = N * (2 * Real.log x) := by ring
      _ ≤ N * brunTitchmarshConstant := mul_le_mul_of_nonneg_left hC hN0.le
      _ ≤ N * (brunTitchmarshConstant * primeSieveEulerCost R) :=
        mul_le_mul_of_nonneg_left
          (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hcost brunTitchmarshConstant_pos.le) hN0.le
      _ = _ := by ring

theorem prime_progression_count (R : Finset ℕ) (hR : ∀ p ∈ R, p.Prime)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (a : ℕ) (x : ℝ) (hx : 2 ≤ x)
    (hmodulus : (primeModulus R : ℝ) ^ 2 ≤ x)
    (hresidue : ∀ p ∈ P, p % primeModulus R = a)
    (hinterval : ∀ p ∈ P, x ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * x) :
    (P.card : ℝ) ≤ brunTitchmarshConstant * x /
      ((∏ p ∈ R, ((p : ℝ) - 1)) * Real.log x) := by
  have hprod0 : (((∏ p ∈ R, p : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (primeModulus_pos R hR).ne'
  have h := prime_progression_count_euler R hR P hP a x hx hmodulus hresidue hinterval
  rw [primeSieveEulerCost_ratio R hR] at h
  calc
    _ ≤ brunTitchmarshConstant * (x / primeModulus R) *
        (((∏ p ∈ R, p : ℕ) : ℝ) / (∏ p ∈ R, ((p : ℝ) - 1))) / Real.log x := h
    _ = _ := by unfold primeModulus; field_simp

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/PrimeResidueCounts.lean -/
section
/- # Counting primes confined to a finite family of residue classes -/

namespace Erdos12Proof

theorem prime_residue_class_count (R : Finset ℕ) (hR : ∀ p ∈ R, p.Prime)
    (P S : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (x : ℝ) (hx : 2 ≤ x)
    (hmodulus : (primeModulus R : ℝ) ^ 2 ≤ x)
    (hclasses : ∀ p ∈ P, p % primeModulus R ∈ S)
    (hinterval : ∀ p ∈ P, x ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * x) :
    (P.card : ℝ) ≤ brunTitchmarshConstant * x * S.card /
      ((∏ p ∈ R, ((p : ℝ) - 1)) * Real.log x) := by
  classical
  have hcard : P.card = ∑ a ∈ S, (P.filter (fun p => p % primeModulus R = a)).card :=
    Finset.card_eq_sum_card_fiberwise hclasses
  have hfibre (a : ℕ) : ((P.filter (fun p => p % primeModulus R = a)).card : ℝ) ≤
      brunTitchmarshConstant * x / ((∏ p ∈ R, ((p : ℝ) - 1)) * Real.log x) := by
    apply prime_progression_count R hR _ (fun p hp => hP p (Finset.mem_filter.mp hp).1)
      a x hx hmodulus
    · intro p hp
      exact (Finset.mem_filter.mp hp).2
    · intro p hp
      exact hinterval p (Finset.mem_filter.mp hp).1
  calc
    (P.card : ℝ) = ∑ a ∈ S, ((P.filter (fun p => p % primeModulus R = a)).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ ∑ _a ∈ S, brunTitchmarshConstant * x /
        ((∏ p ∈ R, ((p : ℝ) - 1)) * Real.log x) := Finset.sum_le_sum (fun a _ => hfibre a)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

theorem prime_restricted_residue_count (R : Finset ℕ) (hR : ∀ p ∈ R, p.Prime)
    (P S : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (x δ : ℝ) (hx : 2 ≤ x)
    (hmodulus : (primeModulus R : ℝ) ^ 2 ≤ x)
    (hclasses : ∀ p ∈ P, p % primeModulus R ∈ S)
    (hclassCount : (S.card : ℝ) ≤ δ * ∏ p ∈ R, ((p : ℝ) - 1))
    (hinterval : ∀ p ∈ P, x ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * x) :
    (P.card : ℝ) ≤ brunTitchmarshConstant * δ * x / Real.log x := by
  have hphi : 0 < ∏ p ∈ R, ((p : ℝ) - 1) := by
    apply Finset.prod_pos
    intro p hp
    exact sub_pos.mpr (by exact_mod_cast (hR p hp).one_lt)
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have h := prime_residue_class_count R hR P S hP x hx hmodulus hclasses hinterval
  calc
    _ ≤ brunTitchmarshConstant * x * S.card /
        ((∏ p ∈ R, ((p : ℝ) - 1)) * Real.log x) := h
    _ ≤ brunTitchmarshConstant * x * (δ * ∏ p ∈ R, ((p : ℝ) - 1)) /
        ((∏ p ∈ R, ((p : ℝ) - 1)) * Real.log x) := by
      apply div_le_div_of_nonneg_right _ (mul_pos hphi hlog).le
      exact mul_le_mul_of_nonneg_left hclassCount
        (mul_nonneg brunTitchmarshConstant_pos.le (by linarith))
    _ = _ := by field_simp

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/CRTResidueCounting.lean -/
section
/- # Counting occupied residue classes through the Chinese remainder theorem -/

namespace Erdos12Proof

theorem residue_image_card_le_product {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j)) (Q : Finset ℕ) :
    (Q.image (fun n : ℕ => (n : ZMod (∏ i, m i)))).card ≤
      ∏ i, (Q.image (fun n : ℕ => (n : ZMod (m i)))).card := by
  classical
  let S := Q.image (fun n : ℕ => (n : ZMod (∏ i, m i)))
  let T := fun i => Q.image (fun n : ℕ => (n : ZMod (m i)))
  let e := ZMod.prodEquivPi m (fun i j hij => hcop i j hij)
  have hnat (n : ℕ) (i : ι) : e (n : ZMod (∏ j, m j)) i = (n : ZMod (m i)) := by
    simp [e]
  let code : S → ∀ i, T i := fun x i => ⟨e x.val i, by
    obtain ⟨n, hn, hnx⟩ := Finset.mem_image.mp x.property
    rw [← hnx, hnat]
    exact Finset.mem_image_of_mem _ hn⟩
  have hcode : Function.Injective code := by
    intro x y hxy
    apply Subtype.ext
    apply e.injective
    funext i
    exact congrArg Subtype.val (congrFun hxy i)
  have h := Fintype.card_le_of_injective code hcode
  simpa only [Fintype.card_coe, Fintype.card_pi, S, T] using h

theorem modulo_image_card {M : ℕ} [NeZero M] (Q : Finset ℕ) :
    (Q.image (fun n => n % M)).card = (Q.image (fun n : ℕ => (n : ZMod M))).card := by
  have hmap : (Q.image (fun n : ℕ => (n : ZMod M))).image ZMod.val =
      Q.image (fun n => n % M) := by
    simp [Finset.image_image, Function.comp_def]
  rw [← hmap, Finset.card_image_of_injective _ (ZMod.val_injective M)]

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/ResiduePairs.lean -/
section
/- # Counting the residue classes permitted by an opposite-pair restriction -/

namespace Erdos12Proof

theorem twice_card_le_of_neg_free {α : Type*} [AddGroup α] [DecidableEq α]
    (s U : Finset α) (hsU : s ⊆ U) (hnegU : ∀ x ∈ s, -x ∈ U)
    (hfree : ∀ x ∈ s, -x ∉ s) : 2 * s.card ≤ U.card := by
  have hdisj : Disjoint s (s.image (fun x => -x)) := by
    apply Finset.disjoint_left.mpr
    intro a ha ha'
    obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp ha'
    exact hfree b hb (heq ▸ ha)
  have hsub : s ∪ s.image (fun x => -x) ⊆ U := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hsU hx
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact hnegU y hy
  have hcard : (s.image (fun x => -x)).card = s.card :=
    Finset.card_image_of_injective _ neg_injective
  have hbound := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hcard] at hbound
  omega

theorem prime_not_dvd_larger_prime {r p : ℕ} (hr : 1 < r) (hp : p.Prime) (hrp : r < p) :
    ¬r ∣ p := by
  intro hdiv
  rcases (Nat.dvd_prime hp).mp hdiv with heq | heq
  · omega
  · omega

theorem occupied_residue_classes_le_half {r : ℕ} (hr : r.Prime) (hr2 : 2 < r)
    (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime ∧ r < p)
    (hopposite : ∀ p ∈ Q, ∀ q ∈ Q, r ∣ p + q → p = q) :
    2 * (Q.image (fun p : ℕ => (p : ZMod r))).card ≤ r - 1 := by
  classical
  let _ : NeZero r := ⟨hr.ne_zero⟩
  let S : Finset (ZMod r) := Q.image (fun p : ℕ => (p : ZMod r))
  have hnonzero : ∀ x ∈ S, x ≠ 0 := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    intro hz
    exact prime_not_dvd_larger_prime (by omega) (hQ p hp).1 (hQ p hp).2
      ((ZMod.natCast_eq_zero_iff p r).mp hz)
  have hfree : ∀ x ∈ S, -x ∉ S := by
    intro x hx hnx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q, hq, hqeq⟩ := Finset.mem_image.mp hnx
    have hsum : ((p + q : ℕ) : ZMod r) = 0 := by
      rw [Nat.cast_add, hqeq, add_neg_cancel]
    have hdiv := (ZMod.natCast_eq_zero_iff (p + q) r).mp hsum
    have hpq := hopposite p hp q hq hdiv
    rw [← hpq, ← two_mul] at hdiv
    rcases hr.dvd_mul.mp hdiv with hd2 | hdp
    · exact (Nat.not_dvd_of_pos_of_lt (by decide) hr2) hd2
    · exact prime_not_dvd_larger_prime (by omega) (hQ p hp).1 (hQ p hp).2 hdp
  have hsU : S ⊆ Finset.univ.erase (0 : ZMod r) := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨hnonzero x hx, Finset.mem_univ _⟩
  have hnegU : ∀ x ∈ S, -x ∈ Finset.univ.erase (0 : ZMod r) := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨neg_ne_zero.mpr (hnonzero x hx), Finset.mem_univ _⟩
  have hbound := twice_card_le_of_neg_free S (Finset.univ.erase 0) hsU hnegU hfree
  simpa only [Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod r)),
    Finset.card_univ, ZMod.card] using hbound

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/OppositePrimeCount.lean -/
section
/- # Prime counts under several opposite-pair restrictions -/

namespace Erdos12Proof

theorem opposite_residue_density (R Q : Finset ℕ)
    (hR : ∀ r ∈ R, r.Prime ∧ 2 < r)
    (hQ : ∀ p ∈ Q, p.Prime)
    (horder : ∀ r ∈ R, ∀ p ∈ Q, r < p)
    (hopposite : ∀ r ∈ R, ∀ p ∈ Q, ∀ q ∈ Q, r ∣ p + q → p = q) :
    ((Q.image (fun p => p % primeModulus R)).card : ℝ) ≤
      (1 / 2 : ℝ) ^ R.card * ∏ r ∈ R, ((r : ℝ) - 1) := by
  classical
  let m : R → ℕ := Subtype.val
  have hm : (∏ r : R, m r) = primeModulus R := by
    exact Finset.prod_coe_sort R (fun r : ℕ => r)
  have hcop : ∀ i j : R, i ≠ j → (m i).Coprime (m j) := by
    intro i j hij
    exact (Nat.coprime_primes (hR i i.property).1 (hR j j.property).1).mpr
      (fun h => hij (Subtype.ext h))
  have hcard := residue_image_card_le_product m hcop Q
  rw [hm] at hcard
  let : NeZero (primeModulus R) := ⟨(primeModulus_pos R (fun r hr => (hR r hr).1)).ne'⟩
  rw [← modulo_image_card Q] at hcard
  have hlocal (r : R) : ((Q.image (fun p : ℕ => (p : ZMod (m r)))).card : ℝ) ≤
      (1 / 2 : ℝ) * ((r.val : ℝ) - 1) := by
    have h := occupied_residue_classes_le_half (hR r r.property).1 (hR r r.property).2
      Q (fun p hp => ⟨hQ p hp, horder r r.property p hp⟩) (hopposite r r.property)
    have hr1 : 1 ≤ r.val := (hR r r.property).1.one_lt.le
    have hc : (2 : ℝ) * (Q.image (fun p : ℕ => (p : ZMod (m r)))).card ≤
        ((r.val - 1 : ℕ) : ℝ) := by exact_mod_cast h
    rw [Nat.cast_sub hr1, Nat.cast_one] at hc
    linarith
  calc
    _ ≤ ∏ r : R, ((Q.image (fun p : ℕ => (p : ZMod (m r)))).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ ∏ r : R, (1 / 2 : ℝ) * ((r.val : ℝ) - 1) := by
      apply Finset.prod_le_prod₀
      · intro r _
        exact Nat.cast_nonneg _
      · intro r _
        exact hlocal r
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_coe]
      rw [Finset.prod_coe_sort R (fun r : ℕ => (r : ℝ) - 1)]

theorem prime_opposite_pair_count (R Q : Finset ℕ)
    (hR : ∀ r ∈ R, r.Prime ∧ 2 < r)
    (hQ : ∀ p ∈ Q, p.Prime)
    (horder : ∀ r ∈ R, ∀ p ∈ Q, r < p)
    (hopposite : ∀ r ∈ R, ∀ p ∈ Q, ∀ q ∈ Q, r ∣ p + q → p = q)
    (x : ℝ) (hx : 2 ≤ x) (hmodulus : (primeModulus R : ℝ) ^ 2 ≤ x)
    (hinterval : ∀ p ∈ Q, x ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * x) :
    (Q.card : ℝ) ≤ brunTitchmarshConstant * (1 / 2 : ℝ) ^ R.card * x / Real.log x := by
  apply prime_restricted_residue_count R (fun r hr => (hR r hr).1) Q
    (Q.image (fun p => p % primeModulus R)) hQ x ((1 / 2 : ℝ) ^ R.card) hx hmodulus
  · intro p hp
    exact Finset.mem_image_of_mem _ hp
  · exact opposite_residue_density R Q hR hQ horder hopposite
  · exact hinterval

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/PrimeHarmonicIntervals.lean -/
section
/- # Reciprocal sums over bounded logarithmic intervals -/

namespace Erdos12Proof

theorem harmonic_le_card_div (Q : Finset ℕ) {x : ℝ} (hx : 0 < x)
    (hQ : ∀ p ∈ Q, x ≤ (p : ℝ)) : harmonic Q ≤ Q.card / x := by
  calc
    _ ≤ ∑ _p ∈ Q, (1 / x : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact one_div_le_one_div_of_le hx (hQ p hp)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

theorem harmonic_dyadic_cover (Q : Finset ℕ) {x C : ℝ} (N : ℕ)
    (hinterval : ∀ p ∈ Q, x ≤ (p : ℝ) ∧ (p : ℝ) < x * 2 ^ N)
    (hbin : ∀ j < N, ∀ T : Finset ℕ, T ⊆ Q →
      (∀ p ∈ T, x * 2 ^ j ≤ (p : ℝ) ∧ (p : ℝ) < x * 2 ^ (j + 1)) →
      harmonic T ≤ C) : harmonic Q ≤ N * C := by
  induction N generalizing Q with
  | zero =>
      have hQ : Q = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro p hp
        have h := hinterval p hp
        simp only [pow_zero, mul_one] at h
        linarith
      simp only [hQ, harmonic, Finset.sum_empty, Nat.cast_zero, zero_mul, le_refl]
  | succ N ih =>
      let T := Q.filter (fun p : ℕ => (p : ℝ) < x * 2 ^ N)
      let U := Q.filter (fun p : ℕ => ¬(p : ℝ) < x * 2 ^ N)
      have hT : harmonic T ≤ N * C := by
        apply ih
        · intro p hp
          exact ⟨(hinterval p (Finset.mem_filter.mp hp).1).1, (Finset.mem_filter.mp hp).2⟩
        · intro j hj S hST hS
          exact hbin j (Nat.lt_succ_of_lt hj) S
            (hST.trans (Finset.filter_subset _ _)) hS
      have hU : harmonic U ≤ C := by
        apply hbin N (Nat.lt_succ_self N) U (Finset.filter_subset _ _)
        intro p hp
        exact ⟨le_of_not_gt (Finset.mem_filter.mp hp).2,
          (hinterval p (Finset.mem_filter.mp hp).1).2⟩
      have hsplit : harmonic Q = harmonic T + harmonic U := by
        exact (Finset.sum_filter_add_sum_filter_not Q
          (fun p : ℕ => (p : ℝ) < x * 2 ^ N) (fun p => (1 / p : ℝ))).symm
      rw [hsplit, Nat.cast_succ]
      nlinarith

theorem prime_harmonic_dyadic_interval (R Q : Finset ℕ)
    (hR : ∀ r ∈ R, r.Prime ∧ 2 < r) (hQ : ∀ p ∈ Q, p.Prime)
    (horder : ∀ r ∈ R, ∀ p ∈ Q, r < p)
    (hopposite : ∀ r ∈ R, ∀ p ∈ Q, ∀ q ∈ Q, r ∣ p + q → p = q)
    (x : ℝ) (hx : 2 ≤ x) (hmodulus : (primeModulus R : ℝ) ^ 2 ≤ x) (N : ℕ)
    (hinterval : ∀ p ∈ Q, x ≤ (p : ℝ) ∧ (p : ℝ) < x * 2 ^ N) :
    harmonic Q ≤ N * (brunTitchmarshConstant * (1 / 2 : ℝ) ^ R.card / Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  apply harmonic_dyadic_cover Q N hinterval
  intro j _ T hT hTinterval
  have hpow : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hxj : x ≤ x * 2 ^ j := le_mul_of_one_le_right hx0.le hpow
  have hxj0 : 0 < x * 2 ^ j := lt_of_lt_of_le hx0 hxj
  have hlogj : Real.log x ≤ Real.log (x * 2 ^ j) := Real.log_le_log hx0 hxj
  have hcount := prime_opposite_pair_count R T hR (fun p hp => hQ p (hT hp))
    (fun r hr p hp => horder r hr p (hT hp))
    (fun r hr p hp q hq => hopposite r hr p (hT hp) q (hT hq))
    (x * 2 ^ j) (hx.trans hxj) (hmodulus.trans hxj) (by
      intro p hp
      obtain ⟨hlo, hhi⟩ := hTinterval p hp
      refine ⟨hlo, ?_⟩
      calc
        (p : ℝ) ≤ x * 2 ^ (j + 1) := hhi.le
        _ = 2 * (x * 2 ^ j) := by rw [pow_succ]; ring)
  calc
    harmonic T ≤ T.card / (x * 2 ^ j) := harmonic_le_card_div T hxj0 (fun p hp => (hTinterval p hp).1)
    _ ≤ (brunTitchmarshConstant * (1 / 2 : ℝ) ^ R.card * (x * 2 ^ j) /
        Real.log (x * 2 ^ j)) / (x * 2 ^ j) :=
      div_le_div_of_nonneg_right hcount hxj0.le
    _ = brunTitchmarshConstant * (1 / 2 : ℝ) ^ R.card / Real.log (x * 2 ^ j) := by
      field_simp
    _ ≤ _ := by
      apply div_le_div_of_nonneg_left _ hlogx hlogj
      exact mul_nonneg brunTitchmarshConstant_pos.le (by positivity)

noncomputable def primeHarmonicWindowConstant : ℝ :=
  4 * brunTitchmarshConstant / Real.log 2

theorem primeHarmonicWindowConstant_pos : 0 < primeHarmonicWindowConstant := by
  exact div_pos (mul_pos (by norm_num) brunTitchmarshConstant_pos)
    (Real.log_pos (by norm_num))

theorem prime_harmonic_cubic_interval (R Q : Finset ℕ)
    (hR : ∀ r ∈ R, r.Prime ∧ 2 < r) (hQ : ∀ p ∈ Q, p.Prime)
    (horder : ∀ r ∈ R, ∀ p ∈ Q, r < p)
    (hopposite : ∀ r ∈ R, ∀ p ∈ Q, ∀ q ∈ Q, r ∣ p + q → p = q)
    (x : ℝ) (hx : 2 ≤ x) (hmodulus : (primeModulus R : ℝ) ^ 2 ≤ x)
    (hinterval : ∀ p ∈ Q, x ≤ (p : ℝ) ∧ (p : ℝ) ≤ x ^ 3) :
    harmonic Q ≤ primeHarmonicWindowConstant * (1 / 2 : ℝ) ^ R.card := by
  have hx0 : 0 < x := by linarith
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  obtain ⟨j, hjlo, hjhi⟩ := exists_nat_pow_near (by linarith : 1 ≤ x) (by norm_num : (1 : ℝ) < 2)
  have hj1 : 1 ≤ j := by
    by_contra h
    have : j = 0 := by omega
    subst j
    norm_num at hjhi
    linarith
  have hlog : (j : ℝ) * Real.log 2 ≤ Real.log x := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ j) hjlo
    simpa only [Real.log_pow] using h
  have hcover : x ^ 3 < x * 2 ^ (2 * (j + 1)) := by
    have hsq : x ^ 2 < (2 ^ (j + 1) : ℝ) ^ 2 := pow_lt_pow_left₀ hjhi hx0.le (by norm_num)
    have h := mul_lt_mul_of_pos_left hsq hx0
    rw [← pow_mul] at h
    convert h using 1 <;> ring
  have h := prime_harmonic_dyadic_interval R Q hR hQ horder hopposite x hx hmodulus
    (2 * (j + 1)) (fun p hp => ⟨(hinterval p hp).1, (hinterval p hp).2.trans_lt hcover⟩)
  have hlength : ((2 * (j + 1) : ℕ) : ℝ) / Real.log x ≤ 4 / Real.log 2 := by
    apply (div_le_div_iff₀ hlx hl2).mpr
    have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    push_cast
    nlinarith
  calc
    _ ≤ (2 * (j + 1) : ℕ) *
        (brunTitchmarshConstant * (1 / 2 : ℝ) ^ R.card / Real.log x) := h
    _ = (((2 * (j + 1) : ℕ) : ℝ) / Real.log x) *
        (brunTitchmarshConstant * (1 / 2 : ℝ) ^ R.card) := by ring
    _ ≤ (4 / Real.log 2) * (brunTitchmarshConstant * (1 / 2 : ℝ) ^ R.card) :=
      mul_le_mul_of_nonneg_right hlength
        (mul_nonneg brunTitchmarshConstant_pos.le (by positivity))
    _ = _ := by unfold primeHarmonicWindowConstant; ring

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/PrimeUniformBound.lean -/
section
/- # A uniform reciprocal bound for prime sets with Property P -/

namespace Erdos12Proof

theorem prime_guarded_harmonic_bound (R Q : Finset ℕ)
    (hR : ∀ r ∈ R, r.Prime ∧ 2 < r)
    (hQ : ∀ p ∈ Q, p.Prime ∧ 2 < p) (hP : PropertyP (Q : Set ℕ))
    (horder : ∀ r ∈ R, ∀ p ∈ Q, r < p)
    (hopposite : ∀ r ∈ R, ∀ p ∈ Q, ∀ q ∈ Q, r ∣ p + q → p = q)
    (hthreshold : ∀ p ∈ Q, primeModulus R ^ 2 ≤ p) :
    harmonic Q ≤ 2 * primeHarmonicWindowConstant * (1 / 2 : ℝ) ^ R.card := by
  classical
  induction Q using Finset.strongInductionOn generalizing R with
  | _ Q ih =>
      by_cases hempty : Q = ∅
      · subst Q
        simp only [harmonic, Finset.sum_empty]
        exact mul_nonneg (mul_nonneg (by norm_num) primeHarmonicWindowConstant_pos.le)
          (by positivity)
      have hne : Q.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
      let p := Q.min' hne
      have hpQ : p ∈ Q := Finset.min'_mem Q hne
      have hp : p.Prime ∧ 2 < p := hQ p hpQ
      have hmin : ∀ q ∈ Q, p ≤ q := fun q hq => Finset.min'_le Q q hq
      let M := primeModulus R
      have hM : 0 < M := primeModulus_pos R (fun r hr => (hR r hr).1)
      have hMp : p ≤ M * p := Nat.le_mul_of_pos_left p hM
      have hpsq : p < (M * p) ^ 2 := by nlinarith [hp.2]
      have hpR : p ∉ R := by
        intro hpR
        exact (Nat.lt_irrefl p) (horder p hpR p hpQ)
      let S := Q.filter (fun q => q < (M * p) ^ 2)
      let T := Q.filter (fun q => ¬q < (M * p) ^ 2)
      have hSsub : S ⊆ Q := Finset.filter_subset _ _
      have hTsub : T ⊆ Q := Finset.filter_subset _ _
      have hTstrict : T ⊂ Q := by
        apply (Finset.ssubset_iff_of_subset hTsub).mpr
        refine ⟨p, hpQ, ?_⟩
        simp only [T, Finset.mem_filter, not_and]
        exact fun _ => not_not.mpr hpsq
      have hwindow : harmonic S ≤ primeHarmonicWindowConstant * (1 / 2 : ℝ) ^ R.card := by
        apply prime_harmonic_cubic_interval R S hR (fun q hq => (hQ q (hSsub hq)).1)
          (fun r hr q hq => horder r hr q (hSsub hq))
          (fun r hr q hq t ht => hopposite r hr q (hSsub hq) t (hSsub ht))
          (p : ℝ) (by exact_mod_cast hp.1.two_le) (by exact_mod_cast hthreshold p hpQ)
        intro q hq
        have hqhi : q < (M * p) ^ 2 := (Finset.mem_filter.mp hq).2
        have hbase : (M : ℝ) ^ 2 ≤ (p : ℝ) := by exact_mod_cast hthreshold p hpQ
        have hupper : ((M * p : ℕ) : ℝ) ^ 2 ≤ (p : ℝ) ^ 3 := by
          push_cast
          nlinarith [mul_le_mul_of_nonneg_right hbase (sq_nonneg (p : ℝ))]
        exact ⟨by exact_mod_cast hmin q (hSsub hq),
          (by exact_mod_cast hqhi.le : (q : ℝ) ≤ ((M * p : ℕ) : ℝ) ^ 2).trans hupper⟩
      have hRinsert : ∀ r ∈ insert p R, r.Prime ∧ 2 < r := by
        intro r hr
        rcases Finset.mem_insert.mp hr with rfl | hr
        · exact hp
        · exact hR r hr
      have hTprime : ∀ q ∈ T, q.Prime ∧ 2 < q := fun q hq => hQ q (hTsub hq)
      have hpT : ∀ q ∈ T, p < q := by
        intro q hq
        exact hpsq.trans_le (Nat.le_of_not_gt (Finset.mem_filter.mp hq).2)
      have hTorder : ∀ r ∈ insert p R, ∀ q ∈ T, r < q := by
        intro r hr q hq
        rcases Finset.mem_insert.mp hr with rfl | hr
        · exact hpT q hq
        · exact horder r hr q (hTsub hq)
      have hTopposite : ∀ r ∈ insert p R, ∀ q ∈ T, ∀ t ∈ T, r ∣ q + t → q = t := by
        intro r hr q hq t ht hdiv
        rcases Finset.mem_insert.mp hr with rfl | hr
        · exact hP hpQ (hTsub hq) (hTsub ht) hdiv (hpT q hq) (hpT t ht)
        · exact hopposite r hr q (hTsub hq) t (hTsub ht) hdiv
      have hTthreshold : ∀ q ∈ T, primeModulus (insert p R) ^ 2 ≤ q := by
        intro q hq
        have hqlo := Nat.le_of_not_gt (Finset.mem_filter.mp hq).2
        simpa only [primeModulus, Finset.prod_insert hpR, Nat.mul_comm, M] using hqlo
      have htail := ih T hTstrict (insert p R) hRinsert hTprime (hP.mono hTsub)
        hTorder hTopposite hTthreshold
      rw [Finset.card_insert_of_notMem hpR, pow_succ] at htail
      have hsplit : harmonic Q = harmonic S + harmonic T :=
        (Finset.sum_filter_add_sum_filter_not Q (fun q => q < (M * p) ^ 2)
          (fun q => (1 / q : ℝ))).symm
      rw [hsplit]
      linarith

noncomputable def primeHarmonicConstant : ℝ := 1 + 2 * primeHarmonicWindowConstant

theorem primeHarmonicConstant_pos : 0 < primeHarmonicConstant := by
  unfold primeHarmonicConstant
  linarith [primeHarmonicWindowConstant_pos]

theorem prime_harmonic_uniform (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (hP : PropertyP (Q : Set ℕ)) : harmonic Q ≤ primeHarmonicConstant := by
  classical
  have hsub : Q.erase 2 ⊆ Q := Finset.erase_subset 2 Q
  have hodd : ∀ p ∈ Q.erase 2, p.Prime ∧ 2 < p := by
    intro p hp
    have hp' := Finset.mem_erase.mp hp
    exact ⟨hQ p hp'.2, by have := (hQ p hp'.2).two_le; omega⟩
  have h := prime_guarded_harmonic_bound ∅ (Q.erase 2) (by simp) hodd (hP.mono hsub)
    (by simp) (by simp) (by
      intro p hp
      simpa only [primeModulus, Finset.prod_empty, one_pow] using (hodd p hp).1.one_lt.le)
  simp only [Finset.card_empty, pow_zero, mul_one] at h
  by_cases htwo : 2 ∈ Q
  · have hsplit : harmonic (Q.erase 2) + (1 / 2 : ℝ) = harmonic Q := by
      exact Finset.sum_erase_add Q (fun p => (1 / p : ℝ)) htwo
    unfold primeHarmonicConstant
    linarith
  · rw [Finset.erase_eq_of_notMem htwo] at h
    unfold primeHarmonicConstant
    linarith

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/PrimeNearRange.lean -/
section
/- # Reciprocal mass in the range controlled by block interaction -/

namespace Erdos12Proof

noncomputable def primeNearRangeConstant : ℝ :=
  8 * (blockPackingExponent + 16) * (1 + brunTitchmarshConstant)

theorem primeNearRangeConstant_pos : 0 < primeNearRangeConstant := by
  unfold primeNearRangeConstant
  have hC := brunTitchmarshConstant_pos
  positivity

theorem prime_near_range_bound (R Q S : Finset ℕ)
    (hR : ∀ r ∈ R, r.Prime ∧ 2 < r) (hQ : ∀ p ∈ Q, p.Prime)
    (hP : PropertyP (Q : Set ℕ))
    (horder : ∀ r ∈ R, ∀ p ∈ Q, r < p)
    (hopposite : ∀ r ∈ R, ∀ p ∈ Q, ∀ q ∈ Q, r ∣ p + q → p = q)
    (D : ℝ) (hD : roughSieveThreshold ≤ D)
    (hscale : ∀ i ∈ S, D ≤ (2 : ℝ) ^ i)
    (htwo : ∀ i ∈ S, 2 ≤ (2 : ℝ) ^ i)
    (hmodulus : ∀ i ∈ S, (primeModulus R : ℝ) ^ 2 ≤ (2 : ℝ) ^ i)
    (hrough : ∀ i ∈ S, ∀ p ∈ dyadicBin Q i, Rough D p)
    (hspan : ∀ i ∈ S, ∀ j ∈ S, i + 4 ≤ j → (2 : ℝ) ^ (j - i) ≤ D ^ roughSieveExponent) :
    (∑ i ∈ S, harmonic (dyadicBin Q i)) ≤
      primeNearRangeConstant * (1 / 2 : ℝ) ^ R.card * (1 + R.card) / Real.log D := by
  have hD0 : 0 < D := lt_of_lt_of_le roughSieveThreshold_pos hD
  have hlogD : 0 < Real.log D := by linarith [(roughSieveThreshold_log hD).1]
  let w := fun i => roughBlockDensity (dyadicBin Q i) D (2 ^ i)
  have hw : ∀ i ∈ S, 0 ≤ w i ∧ w i ≤ (1 + brunTitchmarshConstant) * (1 / 2 : ℝ) ^ R.card := by
    intro i hi
    have hX : 0 < (2 : ℝ) ^ i := by positivity
    have hlogX : 0 < Real.log ((2 : ℝ) ^ i) := Real.log_pos (by linarith [htwo i hi])
    have hlogDX := Real.log_le_log hD0 (hscale i hi)
    have hcount := prime_opposite_pair_count R (dyadicBin Q i) hR
      (fun p hp => hQ p (dyadicBin_subset Q i hp))
      (fun r hr p hp => horder r hr p (dyadicBin_subset Q i hp))
      (fun r hr p hp q hq => hopposite r hr p (dyadicBin_subset Q i hp) q (dyadicBin_subset Q i hq))
      ((2 : ℝ) ^ i) (htwo i hi) (hmodulus i hi) (by
        intro p hp
        have h := dyadicBin_interval Q i hp
        exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2.le⟩)
    have hw0 : 0 ≤ w i := by dsimp only [w, roughBlockDensity]; positivity
    refine ⟨hw0, ?_⟩
    calc
      w i = Real.log D * (dyadicBin Q i).card / (2 : ℝ) ^ i := by
        simp only [w, roughBlockDensity, Nat.cast_pow, Nat.cast_ofNat]
      _ ≤ Real.log D * (brunTitchmarshConstant * (1 / 2 : ℝ) ^ R.card * (2 : ℝ) ^ i /
          Real.log ((2 : ℝ) ^ i)) / (2 : ℝ) ^ i :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcount hlogD.le) hX.le
      _ = brunTitchmarshConstant * (1 / 2 : ℝ) ^ R.card *
          (Real.log D / Real.log ((2 : ℝ) ^ i)) := by field_simp
      _ ≤ brunTitchmarshConstant * (1 / 2 : ℝ) ^ R.card := by
        apply mul_le_of_le_one_right (mul_nonneg brunTitchmarshConstant_pos.le (by positivity))
        exact (div_le_one hlogX).mpr hlogDX
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hpair : ∀ i ∈ S, ∀ j ∈ S, i + 4 ≤ j →
      w i ^ 4 * w j ^ 8 * (2 : ℝ) ^ (j - i) ≤ (2 : ℝ) ^ blockPackingExponent := by
    intro i hi j hj hij
    exact dyadic_block_interaction Q hP D hD i j hij (hscale i hi)
      (hspan i hi j hj hij) (hrough i hi) (hrough j hj)
  have hdensity := dyadic_density_sum S w blockPackingExponent R.card (1 + brunTitchmarshConstant)
    (by linarith [brunTitchmarshConstant_pos]) hw hpair
  have hbin (i : ℕ) : harmonic (dyadicBin Q i) ≤ w i / Real.log D := by
    have hcard := harmonic_le_card_div (dyadicBin Q i) (by positivity : (0 : ℝ) < 2 ^ i)
      (fun p hp => by exact_mod_cast (dyadicBin_interval Q i hp).1)
    calc
      _ ≤ (dyadicBin Q i).card / (2 : ℝ) ^ i := hcard
      _ = _ := by
        dsimp only [w, roughBlockDensity]
        push_cast
        field_simp
  calc
    _ ≤ ∑ i ∈ S, w i / Real.log D := Finset.sum_le_sum (fun i _ => hbin i)
    _ = (∑ i ∈ S, w i) / Real.log D := (Finset.sum_div _ _ _).symm
    _ ≤ _ := by
      exact div_le_div_of_nonneg_right hdensity hlogD.le

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/PrimeNearBins.lean -/
section
/- # The block-interaction estimate at a dyadic starting scale -/

namespace Erdos12Proof

noncomputable def primeNearIndexConstant : ℝ := 2 * primeNearRangeConstant / Real.log 2

theorem primeNearIndexConstant_pos : 0 < primeNearIndexConstant :=
  div_pos (mul_pos (by norm_num) primeNearRangeConstant_pos) (Real.log_pos (by norm_num))

theorem prime_near_bins_bound (R Q S : Finset ℕ)
    (hR : ∀ r ∈ R, r.Prime ∧ 2 < r) (hQ : ∀ p ∈ Q, p.Prime)
    (hP : PropertyP (Q : Set ℕ))
    (horder : ∀ r ∈ R, ∀ p ∈ Q, r < p)
    (hopposite : ∀ r ∈ R, ∀ p ∈ Q, ∀ q ∈ Q, r ∣ p + q → p = q)
    (J B : ℕ) (hJ : 2 ≤ J) (hS : ∀ i ∈ S, J ≤ i ∧ i < B)
    (hD : roughSieveThreshold ≤ (2 : ℝ) ^ J / 2)
    (hmodulus : (primeModulus R : ℝ) ^ 2 ≤ (2 : ℝ) ^ J)
    (hspan : (2 : ℝ) ^ (B - J) ≤ ((2 : ℝ) ^ J / 2) ^ roughSieveExponent) :
    (∑ i ∈ S, harmonic (dyadicBin Q i)) ≤
      primeNearIndexConstant * (1 / 2 : ℝ) ^ R.card * (1 + R.card) / J := by
  let D : ℝ := (2 : ℝ) ^ J / 2
  have hscale (i : ℕ) (hi : i ∈ S) : (2 : ℝ) ^ J ≤ (2 : ℝ) ^ i :=
    pow_le_pow_right₀ (by norm_num) (hS i hi).1
  have hDi (i : ℕ) (hi : i ∈ S) : D ≤ (2 : ℝ) ^ i :=
    (div_le_self (by positivity) (by norm_num)).trans (hscale i hi)
  have htwo (i : ℕ) (hi : i ∈ S) : (2 : ℝ) ≤ (2 : ℝ) ^ i := by
    have hi1 : 1 ≤ i := by have := (hS i hi).1; omega
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hi1
  have hrough (i : ℕ) (hi : i ∈ S) (p : ℕ) (hp : p ∈ dyadicBin Q i) : Rough D p := by
    apply prime_rough_of_lt (hQ p (dyadicBin_subset Q i hp))
    have hpLo : (2 : ℝ) ^ i ≤ p := by exact_mod_cast (dyadicBin_interval Q i hp).1
    have hDlt : D < (2 : ℝ) ^ J := by dsimp only [D]; nlinarith [show (0 : ℝ) < 2 ^ J by positivity]
    exact hDlt.trans_le ((hscale i hi).trans hpLo)
  have hrange (i : ℕ) (hi : i ∈ S) (j : ℕ) (hj : j ∈ S) (_hij : i + 4 ≤ j) :
      (2 : ℝ) ^ (j - i) ≤ D ^ roughSieveExponent := by
    have hgap : j - i ≤ B - J := by have := hS i hi; have := hS j hj; omega
    exact (pow_le_pow_right₀ (by norm_num) hgap).trans hspan
  have h := prime_near_range_bound R Q S hR hQ hP horder hopposite D hD hDi htwo
    (fun i hi => hmodulus.trans (hscale i hi)) hrough hrange
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hJR : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hlog : Real.log D = ((J : ℝ) - 1) * Real.log 2 := by
    dsimp only [D]
    rw [Real.log_div (by positivity) (by norm_num), Real.log_pow]
    ring
  have hden : ((J : ℝ) / 2) * Real.log 2 ≤ Real.log D := by
    rw [hlog]
    have hJ2 : (2 : ℝ) ≤ J := by exact_mod_cast hJ
    nlinarith
  have hsmall : 0 < ((J : ℝ) / 2) * Real.log 2 := mul_pos (by positivity) hl2
  have hnum : 0 ≤ primeNearRangeConstant * (1 / 2 : ℝ) ^ R.card * (1 + R.card) := by
    have hC := primeNearRangeConstant_pos
    positivity
  calc
    _ ≤ primeNearRangeConstant * (1 / 2 : ℝ) ^ R.card * (1 + R.card) / Real.log D := h
    _ ≤ primeNearRangeConstant * (1 / 2 : ℝ) ^ R.card * (1 + R.card) /
        (((J : ℝ) / 2) * Real.log 2) := div_le_div_of_nonneg_left hnum hsmall hden
    _ = _ := by unfold primeNearIndexConstant; field_simp

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/PrimeTailParameters.lean -/
section
/- # Uniform scale parameters for the prime-tail estimate -/

open Filter
open scoped Topology

namespace Erdos12Proof

def primeTailSelectionSize (J : ℕ) : ℕ := 8 * Nat.clog 2 J

def primeTailNearEnd (k J : ℕ) : ℕ := J + 8 * k + 8 * Nat.clog 2 J + 1

theorem natural_clog_real_bound {J : ℕ} (hJ : 1 ≤ J) :
    (Nat.clog 2 J : ℝ) ≤ Real.log J / Real.log 2 + 1 := by
  rw [← Real.natCeil_logb_natCast]
  have hnonneg : 0 ≤ Real.logb 2 (J : ℝ) := Real.logb_nonneg (by norm_num) (by exact_mod_cast hJ)
  exact (Nat.ceil_lt_add_one hnonneg).le

theorem eventual_clog_linear {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ J : ℕ in atTop, (Nat.clog 2 J : ℝ) ≤ ε * J := by
  have hlog : Tendsto (fun J : ℕ => Real.log J / (J : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, pow_one, one_mul, add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
        tendsto_natCast_atTop_atTop
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have heps : 0 < ε * Real.log 2 / 2 := by positivity
  have hsmall := hlog.eventually_lt_const heps
  have hlarge : ∀ᶠ J : ℕ in atTop, (2 / ε : ℝ) ≤ J :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [hsmall, hlarge, eventually_ge_atTop (1 : ℕ)] with J hJlog hJlarge hJ1
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hlogbound : Real.log J ≤ (ε * Real.log 2 / 2) * J :=
    ((div_lt_iff₀ hJ0).mp hJlog).le
  have hunit : 1 ≤ ε * J / 2 := by
    have h := (div_le_iff₀ hε).mp hJlarge
    nlinarith
  have hclog := natural_clog_real_bound hJ1
  have hdiv : Real.log J / Real.log 2 ≤ ε * J / 2 := by
    apply (div_le_iff₀ hl2).mpr
    nlinarith
  linarith

theorem eventual_polynomial_dyadic_growth :
    ∀ᶠ J : ℕ in atTop, 9 * (J : ℝ) ^ 5 ≤ (2 : ℝ) ^ ((J : ℝ) / 2) := by
  have hb : 0 < Real.log (2 : ℝ) / 2 := by positivity
  have hsmall := (isLittleO_pow_exp_pos_mul_atTop 5 hb).bound
    (by norm_num : (0 : ℝ) < 1 / 9)
  have hnat := tendsto_natCast_atTop_atTop.eventually hsmall
  filter_upwards [hnat] with J hJ
  have heq : Real.exp (Real.log 2 / 2 * (J : ℝ)) = (2 : ℝ) ^ ((J : ℝ) / 2) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    congr 1
    ring
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (J : ℝ) ^ 5),
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), heq] at hJ
  linarith

theorem dyadic_guard_density_growth {k J : ℕ} (h : 4 * k ≤ J) :
    (2 : ℝ) ^ ((J : ℝ) / 2) ≤ ((1 / 2 : ℝ) ^ k) ^ 2 * (2 : ℝ) ^ J := by
  have h2 : 2 * k ≤ J := by omega
  have hid : ((1 / 2 : ℝ) ^ k) ^ 2 * (2 : ℝ) ^ J = (2 : ℝ) ^ (J - 2 * k) := by
    have hJpow : (2 : ℝ) ^ J = (2 : ℝ) ^ (2 * k) * (2 : ℝ) ^ (J - 2 * k) := by
      rw [← pow_add, Nat.add_sub_of_le h2]
    rw [hJpow, Nat.mul_comm 2 k, pow_mul, one_div_pow]
    field_simp
  rw [hid, ← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  rw [Nat.cast_sub h2]
  have hR : 4 * (k : ℝ) ≤ J := by exact_mod_cast h
  push_cast
  linarith

theorem selection_polynomial_budget_eventually :
    ∀ᶠ J : ℕ in atTop, ∀ k : ℕ, 4 * k ≤ J →
      (primeTailSelectionSize J + 1 : ℝ) * (J : ℝ) ^ 4 ≤
        ((1 / 2 : ℝ) ^ k) ^ 2 * (2 : ℝ) ^ J := by
  filter_upwards [eventual_clog_linear (ε := 1) (by norm_num),
    eventual_polynomial_dyadic_growth, eventually_ge_atTop (1 : ℕ)] with J hclog hgrowth hJ
  intro k hk
  have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hsize : (primeTailSelectionSize J + 1 : ℝ) ≤ 9 * J := by
    dsimp only [primeTailSelectionSize]
    push_cast
    linarith
  calc
    _ ≤ 9 * (J : ℝ) ^ 5 := by nlinarith [mul_le_mul_of_nonneg_right hsize (by positivity : 0 ≤ (J : ℝ) ^ 4)]
    _ ≤ (2 : ℝ) ^ ((J : ℝ) / 2) := hgrowth
    _ ≤ _ := dyadic_guard_density_growth hk

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/PrimeTailNumerics.lean -/
section
/- # Numerical budgets for selecting moduli and summing the middle range -/

namespace Erdos12Proof

theorem clog_dyadic_reciprocal (J : ℕ) : (J : ℝ) * (1 / 2 : ℝ) ^ Nat.clog 2 J ≤ 1 := by
  have h : (J : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 J := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) J
  rw [one_div_pow, mul_one_div]
  exact (div_le_one (by positivity)).mpr h

theorem selection_dyadic_reciprocal (J : ℕ) :
    (J : ℝ) * (1 / 2 : ℝ) ^ primeTailSelectionSize J ≤ 1 := by
  have hpower : (2 : ℝ) ^ Nat.clog 2 J ≤ (2 : ℝ) ^ primeTailSelectionSize J := by
    apply pow_le_pow_right₀ (by norm_num)
    dsimp only [primeTailSelectionSize]
    omega
  have h := one_div_le_one_div_of_le (by positivity) hpower
  rw [← one_div_pow, ← one_div_pow] at h
  exact (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg J)).trans (clog_dyadic_reciprocal J)

theorem near_end_dyadic_budget (k J : ℕ) :
    (2 : ℝ) ^ J * (1 / 2 : ℝ) ^ primeTailNearEnd k J * (J : ℝ) ^ 4 ≤
      ((1 / 2 : ℝ) ^ k) ^ 2 := by
  let q : ℝ := 1 / 2
  let B := primeTailNearEnd k J
  have hJB : J ≤ B := by dsimp only [B, primeTailNearEnd]; omega
  have hspan : 2 * k + 4 * Nat.clog 2 J ≤ B - J := by
    dsimp only [B, primeTailNearEnd]
    omega
  have hpowB : (2 : ℝ) ^ B = (2 : ℝ) ^ J * (2 : ℝ) ^ (B - J) := by
    rw [← pow_add, Nat.add_sub_of_le hJB]
  have heq : (2 : ℝ) ^ J * q ^ B = 1 / (2 : ℝ) ^ (B - J) := by
    dsimp only [q]
    rw [one_div_pow, hpowB]
    field_simp
  have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hspan
  have hinv := one_div_le_one_div_of_le (by positivity) hpow
  have hid : 1 / (2 : ℝ) ^ (2 * k + 4 * Nat.clog 2 J) =
      (q ^ k) ^ 2 * (q ^ Nat.clog 2 J) ^ 4 := by
    dsimp only [q]
    rw [pow_add, pow_mul, pow_mul, one_div_pow, one_div_pow, one_div_pow]
    field_simp
    simp only [← pow_mul, Nat.mul_comm]
  have hclog := clog_dyadic_reciprocal J
  have hclogpow : ((J : ℝ) * q ^ Nat.clog 2 J) ^ 4 ≤ 1 := by
    exact (pow_le_pow_left₀ (by positivity) hclog 4).trans_eq (by norm_num)
  calc
    _ = (1 / (2 : ℝ) ^ (B - J)) * (J : ℝ) ^ 4 := by rw [heq]
    _ ≤ (1 / (2 : ℝ) ^ (2 * k + 4 * Nat.clog 2 J)) * (J : ℝ) ^ 4 :=
      mul_le_mul_of_nonneg_right hinv (by positivity)
    _ = (q ^ k) ^ 2 * ((J : ℝ) * q ^ Nat.clog 2 J) ^ 4 := by rw [hid]; ring
    _ ≤ (q ^ k) ^ 2 := by
      exact (mul_le_mul_of_nonneg_left hclogpow (by positivity)).trans_eq (mul_one _)

theorem heavy_bin_budget {k J : ℕ} (hJ : 1 ≤ J) {n : ℝ}
    (hheavy : (1 / 2 : ℝ) ^ k * (2 : ℝ) ^ J / (J : ℝ) ^ 2 ≤ n)
    (hbudget : (primeTailSelectionSize J + 1 : ℝ) * (J : ℝ) ^ 4 ≤
      ((1 / 2 : ℝ) ^ k) ^ 2 * (2 : ℝ) ^ J) :
    (primeTailSelectionSize J + 1 : ℝ) * (J : ℝ) ^ 2 ≤ (1 / 2 : ℝ) ^ k * n := by
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hheavy' := (div_le_iff₀ (sq_pos_of_pos hJ0)).mp hheavy
  have hscaled := mul_le_mul_of_nonneg_left hheavy' (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k)
  apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hJ0)).mp
  nlinarith

theorem middle_range_numerical_bound {k J : ℕ} (hJ : 1 ≤ J) {n H : ℝ} (hn : 0 < n)
    (hH : H ≤ 2 * (primeTailSelectionSize J + 1 : ℝ) * ((J : ℝ) + 1))
    (hheavy : (1 / 2 : ℝ) ^ k * (2 : ℝ) ^ J / (J : ℝ) ^ 2 ≤ n)
    (hbudget : (primeTailSelectionSize J + 1 : ℝ) * (J : ℝ) ^ 4 ≤
      ((1 / 2 : ℝ) ^ k) ^ 2 * (2 : ℝ) ^ J) :
    2 * H / n + (160 * (J : ℝ) * ((2 : ℝ) ^ J) ^ 2 / n) *
      (1 / 2 : ℝ) ^ primeTailNearEnd k J ≤ 168 * (1 / 2 : ℝ) ^ k / J := by
  have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hJ0 : (0 : ℝ) < J := by linarith
  have hb := heavy_bin_budget hJ hheavy hbudget
  have hH' : H * J ≤ 4 * ((1 / 2 : ℝ) ^ k * n) := by
    have hs0 : (0 : ℝ) ≤ primeTailSelectionSize J + 1 := by positivity
    have hlinear : H ≤ 4 * (primeTailSelectionSize J + 1 : ℝ) * J := by
      have hprod := mul_nonneg hs0 (sub_nonneg.mpr hJ1)
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hlinear hJ0.le]
  have hdecay := near_end_dyadic_budget k J
  have hheavy' := (div_le_iff₀ (sq_pos_of_pos hJ0)).mp hheavy
  have hs1 := mul_le_mul_of_nonneg_right hdecay (by positivity : (0 : ℝ) ≤ 2 ^ J)
  have hs2 := mul_le_mul_of_nonneg_left hheavy' (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k)
  have hmiddle : (J : ℝ) ^ 2 * ((2 : ℝ) ^ J) ^ 2 *
      (1 / 2 : ℝ) ^ primeTailNearEnd k J ≤ (1 / 2 : ℝ) ^ k * n := by
    apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hJ0)).mp
    nlinarith
  apply (le_div_iff₀ hJ0).mpr
  apply (mul_le_mul_iff_of_pos_right hn).mp
  field_simp
  nlinarith

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/PrimeFarTail.lean -/
section
/- # The far prime tail after inserting selected internal moduli -/

namespace Erdos12Proof

theorem primeModulus_mem_le (R : Finset ℕ) (hR : ∀ r ∈ R, r.Prime)
    {r : ℕ} (hr : r ∈ R) : r ≤ primeModulus R :=
  Nat.le_of_dvd (primeModulus_pos R hR) (Finset.dvd_prod_of_mem (fun p : ℕ => p) hr)

theorem primeModulus_square_order (R : Finset ℕ) (hR : ∀ r ∈ R, r.Prime ∧ 2 < r)
    {r p : ℕ} (hr : r ∈ R) (hp : primeModulus R ^ 2 ≤ p) : r < p := by
  have hle := primeModulus_mem_le R (fun r hr => (hR r hr).1) hr
  have hr2 := (hR r hr).2
  nlinarith

theorem prime_square_tail_bound (R Q : Finset ℕ)
    (hR : ∀ r ∈ R, r.Prime ∧ 2 < r)
    (hQ : ∀ p ∈ Q, p.Prime ∧ 2 < p) (hP : PropertyP (Q : Set ℕ))
    (hopposite : ∀ r ∈ R, ∀ p ∈ Q, ∀ q ∈ Q, r ∣ p + q → p = q)
    (hthreshold : ∀ p ∈ Q, primeModulus R ^ 2 ≤ p) :
    harmonic Q ≤ 2 * primeHarmonicWindowConstant * (1 / 2 : ℝ) ^ R.card :=
  prime_guarded_harmonic_bound R Q hR hQ hP
    (fun _ hr _ hp => primeModulus_square_order R hR hr (hthreshold _ hp)) hopposite hthreshold

theorem prime_selected_tail_bound (R Q E : Finset ℕ)
    (hR : ∀ r ∈ R, r.Prime ∧ 2 < r)
    (hQ : ∀ p ∈ Q, p.Prime ∧ 2 < p) (hP : PropertyP (Q : Set ℕ))
    (hE : E ⊆ Q) (hdisjoint : Disjoint R E)
    (hopposite : ∀ r ∈ R, ∀ p ∈ Q, ∀ q ∈ Q, r ∣ p + q → p = q) :
    harmonic (Q.filter (fun p => primeModulus (R ∪ E) ^ 2 ≤ p)) ≤
      2 * primeHarmonicWindowConstant * (1 / 2 : ℝ) ^ R.card * (1 / 2 : ℝ) ^ E.card := by
  classical
  let T := Q.filter (fun p => primeModulus (R ∪ E) ^ 2 ≤ p)
  have hRE : ∀ r ∈ R ∪ E, r.Prime ∧ 2 < r := by
    intro r hr
    rcases Finset.mem_union.mp hr with hr | hr
    · exact hR r hr
    · exact hQ r (hE hr)
  have hT : T ⊆ Q := Finset.filter_subset _ _
  have h := prime_square_tail_bound (R ∪ E) T hRE (fun p hp => hQ p (hT hp)) (hP.mono hT) (by
    intro r hr p hp q hq hdiv
    rcases Finset.mem_union.mp hr with hr | hr
    · exact hopposite r hr p (hT hp) q (hT hq) hdiv
    · exact hP (hE hr) (hT hp) (hT hq) hdiv
        (primeModulus_square_order (R ∪ E) hRE (Finset.mem_union_right R hr) (Finset.mem_filter.mp hp).2)
        (primeModulus_square_order (R ∪ E) hRE (Finset.mem_union_right R hr) (Finset.mem_filter.mp hq).2))
    (fun _ hp => (Finset.mem_filter.mp hp).2)
  rw [Finset.card_union_of_disjoint hdisjoint, pow_add] at h
  simpa only [mul_assoc] using h

theorem two_pow_card_le_primeModulus (R : Finset ℕ) (hR : ∀ p ∈ R, p.Prime) :
    2 ^ R.card ≤ primeModulus R := by
  calc
    _ = ∏ _p ∈ R, (2 : ℕ) := by simp
    _ ≤ primeModulus R := Finset.prod_le_prod (fun p hp => (hR p hp).two_le)

theorem prime_guard_count_bound (R : Finset ℕ) (hR : ∀ p ∈ R, p.Prime) (A J : ℕ)
    (hbound : primeModulus R ^ A ≤ 2 ^ J) : R.card * A ≤ J := by
  have hpow := Nat.pow_le_pow_left (two_pow_card_le_primeModulus R hR) A
  rw [← pow_mul] at hpow
  exact (pow_le_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).mp (hpow.trans hbound)

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/SelectedPrimeProducts.lean -/
section
/- # Products of selected prime moduli in one dyadic interval -/

namespace Erdos12Proof

theorem primeModulus_union (R E : Finset ℕ) (hRE : Disjoint R E) :
    primeModulus (R ∪ E) = primeModulus R * primeModulus E := by
  exact Finset.prod_union hRE

theorem selected_modulus_dyadic_bound (R E : Finset ℕ) (hRE : Disjoint R E) (J : ℕ)
    (hR : primeModulus R ≤ 2 ^ J) (hE : ∀ p ∈ E, p ≤ 2 ^ (J + 1)) :
    primeModulus (R ∪ E) ≤ 2 ^ ((E.card + 1) * (J + 1)) := by
  have hEprod : primeModulus E ≤ (2 ^ (J + 1)) ^ E.card := by
    calc
      _ ≤ ∏ _p ∈ E, (2 ^ (J + 1) : ℕ) := Finset.prod_le_prod hE
      _ = _ := by simp
  rw [primeModulus_union R E hRE]
  calc
    _ ≤ 2 ^ J * (2 ^ (J + 1)) ^ E.card := Nat.mul_le_mul hR hEprod
    _ ≤ 2 ^ (J + 1) * (2 ^ (J + 1)) ^ E.card := Nat.mul_le_mul_right _
      (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (Nat.le_succ J))
    _ = _ := by rw [← pow_succ', ← pow_mul, Nat.mul_comm (J + 1)]

theorem prime_modulus_le_of_power_bound (R : Finset ℕ) (hR : ∀ r ∈ R, r.Prime)
    {A J : ℕ} (hA : 1 ≤ A) (hbound : primeModulus R ^ A ≤ 2 ^ J) :
    primeModulus R ≤ 2 ^ J := by
  have hM : 1 ≤ primeModulus R := primeModulus_pos R hR
  have h := Nat.pow_le_pow_right hM hA
  simpa only [pow_one] using h.trans hbound

theorem external_selected_disjoint (R Q E : Finset ℕ) (hE : E ⊆ Q)
    (horder : ∀ r ∈ R, ∀ p ∈ Q, r < p) : Disjoint R E := by
  apply Finset.disjoint_left.mpr
  intro p hpR hpE
  exact (Nat.lt_irrefl p) (horder p hpR p (hE hpE))

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/PrimeLightBins.lean -/
section
/- # Reciprocal mass of light dyadic bins -/

namespace Erdos12Proof

theorem reciprocal_square_le_telescoping {n : ℕ} (hn : 0 < n) :
    1 / (n : ℝ) ^ 2 ≤ 2 * (1 / (n : ℝ) - 1 / (n + 1 : ℕ)) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  nlinarith

theorem finite_reciprocal_square_tail (S : Finset ℕ) {J : ℕ} (hJ : 0 < J)
    (hS : ∀ j ∈ S, J ≤ j) : (∑ j ∈ S, 1 / (j : ℝ) ^ 2) ≤ 2 / (J : ℝ) := by
  classical
  let N := J + S.sup id + 1
  have hJN : J ≤ N := by dsimp only [N]; omega
  have hsub : S ⊆ Finset.Ico J N := by
    intro j hj
    have hsup : j ≤ S.sup id := Finset.le_sup (f := id) hj
    exact Finset.mem_Ico.mpr ⟨hS j hj, by dsimp only [N]; omega⟩
  have htel : (∑ j ∈ Finset.Ico J N, (1 / (j : ℝ) - 1 / (j + 1 : ℕ))) =
      1 / (J : ℝ) - 1 / (N : ℝ) := by
    rw [Finset.sum_Ico_eq_sub _ hJN, Finset.sum_range_sub', Finset.sum_range_sub']
    ring
  calc
    _ ≤ ∑ j ∈ Finset.Ico J N, 1 / (j : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => by positivity)
    _ ≤ ∑ j ∈ Finset.Ico J N, 2 * (1 / (j : ℝ) - 1 / (j + 1 : ℕ)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact reciprocal_square_le_telescoping (hJ.trans_le (Finset.mem_Ico.mp hj).1)
    _ = 2 * (1 / (J : ℝ) - 1 / (N : ℝ)) := by rw [← Finset.mul_sum, htel]
    _ ≤ 2 * (1 / (J : ℝ)) := by
      have hN : (0 : ℝ) ≤ 1 / N := by positivity
      linarith
    _ = _ := by ring

theorem light_dyadic_bins_bound (Q S : Finset ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    {J : ℕ} (hJ : 0 < J) (hS : ∀ j ∈ S, J ≤ j)
    (hlight : ∀ j ∈ S, ((dyadicBin Q j).card : ℝ) ≤ δ * (2 : ℝ) ^ j / (j : ℝ) ^ 2) :
    (∑ j ∈ S, harmonic (dyadicBin Q j)) ≤ 2 * δ / J := by
  have hbin (j : ℕ) (hj : j ∈ S) : harmonic (dyadicBin Q j) ≤ δ / (j : ℝ) ^ 2 := by
    have hpow : (0 : ℝ) < 2 ^ j := by positivity
    calc
      _ ≤ (dyadicBin Q j).card / (2 : ℝ) ^ j := harmonic_le_card_div _ hpow
        (fun p hp => by exact_mod_cast (dyadicBin_interval Q j hp).1)
      _ ≤ (δ * (2 : ℝ) ^ j / (j : ℝ) ^ 2) / (2 : ℝ) ^ j :=
        div_le_div_of_nonneg_right (hlight j hj) hpow.le
      _ = _ := by field_simp
  calc
    _ ≤ ∑ j ∈ S, δ / (j : ℝ) ^ 2 := Finset.sum_le_sum (fun j hj => hbin j hj)
    _ = δ * ∑ j ∈ S, 1 / (j : ℝ) ^ 2 := by rw [Finset.mul_sum]; simp only [mul_one_div]
    _ ≤ δ * (2 / J) := mul_le_mul_of_nonneg_left (finite_reciprocal_square_tail S hJ hS) hδ
    _ = _ := by ring

end Erdos12Proof
end

/- BEGIN SOURCE: AnalyticNumberTheory/LargeSieve/Additive.lean -/
section
/- # AnalyticNumberTheory.LargeSieve.Additive

## Additive large sieve (Montgomery 1971)

For a `δ`-well-spaced set of points `{x_r}` modulo 1 and any finitely supported
complex sequence `a_n`,

  Σ_r |Σ_{M<n≤M+N} a_n e(n x_r)|² ≤ (N + 1/δ) · Σ_{M<n≤M+N} |a_n|²,

where `e(x) = exp(2πix)`. This is a basic analytic input to the
Bombieri--Vinogradov theorem and the weighted Pan mean-value theorem
(`PanMeanValueUniform`); the multiplicative and arithmetic large sieves are
consequences of it.

This module has three parts:

1. **Representation**: the standard additive character
   `unitChar x = exp(2πix)` on `AddCircle 1` (mathlib's `AddCircle.toCircle`),
   the interval exponential sum `circleCharSum`, and `wellSpaced`
   (`δ`-separation in the distance modulo 1).
2. **Target statements**: `MontgomeryLargeSievePrimal` and
   `MontgomeryLargeSieveDual` are quantified propositions. This module defines
   these targets rather than proving either large-sieve bound.
3. **Duality lemma**: for any finite matrix `A` and constant `C ≥ 0`, the
   primal bound (for every `a`) is equivalent to the dual bound (for every `b`)
   (`largeSieveDuality`). This is the algebraic foundation of the large-sieve
   argument: Montgomery's original proof starts with the dual form
   (geometric-sum bounds and the Schur test), and duality preserves the constant.
   The dual form uses the conjugate transpose (`star (A i j)`); the classical
   `e(nx)` formulation follows equivalently by conjugating `b` and reversing
   the sign of `n`.

References:
  - Montgomery, H.L. (1971), "Topics in Multiplicative Number Theory"
  - Iwaniec & Kowalski, "Analytic Number Theory" (2004), Ch. 7
  - Halberstam & Richert, "Sieve Methods" (1974), Ch. 9-10
-/

namespace AnalyticNumberTheory.LargeSieve

open scoped BigOperators

noncomputable section

/- ## 1. Additive characters and exponential sums on the circle modulo 1 -/


/- ## 2. Additive large-sieve target statements -/


/- ## 3. Duality lemma (the algebraic foundation of the large sieve) -/


/-- **Complex Cauchy--Schwarz** (Finset):
`|Σᵢ xᵢ·conj(yᵢ)| ≤ √(Σ‖xᵢ‖²)·√(Σ‖yᵢ‖²)`, proved using the triangle
inequality and real Cauchy--Schwarz. -/
theorem complexCauchySchwarz {ι : Type*} (s : Finset ι) (x y : ι → ℂ) :
    ‖∑ i ∈ s, x i * star (y i)‖ ≤
      Real.sqrt (∑ i ∈ s, ‖x i‖ ^ 2) * Real.sqrt (∑ i ∈ s, ‖y i‖ ^ 2) := by
  calc
    ‖∑ i ∈ s, x i * star (y i)‖ ≤ ∑ i ∈ s, ‖x i * star (y i)‖ :=
      norm_sum_le s _
    _ = ∑ i ∈ s, ‖x i‖ * ‖y i‖ := by simp only [norm_mul, norm_star]
    _ ≤ Real.sqrt (∑ i ∈ s, ‖x i‖ ^ 2) * Real.sqrt (∑ i ∈ s, ‖y i‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt s (fun i => ‖x i‖) (fun i => ‖y i‖)

/-- **Large-sieve duality lemma** (finite matrices): for any `A : ι → κ → ℂ`
and `C ≥ 0`, the primal bound
`Σᵢ |Σⱼ Aᵢⱼ aⱼ|² ≤ C·Σⱼ |aⱼ|² (∀a)` is equivalent to the
conjugate-transpose dual bound
`Σⱼ |Σᵢ conj(Aᵢⱼ) bᵢ|² ≤ C·Σᵢ |bᵢ|² (∀b)`.

Proof (Montgomery's classical argument): put `v = A*b` (`bStar`). Then
`‖A*b‖² = |⟨b, A A*b⟩| ≤ ‖A A*b‖·‖b‖ ≤ √C·‖A*b‖·‖b‖`.
The primal bound applied to `v` and complex Cauchy--Schwarz give
`‖A*b‖ ≤ √C·‖b‖`. The converse follows symmetrically from `A** = A`
(`star (star A) = A`). -/
theorem largeSieveDuality_primalToDual {ι κ : Type*}
    (s : Finset ι) (t : Finset κ) (A : ι → κ → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hPrimal : ∀ a : κ → ℂ,
      ∑ i ∈ s, ‖∑ j ∈ t, A i j * a j‖ ^ 2 ≤ C * ∑ j ∈ t, ‖a j‖ ^ 2) :
    ∀ b : ι → ℂ,
      ∑ j ∈ t, ‖∑ i ∈ s, star (A i j) * b i‖ ^ 2 ≤ C * ∑ i ∈ s, ‖b i‖ ^ 2 := by
  intro b
  let bStar : κ → ℂ := fun j => ∑ i ∈ s, star (A i j) * b i
  let AAb : ι → ℂ := fun i => ∑ j ∈ t, A i j * bStar j
  have hsquare : (∑ j ∈ t, ‖bStar j‖ ^ 2) =
      ‖∑ i ∈ s, b i * star (AAb i)‖ := by
    have hnonneg : 0 ≤ (∑ j ∈ t, ‖bStar j‖ ^ 2 : ℝ) :=
      Finset.sum_nonneg (fun j hj => sq_nonneg _)
    symm
    calc
      ‖∑ i ∈ s, b i * star (AAb i)‖
          = ‖∑ i ∈ s, ∑ j ∈ t, b i * star (A i j) * star (bStar j)‖ := by
            congr 1
            apply Finset.sum_congr rfl
            intro i hi
            calc
              b i * star (∑ j ∈ t, A i j * bStar j)
                  = b i * (∑ j ∈ t, star (A i j) * star (bStar j)) := by
                    congr 1
                    exact (map_sum (starRingEnd ℂ) (fun j => A i j * bStar j) t).trans
                      (Finset.sum_congr rfl (fun j hj =>
                        map_mul (starRingEnd ℂ) (A i j) (bStar j)))
              _ = ∑ j ∈ t, b i * (star (A i j) * star (bStar j)) := by
                    rw [Finset.mul_sum]
              _ = ∑ j ∈ t, b i * star (A i j) * star (bStar j) := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    rw [← mul_assoc]
      _ = ‖∑ j ∈ t, ∑ i ∈ s, b i * star (A i j) * star (bStar j)‖ := by
            congr 1
            rw [Finset.sum_comm]
      _ = ‖∑ j ∈ t, (∑ i ∈ s, b i * star (A i j)) * star (bStar j)‖ := by
            congr 1
            apply Finset.sum_congr rfl
            intro j hj
            rw [← Finset.sum_mul]
      _ = ‖∑ j ∈ t, (∑ i ∈ s, star (A i j) * b i) * star (bStar j)‖ := by
            congr 1
            apply Finset.sum_congr rfl
            intro j hj
            simp [mul_comm]
      _ = ‖∑ j ∈ t, bStar j * star (bStar j)‖ := rfl
      _ = ‖((∑ j ∈ t, ‖bStar j‖ ^ 2 : ℝ) : ℂ)‖ := by
            congr 1
            rw [Complex.ofReal_sum]
            apply Finset.sum_congr rfl
            intro j hj
            exact (Complex.mul_conj (bStar j)).trans (by rw [Complex.normSq_eq_norm_sq])
      _ = ∑ j ∈ t, ‖bStar j‖ ^ 2 := by
            rw [Complex.norm_real, Real.norm_of_nonneg hnonneg]
  have hcs : ‖∑ i ∈ s, b i * star (AAb i)‖ ≤
      Real.sqrt (∑ i ∈ s, ‖b i‖ ^ 2) * Real.sqrt (∑ i ∈ s, ‖AAb i‖ ^ 2) := by
    exact complexCauchySchwarz s b AAb
  have hnorm : (∑ i ∈ s, ‖AAb i‖ ^ 2) ≤ C * ∑ j ∈ t, ‖bStar j‖ ^ 2 := by
    simpa [AAb] using hPrimal bStar
  have hchain : (∑ j ∈ t, ‖bStar j‖ ^ 2) ≤
      Real.sqrt (∑ i ∈ s, ‖b i‖ ^ 2) * Real.sqrt (C * ∑ j ∈ t, ‖bStar j‖ ^ 2) := by
    calc
      (∑ j ∈ t, ‖bStar j‖ ^ 2) = ‖∑ i ∈ s, b i * star (AAb i)‖ := hsquare
      _ ≤
          Real.sqrt (∑ i ∈ s, ‖b i‖ ^ 2) * Real.sqrt (∑ i ∈ s, ‖AAb i‖ ^ 2) := hcs
      _ ≤ Real.sqrt (∑ i ∈ s, ‖b i‖ ^ 2) * Real.sqrt (C * ∑ j ∈ t, ‖bStar j‖ ^ 2) := by
            apply mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
            exact Real.sqrt_le_sqrt hnorm
  by_cases hD0 : (∑ j ∈ t, ‖bStar j‖ ^ 2) = 0
  · rw [hD0]
    exact mul_nonneg hC (Finset.sum_nonneg (fun i hi => sq_nonneg _))
  · have hDpos : 0 < (∑ j ∈ t, ‖bStar j‖ ^ 2) :=
      lt_of_le_of_ne (Finset.sum_nonneg (fun j hj => sq_nonneg _)) (Ne.symm hD0)
    have hS : 0 ≤ ∑ i ∈ s, ‖b i‖ ^ 2 := Finset.sum_nonneg (fun i hi => sq_nonneg _)
    have hCD : 0 ≤ C * ∑ j ∈ t, ‖bStar j‖ ^ 2 :=
      mul_nonneg hC (Finset.sum_nonneg (fun j hj => sq_nonneg _))
    -- Square the nonnegative norm bound and cancel the positive dual energy.
    have hsq2 := pow_le_pow_left₀ hDpos.le hchain 2
    rw [mul_pow, Real.sq_sqrt hS, Real.sq_sqrt hCD] at hsq2
    nlinarith

/-- **Large-sieve duality lemma**: equivalence of the primal and dual forms.
For the converse, replace `A` by its conjugate transpose and use
`star (star x) = x` to recover the primal form. -/
theorem largeSieveDuality {ι κ : Type*}
    (s : Finset ι) (t : Finset κ) (A : ι → κ → ℂ) {C : ℝ} (hC : 0 ≤ C) :
    (∀ a : κ → ℂ, ∑ i ∈ s, ‖∑ j ∈ t, A i j * a j‖ ^ 2 ≤ C * ∑ j ∈ t, ‖a j‖ ^ 2) ↔
      (∀ b : ι → ℂ, ∑ j ∈ t, ‖∑ i ∈ s, star (A i j) * b i‖ ^ 2 ≤ C * ∑ i ∈ s, ‖b i‖ ^ 2) := by
  constructor
  · exact largeSieveDuality_primalToDual s t A hC
  · intro hDual a
    have hPrim := largeSieveDuality_primalToDual (s := t) (t := s)
      (A := fun j i => star (A i j)) hC hDual
    simpa [star_star] using hPrim a


end

end AnalyticNumberTheory.LargeSieve
end

/- BEGIN SOURCE: AnalyticNumberTheory/LargeSieve/Duality.lean -/
section
/- # AnalyticNumberTheory.LargeSieve.Duality

## Dual quadratic-form identity

The central Parseval/tensor-product step in Montgomery's additive large-sieve
proof expands the square sum of `T(n) = Σ_{x∈X} star(e(nx))·b_x`
into a quadratic form with coefficients `b_x·star(b_y)` and kernel
`Σ_n star(e(n(x−y)))`:

  Σ_n |T(n)|² = Σ_x Σ_y b_x·star(b_y)·Σ_n star(e(n(x−y))).

The module proves three levels of this identity:

1. **Finite-matrix expansion** (`dualExpansion`): a purely algebraic identity
   for arbitrary `φ : ι → κ → ℂ` and `b : κ → ℂ`, with no character hypotheses.
2. **Real additive-character version** (`dualQuadraticIdentity`): take
   `φ n x = e(nx)` and use
   `star(e(nx))·e(ny) = star(e(n(x−y)))` to reduce the kernel to
   `Σ_n star(e(n(x−y)))`.
3. **Shifted-interval version** (`dualQuadraticIdentity_Icc`) for
   `n ∈ (M, M+N]`, and **circle version** (`dualQuadraticIdentity_circle`)
   for `charPow n x = e(nx)` on `AddCircle 1`, matching
   `MontgomeryLargeSieveDual`.

The subsequent geometric-sum and Schur-test argument estimates the off-diagonal
kernel entries by `min(N, 1/(2·dist x y))`. These are the kernel estimates used
in the dual large-sieve argument; this module supplies
the identities, not the sharp Montgomery bound.

References: Montgomery, "Topics in Multiplicative Number Theory" (1971), Ch. 1;
Iwaniec & Kowalski, "Analytic Number Theory" (2004), Ch. 7.
-/

namespace AnalyticNumberTheory.LargeSieve

open scoped BigOperators

noncomputable section

/- ## 1. Finite-matrix expansion -/

/-- Expansion of `|Σ_x c_x|²` as `Σ_x Σ_y c_x·star(c_y)`. -/
theorem normSq_sum_eq_sum_mul_star {ι : Type*} (s : Finset ι) (c : ι → ℂ) :
    (‖∑ x ∈ s, c x‖ : ℂ) ^ 2 = ∑ x ∈ s, ∑ y ∈ s, c x * star (c y) := by
  have hcast : (‖∑ x ∈ s, c x‖ : ℂ) ^ 2 = ((‖∑ x ∈ s, c x‖ ^ 2 : ℝ) : ℂ) :=
    (map_pow (algebraMap ℝ ℂ) (‖∑ x ∈ s, c x‖) 2).symm
  rw [hcast]
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  change (∑ x ∈ s, c x) * star (∑ x ∈ s, c x) = _
  rw [star_sum, Finset.sum_mul]
  simp only [Finset.mul_sum]

/-- **Dual quadratic-form expansion** (finite matrices): for arbitrary
`φ : ι → κ → ℂ` and `b : κ → ℂ`,

  Σ_n |Σ_x star(φ n x)·b_x|² = Σ_x Σ_y b_x·star(b_y)·(Σ_n star(φ n x)·φ n y).

This is the algebraic foundation of Montgomery's dual large-sieve argument:
the left side sums over `n`, while the right side is regrouped by `x, y`.
The kernel `Σ_n star(φ n x)·φ n y` is the object to be estimated. -/
theorem dualExpansion {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (φ : ι → κ → ℂ) (b : κ → ℂ) :
    (∑ n ∈ s, ‖∑ x ∈ t, star (φ n x) * b x‖ ^ 2) =
      ∑ x ∈ t, ∑ y ∈ t, b x * star (b y) * (∑ n ∈ s, star (φ n x) * φ n y) := by
  let f : ι → κ → κ → ℂ := fun n x y => b x * star (b y) * (star (φ n x) * φ n y)
  calc
    (∑ n ∈ s, ‖∑ x ∈ t, star (φ n x) * b x‖ ^ 2)
        = ∑ n ∈ s, ∑ x ∈ t, ∑ y ∈ t, (star (φ n x) * b x) * star (star (φ n y) * b y) := by
          push_cast
          apply Finset.sum_congr rfl
          intro n hn
          rw [normSq_sum_eq_sum_mul_star]
    _ = ∑ n ∈ s, ∑ x ∈ t, ∑ y ∈ t, f n x y := by
          apply Finset.sum_congr rfl; intro n hn
          apply Finset.sum_congr rfl; intro x hx
          apply Finset.sum_congr rfl; intro y hy
          have hst : star (star (φ n y) * b y) = star (b y) * φ n y := by
            rw [star_mul, star_star]
          rw [hst]
          simp [f]
          ring
    _ = ∑ x ∈ t, ∑ y ∈ t, ∑ n ∈ s, f n x y := by
          calc
            (∑ n ∈ s, ∑ x ∈ t, ∑ y ∈ t, f n x y)
                = ∑ x ∈ t, ∑ n ∈ s, ∑ y ∈ t, f n x y := by
                  rw [Finset.sum_comm]
            _ = ∑ x ∈ t, ∑ y ∈ t, ∑ n ∈ s, f n x y := by
                  apply Finset.sum_congr rfl
                  intro x hx
                  rw [Finset.sum_comm]
    _ = ∑ x ∈ t, ∑ y ∈ t, b x * star (b y) * (∑ n ∈ s, star (φ n x) * φ n y) := by
          apply Finset.sum_congr rfl; intro x hx
          apply Finset.sum_congr rfl; intro y hy
          simp [f]
          rw [← Finset.mul_sum]

/- ## 2. Real additive-character version -/

/-- Character cross-product identity:
`star(e(nx))·e(ny) = star(e(n(x−y)))` (`n : ℤ`). -/
theorem charReal_cross (n : ℤ) (x y : ℝ) :
    star (charReal ((n : ℝ) * x)) * charReal ((n : ℝ) * y) =
      star (charReal ((n : ℝ) * (x - y))) := by
  rw [mul_sub, charReal_sub, star_mul, star_star, mul_comm]

/-- **Dual quadratic-form identity** (real additive characters):
take `φ n x = e(nx)`.

  Σ_n |Σ_x star(e(nx))·b_x|² = Σ_x Σ_y b_x·star(b_y)·Σ_n star(e(n(x−y))). -/
theorem dualQuadraticIdentity (s : Finset ℤ) (t : Finset ℝ) (b : ℝ → ℂ) :
    (∑ n ∈ s, ‖∑ x ∈ t, star (charReal ((n : ℝ) * x)) * b x‖ ^ 2) =
      ∑ x ∈ t, ∑ y ∈ t, b x * star (b y) *
        (∑ n ∈ s, star (charReal ((n : ℝ) * (x - y)))) := by
  simpa only [charReal_cross] using
    dualExpansion s t (fun n x => charReal ((n : ℝ) * x)) b

/-- **Dual quadratic-form identity (shifted interval)**:
expand the dual form for `n ∈ (M, M+N]`. -/
theorem dualQuadraticIdentity_Icc (M : ℤ) (N : ℕ) (t : Finset ℝ) (b : ℝ → ℂ) :
    (∑ n ∈ Finset.Icc (M + 1) (M + N),
        ‖∑ x ∈ t, star (charReal ((n : ℝ) * x)) * b x‖ ^ 2) =
      ∑ x ∈ t, ∑ y ∈ t, b x * star (b y) *
        (∑ n ∈ Finset.Icc (M + 1) (M + N), star (charReal ((n : ℝ) * (x - y)))) :=
  dualQuadraticIdentity (Finset.Icc (M + 1) (M + N)) t b

/- ## 3. Circle version (AddCircle 1) -/


end

end AnalyticNumberTheory.LargeSieve
end

/- BEGIN SOURCE: AnalyticNumberTheory/LargeSieve/WellSpaced.lean -/
section
/- # AnalyticNumberTheory.LargeSieve.WellSpaced

## Well-spaced points and the Schur test

This module combines the dual quadratic-form identity
(`dualQuadraticIdentity_Icc`, `Duality.lean`) with the interval
geometric-sum bound (`geomSum_exp_bound_Icc`, `GeomSum.lean`) to prove
an additive large-sieve inequality with an explicit weaker constant.

The spacing condition is parametrized by `ℝ`: a set `X ⊆ ℝ` is
`δ`-well-spaced modulo 1 if any two distinct points have distance
`distToInt` at least `δ`. This corresponds to `wellSpaced` on
`AddCircle 1` in `Additive.lean`, while keeping the counting geometry
in the real numbers and their fractional parts. The circle formulation
requires a separate bridge.

Proof structure (the classical Montgomery framework, with a weaker constant):

1. **Counting**: a set in `[a, a+L]` with pairwise real distances at
   least `δ` has at most `L/δ + 1` points (`sepCard_le_interval`,
   by induction on the largest point). Splitting fractional parts into
   `[0,r]` and `[1−r,1]` gives the ball count
   `#{y : distToInt(x−y) ≤ r} ≤ 2r/δ + 2`
   (`wellSpaced_ball_card_le`).
2. **Dyadic-shell row sum**: for fixed `x`, group `Σ_y |K(x,y)|`
   by dyadic shells of `distToInt(x−y)`. Each shell has at most
   `2·2^{-j}/δ + 2` points; the geometric bound `≤ 1/(2ρ)` gives
   `Σ_{y∈X} |Σ_{M<n≤M+N} e(n(x−y))| ≤ N + (2K+12)/δ`,
   where `K = ⌈log₂(1/δ)⌉` (`wellSpacedRowSum`).
3. **Schur/Cauchy--Schwarz test** (`quadraticFormBound`):
   for a kernel with symmetric norms (`|K xy| = |K yx|`), as for
   a Hermitian kernel, row sums at most `C` imply
   `|Σ_x Σ_y b_x·conj(b_y)·K_xy| ≤ C·Σ_x |b_x|²`.
4. **Assembly**: the dual identity, row-sum bound, and Schur test give
   `largeSieveDual_wellSpaced`; `largeSieveDuality` then gives
   `largeSievePrimal_wellSpaced`.

The explicit weaker constant is
`C(N,δ) = N + (2⌈log₂(1/δ)⌉+12)/δ`, with the ceiling taken in `ℕ`.
The classical sharp constant `N + 1/δ` requires Montgomery's
positive-kernel/Parseval method (a Fejér-kernel majorant or a
Hilbert-type quadratic-form estimate). It is not proved here:
naive dyadic-shell counting and the Schur test incur a `log(1/δ)` factor.

References: Montgomery, "Topics in Multiplicative Number Theory" (1971), Ch. 1;
Iwaniec & Kowalski, "Analytic Number Theory" (2004), Ch. 7.
-/

namespace AnalyticNumberTheory.LargeSieve

open scoped BigOperators

noncomputable section

/- ## 1. Real-parametrized well-spaced sets and basic distance properties -/

/-- `X ⊆ ℝ` is `δ`-well-spaced modulo 1: any two distinct points have
distance modulo 1 at least `δ`. This corresponds to `wellSpaced` on
`AddCircle 1` in `Additive.lean`. -/
def wellSpacedReal (X : Finset ℝ) (δ : ℝ) : Prop :=
  ∀ ⦃x : ℝ⦄, x ∈ X → ∀ ⦃y : ℝ⦄, y ∈ X → x ≠ y → δ ≤ distToInt (x - y)

/-- Distance modulo 1 is bounded by every integer translate:
`‖z‖ ≤ |z − k|` (`k : ℤ`). -/
theorem distToInt_le_sub (z : ℝ) (k : ℤ) : distToInt z ≤ |z - (k : ℝ)| := by
  dsimp [distToInt]
  by_cases hk : (k : ℝ) ≤ ⌊z⌋
  · have hnonneg : 0 ≤ z - (k : ℝ) := by
      have hz : (k : ℝ) ≤ z := le_trans hk (Int.floor_le z)
      linarith
    have hz : z - (k : ℝ) = Int.fract z + ((⌊z⌋ : ℝ) - (k : ℝ)) := by
      rw [← Int.self_sub_floor z]
      ring
    rw [abs_of_nonneg hnonneg, hz]
    have h1 : Int.fract z ≤ Int.fract z + ((⌊z⌋ : ℝ) - (k : ℝ)) := by linarith
    exact le_trans (min_le_left _ _) h1
  · have hklt : ⌊z⌋ < (k : ℝ) := lt_of_not_ge hk
    have hkz : ⌊z⌋ < k := by exact_mod_cast hklt
    have hk1 : ⌊z⌋ + 1 ≤ k := by omega
    have hk1r : (⌊z⌋ : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hk1
    have hnonneg : 0 ≤ (k : ℝ) - z := by
      have hzlt : z < (k : ℝ) := lt_of_lt_of_le (Int.lt_floor_add_one z) hk1r
      linarith
    have hz : (k : ℝ) - z = ((k : ℝ) - (⌊z⌋ : ℝ)) - Int.fract z := by
      rw [← Int.self_sub_floor z]
      ring
    rw [abs_sub_comm, abs_of_nonneg hnonneg, hz]
    have h1 : 1 - Int.fract z ≤ ((k : ℝ) - (⌊z⌋ : ℝ)) - Int.fract z := by
      have hkdiff : 1 ≤ (k : ℝ) - (⌊z⌋ : ℝ) := by linarith
      linarith [Int.fract_lt_one z]
    exact le_trans (min_le_right _ _) h1

/-- Distance modulo 1 is bounded by the difference of fractional parts:
`‖a−b‖ ≤ |fract a − fract b|`, using the integer translate `⌊a⌋ − ⌊b⌋`. -/
theorem distToInt_le_fract (a b : ℝ) :
    distToInt (a - b) ≤ |Int.fract a - Int.fract b| := by
  have hsub : a - b - ((⌊a⌋ : ℝ) - (⌊b⌋ : ℝ)) = Int.fract a - Int.fract b := by
    rw [← Int.self_sub_floor a, ← Int.self_sub_floor b]
    ring
  have hd := distToInt_le_sub (a - b) (⌊a⌋ - ⌊b⌋)
  simpa [hsub] using hd

/-- Distance modulo 1 is even: `‖−w‖ = ‖w‖`. -/
theorem distToInt_neg (w : ℝ) : distToInt (-w) = distToInt w := by
  unfold distToInt
  by_cases hw : Int.fract w = 0
  · rw [Int.fract_neg_eq_zero.mpr hw, hw]
  · rw [Int.fract_neg hw, sub_sub_cancel, min_comm]

/-- Symmetry of distance modulo 1: `‖a−b‖ = ‖b−a‖`. -/
theorem distToInt_sub_comm (a b : ℝ) : distToInt (a - b) = distToInt (b - a) := by
  simpa only [neg_sub] using distToInt_neg (b - a)

/-- `distToInt z = 0` if and only if `z ∈ ℤ`. -/
theorem distToInt_eq_zero_iff (z : ℝ) : distToInt z = 0 ↔ ∃ k : ℤ, (k : ℝ) = z := by
  have hfract : distToInt z = 0 ↔ Int.fract z = 0 := by
    unfold distToInt
    rw [min_eq_iff]
    have hright : 0 < 1 - Int.fract z := sub_pos.mpr (Int.fract_lt_one z)
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩)
      · exact h
      · linarith
    · intro h
      exact Or.inl ⟨h, h.le.trans hright.le⟩
  exact hfract.trans Int.fract_eq_zero_iff


/- ## 2. Counting lemmas -/

/-- **Interval count**: a set in `[a, a+L]` with pairwise distances at
least `δ` has at most `L/δ + 1` points. Choose its largest point `m`;
the remaining points lie in `[a, m−δ]`, so induction applies. -/
theorem sepCard_le_interval (a L : ℝ) {δ : ℝ} (hδ : 0 < δ) (hL : 0 ≤ L)
    (S : Finset ℝ)
    (hS : ∀ x ∈ S, a ≤ x ∧ x ≤ a + L)
    (hsep : ∀ ⦃x : ℝ⦄, x ∈ S → ∀ ⦃y : ℝ⦄, y ∈ S → x ≠ y → δ ≤ |x - y|) :
    (S.card : ℝ) ≤ L / δ + 1 := by
  have hmain : ∀ n : ℕ, ∀ S : Finset ℝ, S.card = n →
      ∀ L : ℝ, 0 ≤ L → (∀ x ∈ S, a ≤ x ∧ x ≤ a + L) →
      (∀ ⦃x : ℝ⦄, x ∈ S → ∀ ⦃y : ℝ⦄, y ∈ S → x ≠ y → δ ≤ |x - y|) →
      (S.card : ℝ) ≤ L / δ + 1 := by
    intro n
    induction n with
    | zero =>
        intro S hcard L' hL' hS' hsep'
        have h0 : (S.card : ℝ) = 0 := by simp [hcard]
        rw [h0]
        have h1 : 0 ≤ L' / δ := div_nonneg hL' (le_of_lt hδ)
        nlinarith
    | succ n ih =>
        intro S hcard L' hL' hS' hsep'
        have hne : S.Nonempty := Finset.card_pos.mp (by omega)
        let m : ℝ := S.max' hne
        let S' : Finset ℝ := S.erase m
        have hm : m ∈ S := S.max'_mem hne
        have hcard' : S'.card + 1 = S.card := by
          dsimp [S']
          exact Finset.card_erase_add_one hm
        have hcardS' : S'.card = n := by omega
        have hS'' : ∀ x ∈ S', a ≤ x ∧ x ≤ m - δ := by
          intro x hx
          have hxS : x ∈ S := (Finset.erase_subset m S) hx
          have hxm : x ≤ m := by
            dsimp [m]
            exact S.le_max' x hxS
          have hxne : x ≠ m := (Finset.mem_erase.mp hx).1
          have hδx : δ ≤ m - x := by
            simpa only [abs_of_nonneg (sub_nonneg.mpr hxm)] using hsep' hm hxS hxne.symm
          exact ⟨(hS' x hxS).1, by linarith⟩
        have hsep'' : ∀ ⦃x : ℝ⦄, x ∈ S' → ∀ ⦃y : ℝ⦄, y ∈ S' → x ≠ y → δ ≤ |x - y| := by
          intro x hx y hy hxy
          exact hsep' (Finset.erase_subset m S hx) (Finset.erase_subset m S hy) hxy
        by_cases hS'empty : S' = ∅
        · have hS'card0 : S'.card = 0 := by
            simpa using congrArg Finset.card hS'empty
          have hcardS : S.card = 1 := by omega
          have hc1 : (S.card : ℝ) = 1 := by exact_mod_cast hcardS
          rw [hc1]
          have h1 : 0 ≤ L' / δ := div_nonneg hL' (le_of_lt hδ)
          nlinarith
        · have hS'ne : S'.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS'empty
          rcases hS'ne with ⟨w, hw⟩
          have hw1 : a ≤ w := (hS'' w hw).1
          have hw2 : w ≤ m - δ := (hS'' w hw).2
          have hL'' : 0 ≤ m - δ - a := by linarith
          have hIH := ih S' hcardS' (m - δ - a) hL''
            (by
              intro x hx
              have hx' := hS'' x hx
              exact ⟨hx'.1, by linarith [hx'.2]⟩) hsep''
          have hmle : m ≤ a + L' := (hS' m hm).2
          calc
            (S.card : ℝ) = (S'.card : ℝ) + 1 := by
              exact_mod_cast hcard'.symm
            _ ≤ ((m - δ - a) / δ + 1) + 1 := by linarith [hIH]
            _ = (m - a) / δ + 1 := by
              field_simp [hδ.ne']
              ring
            _ ≤ L' / δ + 1 := by
              have hma : m - a ≤ L' := by linarith
              have hd : (m - a) / δ ≤ L' / δ := div_le_div_of_nonneg_right hma (le_of_lt hδ)
              linarith
  exact hmain S.card S rfl L hL hS hsep

/-- Translation and reflection preserve the lower bound on distance modulo one. -/
private lemma distToInt_sub_le_fract_sub (x y z : ℝ) :
    distToInt (y - z) ≤ |Int.fract (x - y) - Int.fract (x - z)| := by
  have h := distToInt_le_fract (x - y) (x - z)
  rw [show (x - y) - (x - z) = -(y - z) by ring, distToInt_neg] at h
  exact h

/-- **Left-arc count**: at most `r/δ + 1` well-spaced points satisfy
`fract(x−y) ≤ r`. -/
theorem wellSpaced_fract_left_card_le (X : Finset ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hws : wellSpacedReal X δ) (x : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    ((X.filter fun y => Int.fract (x - y) ≤ r).card : ℝ) ≤ r / δ + 1 := by
  let S : Finset ℝ := X.filter fun y => Int.fract (x - y) ≤ r
  let T : Finset ℝ := S.image fun y => Int.fract (x - y)
  have hcard : T.card = S.card := by
    dsimp [T]
    apply Finset.card_image_of_injOn
    intro y hy z hz hfz
    by_contra hyz
    have hyX : y ∈ X := (Finset.mem_filter.mp hy).1
    have hzX : z ∈ X := (Finset.mem_filter.mp hz).1
    have hδyz : δ ≤ distToInt (y - z) := hws hyX hzX hyz
    have hle := distToInt_sub_le_fract_sub x y z
    have hdiff : |Int.fract (x - y) - Int.fract (x - z)| = 0 := by
      have hfz' : Int.fract (x - y) = Int.fract (x - z) := by simpa using hfz
      rw [hfz']
      norm_num
    linarith
  have hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ r := by
    intro t ht
    rcases (Finset.mem_image.mp ht) with ⟨y, hy, rfl⟩
    exact ⟨Int.fract_nonneg (x - y), (Finset.mem_filter.mp hy).2⟩
  have hTsep : ∀ ⦃t : ℝ⦄, t ∈ T → ∀ ⦃u : ℝ⦄, u ∈ T → t ≠ u → δ ≤ |t - u| := by
    intro t ht u hu htu
    rcases (Finset.mem_image.mp ht) with ⟨y, hy, rfl⟩
    rcases (Finset.mem_image.mp hu) with ⟨z, hz, rfl⟩
    have hyX : y ∈ X := (Finset.mem_filter.mp hy).1
    have hzX : z ∈ X := (Finset.mem_filter.mp hz).1
    have hyz : y ≠ z := by
      intro hyz
      apply htu
      congr
    have hδyz : δ ≤ distToInt (y - z) := hws hyX hzX hyz
    have hle := distToInt_sub_le_fract_sub x y z
    linarith
  have hcardT : (T.card : ℝ) ≤ r / δ + 1 :=
    sepCard_le_interval 0 r hδ hr T (by simpa using hT) hTsep
  change (S.card : ℝ) ≤ r / δ + 1
  rw [← hcard]
  exact hcardT

/-- **Right-arc count**: at most `r/δ + 1` well-spaced points satisfy
`1 − fract(x−y) ≤ r`. -/
theorem wellSpaced_fract_right_card_le (X : Finset ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hws : wellSpacedReal X δ) (x : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    ((X.filter fun y => 1 - Int.fract (x - y) ≤ r).card : ℝ) ≤ r / δ + 1 := by
  let S : Finset ℝ := X.filter fun y => 1 - Int.fract (x - y) ≤ r
  let T : Finset ℝ := S.image fun y => Int.fract (x - y)
  have hcard : T.card = S.card := by
    dsimp [T]
    apply Finset.card_image_of_injOn
    intro y hy z hz hfz
    by_contra hyz
    have hyX : y ∈ X := (Finset.mem_filter.mp hy).1
    have hzX : z ∈ X := (Finset.mem_filter.mp hz).1
    have hδyz : δ ≤ distToInt (y - z) := hws hyX hzX hyz
    have hle := distToInt_sub_le_fract_sub x y z
    have hdiff : |Int.fract (x - y) - Int.fract (x - z)| = 0 := by
      have hfz' : Int.fract (x - y) = Int.fract (x - z) := by simpa using hfz
      rw [hfz']
      norm_num
    linarith
  have hT : ∀ t ∈ T, 1 - r ≤ t ∧ t ≤ 1 := by
    intro t ht
    rcases (Finset.mem_image.mp ht) with ⟨y, hy, rfl⟩
    have hyr : 1 - Int.fract (x - y) ≤ r := (Finset.mem_filter.mp hy).2
    exact ⟨by linarith, le_of_lt (Int.fract_lt_one (x - y))⟩
  have hTsep : ∀ ⦃t : ℝ⦄, t ∈ T → ∀ ⦃u : ℝ⦄, u ∈ T → t ≠ u → δ ≤ |t - u| := by
    intro t ht u hu htu
    rcases (Finset.mem_image.mp ht) with ⟨y, hy, rfl⟩
    rcases (Finset.mem_image.mp hu) with ⟨z, hz, rfl⟩
    have hyX : y ∈ X := (Finset.mem_filter.mp hy).1
    have hzX : z ∈ X := (Finset.mem_filter.mp hz).1
    have hyz : y ≠ z := by
      intro hyz
      apply htu
      congr
    have hδyz : δ ≤ distToInt (y - z) := hws hyX hzX hyz
    have hle := distToInt_sub_le_fract_sub x y z
    linarith
  have hcardT : (T.card : ℝ) ≤ r / δ + 1 :=
    sepCard_le_interval (1 - r) r hδ hr T (by simpa [sub_add_cancel] using hT) hTsep
  change (S.card : ℝ) ≤ r / δ + 1
  rw [← hcard]
  exact hcardT

/-- **Ball count modulo 1**: a ball of radius `r ≤ 1/2` contains at most
`2r/δ + 2` well-spaced points. Split fractional parts into left and
right intervals, each containing at most `r/δ + 1` points. -/
theorem wellSpaced_ball_card_le (X : Finset ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hws : wellSpacedReal X δ) (x : ℝ) {r : ℝ} (hr0 : 0 ≤ r) (_hr1 : r ≤ 1 / 2) :
    ((X.filter fun y => distToInt (x - y) ≤ r).card : ℝ) ≤ 2 * r / δ + 2 := by
  let B : Finset ℝ := X.filter fun y => distToInt (x - y) ≤ r
  let L : Finset ℝ := X.filter fun y => Int.fract (x - y) ≤ r
  let R : Finset ℝ := X.filter fun y => 1 - Int.fract (x - y) ≤ r
  have hsub : B ⊆ L ∪ R := by
    intro y hy
    have hyX : y ∈ X := (Finset.mem_filter.mp hy).1
    have hyB : distToInt (x - y) ≤ r := (Finset.mem_filter.mp hy).2
    have hmin : min (Int.fract (x - y)) (1 - Int.fract (x - y)) ≤ r := by
      dsimp [distToInt] at hyB
      exact hyB
    rcases (min_le_iff.mp hmin) with hf | hf
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hyX, hf⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hyX, hf⟩))
  have hB : B.card ≤ L.card + R.card := by
    have h1 : B.card ≤ (L ∪ R).card := Finset.card_le_card hsub
    exact le_trans h1 (Finset.card_union_le L R)
  have hL : (L.card : ℝ) ≤ r / δ + 1 := wellSpaced_fract_left_card_le X hδ hws x hr0
  have hR : (R.card : ℝ) ≤ r / δ + 1 := wellSpaced_fract_right_card_le X hδ hws x hr0
  calc
    (B.card : ℝ) ≤ (L.card : ℝ) + (R.card : ℝ) := by exact_mod_cast hB
    _ ≤ (r / δ + 1) + (r / δ + 1) := by linarith
    _ = 2 * r / δ + 2 := by ring

/- ## 3. Interval-kernel properties and dyadic-shell row sums -/

/-- `e(0) = 1`. -/
theorem charReal_zero : charReal 0 = 1 := by
  dsimp [charReal]
  simp

/-- The interval exponential sum at zero: `Σ_{M<n≤M+N} e(n·0) = N`. -/
theorem charRealSubIcc_zero (M : ℤ) (N : ℕ) : charRealSubIcc M N 0 = (N : ℂ) := by
  simp [charRealSubIcc_eq_shift, charReal_zero]

/-- Conjugation of the interval kernel:
`Σ_n e(n·(−z)) = conj(Σ_n e(nz))`. -/
theorem charRealSubIcc_neg (M : ℤ) (N : ℕ) (z : ℝ) :
    charRealSubIcc M N (-z) = star (charRealSubIcc M N z) := by
  simp only [charRealSubIcc, mul_neg, charReal_neg, star_sum]

/-- Kernel norm symmetry:
`|Σ_n e(n(x−y))| = |Σ_n e(n(y−x))|`. -/
theorem charRealSubIcc_norm_sym (M : ℤ) (N : ℕ) (x y : ℝ) :
    ‖charRealSubIcc M N (x - y)‖ = ‖charRealSubIcc M N (y - x)‖ := by
  rw [show y - x = -(x - y) from (neg_sub x y).symm, charRealSubIcc_neg, norm_star]

/-- Pointwise shell bound: if `0 < ρ ≤ 1/2` and `(1/2)^J < ρ`, then
`1/(2ρ) ≤ Σ_{2≤j≤J} 2^{j-1}·1_{ρ ≤ (1/2)^{j-1}}`.
Choose the least `k` with `(1/2)^k < ρ`. Then `2 ≤ k ≤ J`,
`1/(2ρ) < 2^{k-1}`, and every shell index `j ∈ [2,k]` contributes. -/
theorem shell_geom_bound {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ρ ≤ 1 / 2) {J : ℕ}
    (hJ : (1 / 2 : ℝ) ^ J < ρ) :
    1 / (2 * ρ) ≤
      ∑ j ∈ Finset.Icc 2 J,
        (2 : ℝ) ^ (j - 1) * if ρ ≤ (1 / 2 : ℝ) ^ (j - 1) then (1 : ℝ) else 0 := by
  let p : ℕ → Prop := fun j => (1 / 2 : ℝ) ^ j < ρ
  have hp : ∃ j, p j := ⟨J, hJ⟩
  let k : ℕ := Nat.find hp
  have hk : p k := Nat.find_spec hp
  have hkmin : ∀ j < k, ¬p j := by
    intro j hj hj'
    have hle : Nat.find hp ≤ j := Nat.find_min' hp hj'
    omega
  have hk2 : 2 ≤ k := by
    by_contra h
    have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with hk0 | hk1
    · have : (1 : ℝ) < ρ := by simpa [p, hk0] using hk
      linarith
    · have : (1 / 2 : ℝ) < ρ := by simpa [p, hk1] using hk
      linarith
  have hkJ : k ≤ J := by
    by_contra h
    have hJk : J < k := lt_of_not_ge h
    have hnp : ¬p J := hkmin J hJk
    exact hnp hJ
  have hρk : (1 / 2 : ℝ) ^ k < ρ := hk
  have h2ρ : (1 / 2 : ℝ) ^ (k - 1) < 2 * ρ := by
    have hmul : 2 * ((1 / 2 : ℝ) ^ k) < 2 * ρ := by
      exact mul_lt_mul_of_pos_left hρk (by norm_num : 0 < (2 : ℝ))
    have hred : 2 * ((1 / 2 : ℝ) ^ k) = (1 / 2 : ℝ) ^ (k - 1) := by
      have hkform : k = (k - 1) + 1 := by omega
      nth_rewrite 1 [hkform]
      rw [pow_succ']
      ring_nf
    rwa [hred] at hmul
  have hbound : 1 / (2 * ρ) < (2 : ℝ) ^ (k - 1) := by
    have hpos1 : 0 < (1 / 2 : ℝ) ^ (k - 1) := pow_pos (by norm_num) (k - 1)
    have hpos2 : 0 < 2 * ρ := by nlinarith [hρ0]
    have h1 : 1 / (2 * ρ) < 1 / ((1 / 2 : ℝ) ^ (k - 1)) :=
      one_div_lt_one_div_of_lt hpos1 h2ρ
    have h2 : 1 / ((1 / 2 : ℝ) ^ (k - 1)) = (2 : ℝ) ^ (k - 1) := by
      rw [one_div_pow]
      field_simp
    simpa [h2] using h1
  have hind : ∀ j ∈ Finset.Icc 2 k, ρ ≤ (1 / 2 : ℝ) ^ (j - 1) := by
    intro j hj
    have hj' : 2 ≤ j ∧ j ≤ k := Finset.mem_Icc.mp hj
    have hj1 : j - 1 < k := by omega
    have hnp : ¬p (j - 1) := hkmin (j - 1) hj1
    dsimp [p] at hnp
    exact le_of_not_gt hnp
  have hcong : (∑ j ∈ Finset.Icc 2 k, (2 : ℝ) ^ (j - 1)) =
      ∑ j ∈ Finset.Icc 2 k,
        (2 : ℝ) ^ (j - 1) * if ρ ≤ (1 / 2 : ℝ) ^ (j - 1) then (1 : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [ite_eq_left (hind j hj)]
    ring
  have hsub : Finset.Icc 2 k ⊆ Finset.Icc 2 J := Finset.Icc_subset_Icc (by norm_num) hkJ
  have hnonneg : ∀ j ∈ Finset.Icc 2 J, j ∉ Finset.Icc 2 k →
      0 ≤ (2 : ℝ) ^ (j - 1) * if ρ ≤ (1 / 2 : ℝ) ^ (j - 1) then (1 : ℝ) else 0 := by
    intro j hj hjn
    by_cases hc : ρ ≤ (1 / 2 : ℝ) ^ (j - 1)
    · rw [ite_eq_left hc]
      positivity
    · rw [ite_eq_right hc]
      positivity
  have hsum_low : (∑ j ∈ Finset.Icc 2 k, (2 : ℝ) ^ (j - 1)) ≤
      ∑ j ∈ Finset.Icc 2 J,
        (2 : ℝ) ^ (j - 1) * if ρ ≤ (1 / 2 : ℝ) ^ (j - 1) then (1 : ℝ) else 0 := by
    calc
      (∑ j ∈ Finset.Icc 2 k, (2 : ℝ) ^ (j - 1))
          = ∑ j ∈ Finset.Icc 2 k,
              (2 : ℝ) ^ (j - 1) * if ρ ≤ (1 / 2 : ℝ) ^ (j - 1) then (1 : ℝ) else 0 := hcong
      _ ≤ ∑ j ∈ Finset.Icc 2 J,
              (2 : ℝ) ^ (j - 1) * if ρ ≤ (1 / 2 : ℝ) ^ (j - 1) then (1 : ℝ) else 0 :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
  have hlast : (2 : ℝ) ^ (k - 1) ≤ ∑ j ∈ Finset.Icc 2 k, (2 : ℝ) ^ (j - 1) := by
    have hnon : ∀ j ∈ Finset.Icc 2 k, 0 ≤ (2 : ℝ) ^ (j - 1) := by
      intro j hj
      positivity
    have hk2mem : k ∈ Finset.Icc 2 k := Finset.mem_Icc.mpr ⟨hk2, le_rfl⟩
    exact Finset.single_le_sum hnon hk2mem
  exact le_of_lt (lt_of_lt_of_le hbound (le_trans hlast hsum_low))

/-- `(1/2)^m · 2^m = 1`. -/
theorem half_pow_mul_two_pow (m : ℕ) : (1 / 2 : ℝ) ^ m * (2 : ℝ) ^ m = 1 := by
  rw [one_div_pow]
  exact div_mul_cancel₀ (1 : ℝ) (pow_ne_zero m (by norm_num))

/-- `(1/2)^m ≤ 1/2` for `1 ≤ m`. -/
theorem half_pow_le_half {m : ℕ} (hm : 1 ≤ m) : (1 / 2 : ℝ) ^ m ≤ 1 / 2 := by
  rw [one_div_pow]
  have h2m : 2 ≤ (2 : ℝ) ^ m := by
    have hpow1 : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ m := pow_le_pow_right₀ (by norm_num) hm
    simpa using hpow1
  have hpos : 0 < (2 : ℝ) ^ m := pow_pos (by norm_num) m
  exact one_div_le_one_div_of_le (by norm_num : 0 < (2 : ℝ)) h2m

/- ### 3½. The weaker constant and log₂ lemmas -/

/-- **Weaker additive large-sieve constant**:
`C(N,δ) = N + (2⌈log₂(1/δ)⌉+12)/δ`, with a natural-number ceiling.
This is explicit; the logarithmic factor is the cost of naive
dyadic-shell counting and the Schur test. The sharp `N + 1/δ`
requires a positive-kernel argument not supplied here. -/
noncomputable def largeSieveBound (N : ℕ) (δ : ℝ) : ℝ :=
  (N : ℝ) + (2 * (Nat.ceil (Real.log (1 / δ) / Real.log 2) : ℝ) + 12) / δ

theorem largeSieveBound_nonneg (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    0 ≤ largeSieveBound N δ := by
  unfold largeSieveBound
  positivity

/-- `K := ⌈log₂(1/δ)⌉` satisfies `(1/2)^{K+1} < δ` for `0 < δ ≤ 1`. -/
theorem log2_ceil_half_lt {δ : ℝ} (hδ : 0 < δ) (_hδ1 : δ ≤ 1) :
    (1 / 2 : ℝ) ^ (Nat.ceil (Real.log (1 / δ) / Real.log 2) + 1) < δ := by
  -- Compare logarithms; the extra step above the ceiling makes the bound strict.
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hceil : Real.log (1 / δ) / Real.log 2 <
      (Nat.ceil (Real.log (1 / δ) / Real.log 2) : ℝ) + 1 := by
    have hle := Nat.le_ceil (Real.log (1 / δ) / Real.log 2)
    linarith
  have hlog := (div_lt_iff₀ hlog2).mp hceil
  apply (Real.log_lt_log_iff (pow_pos (by norm_num) _) hδ).mp
  rw [Real.log_pow]
  simp only [Nat.cast_add, Nat.cast_one, one_div, Real.log_inv] at hlog ⊢
  nlinarith

/-- `K := ⌈log₂(1/δ)⌉` satisfies `2^K < 2/δ` for `0 < δ ≤ 1`. -/
theorem log2_ceil_two_pow_lt {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (2 : ℝ) ^ Nat.ceil (Real.log (1 / δ) / Real.log 2) < 2 / δ := by
  let a : ℝ := Real.log (1 / δ) / Real.log 2
  let K : ℕ := Nat.ceil a
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : 1 < (2 : ℝ))
  have ha0 : 0 ≤ a := by
    dsimp [a]
    have h1d : 1 ≤ 1 / δ := one_le_one_div hδ hδ1
    have hlog : 0 ≤ Real.log (1 / δ) := Real.log_nonneg h1d
    exact div_nonneg hlog (le_of_lt hlog2pos)
  have hK : (K : ℝ) < a + 1 := by
    dsimp [K]
    exact Nat.ceil_lt_add_one ha0
  have hmono : (2 : ℝ) ^ (K : ℝ) < (2 : ℝ) ^ (a + 1) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hK
  have hmono' : (2 : ℝ) ^ K < (2 : ℝ) ^ (a + 1) := by
    simpa [Real.rpow_natCast] using hmono
  have h2a : (2 : ℝ) ^ a = 1 / δ := by
    dsimp [a]
    rw [Real.rpow_def_of_pos (by norm_num : 0 < (2 : ℝ))]
    have harg : Real.log 2 * (Real.log (1 / δ) / Real.log 2) = Real.log (1 / δ) := by
      field_simp [hlog2pos.ne']
    have hpos : 0 < 1 / δ := by positivity
    calc
      Real.exp (Real.log 2 * (Real.log (1 / δ) / Real.log 2))
          = Real.exp (Real.log (1 / δ)) := by rw [harg]
      _ = 1 / δ := Real.exp_log hpos
  have h2 : (2 : ℝ) ^ (a + 1) = 2 / δ := by
    calc
      (2 : ℝ) ^ (a + 1) = (2 : ℝ) ^ a * (2 : ℝ) ^ 1 := Real.rpow_add (by norm_num) a 1
      _ = (1 / δ) * 2 := by
        rw [h2a]
        norm_num
      _ = 2 / δ := by ring
  exact lt_of_lt_of_eq hmono' h2

/-- **Dyadic-shell row sum (weaker constant)**: for a `δ`-well-spaced
set `X` modulo 1 and fixed `x ∈ X`,
`Σ_{y∈X} |Σ_{M<n≤M+N} e(n(x−y))| ≤ N + (2K+12)/δ`,
where `K = ⌈log₂(1/δ)⌉`. The logarithmic factor is the cost of
the naive Schur test. -/
theorem wellSpacedRowSum (M : ℤ) (N : ℕ) {δ : ℝ} (hδ : 0 < δ) (X : Finset ℝ)
    (hws : wellSpacedReal X δ) (x : ℝ) (hx : x ∈ X) :
    (∑ y ∈ X, ‖charRealSubIcc M N (x - y)‖) ≤ largeSieveBound N δ := by
  by_cases hδhalf : δ ≤ 1 / 2
  · let K : ℕ := Nat.ceil (Real.log (1 / δ) / Real.log 2)
    let J : ℕ := K + 1
    have hδle1 : δ ≤ 1 := le_trans hδhalf (by norm_num)
    have hJδ : (1 / 2 : ℝ) ^ J < δ := by
      dsimp [J, K]
      exact log2_ceil_half_lt hδ hδle1
    have hsplit : (∑ y ∈ X, ‖charRealSubIcc M N (x - y)‖) =
        (N : ℝ) + ∑ y ∈ X.erase x, ‖charRealSubIcc M N (x - y)‖ := by
      calc
        (∑ y ∈ X, ‖charRealSubIcc M N (x - y)‖)
            = ∑ y ∈ X.erase x, ‖charRealSubIcc M N (x - y)‖ + ‖charRealSubIcc M N (x - x)‖ := by
              exact (Finset.sum_erase_add X (fun y => ‖charRealSubIcc M N (x - y)‖) hx).symm
        _ = ‖charRealSubIcc M N (x - x)‖ + ∑ y ∈ X.erase x, ‖charRealSubIcc M N (x - y)‖ := by
              rw [add_comm]
        _ = (N : ℝ) + ∑ y ∈ X.erase x, ‖charRealSubIcc M N (x - y)‖ := by
              have hz : charRealSubIcc M N 0 = (N : ℂ) := charRealSubIcc_zero M N
              rw [show x - x = 0 by ring, hz]
              norm_num
    have hfar : (∑ y ∈ X.erase x, ‖charRealSubIcc M N (x - y)‖) ≤
        ∑ y ∈ X.erase x, 1 / (2 * distToInt (x - y)) := by
      apply Finset.sum_le_sum
      intro y hy
      have hyX : y ∈ X := (Finset.erase_subset x X) hy
      have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
      have hδy0 : δ ≤ distToInt (y - x) := hws hyX hx hyx
      have hδy : δ ≤ distToInt (x - y) := by
        rwa [distToInt_sub_comm y x] at hδy0
      have hnotint : ¬ ∃ k : ℤ, (k : ℝ) = x - y := by
        intro hk
        have h0 : distToInt (x - y) = 0 := (distToInt_eq_zero_iff (x - y)).mpr hk
        linarith
      exact (geomSum_exp_bound_Icc M N (x - y)).2 hnotint
    have hpt : ∀ y ∈ X.erase x,
        1 / (2 * distToInt (x - y)) ≤
          ∑ j ∈ Finset.Icc 2 J, (2 : ℝ) ^ (j - 1) *
            if distToInt (x - y) ≤ (1 / 2 : ℝ) ^ (j - 1) then (1 : ℝ) else 0 := by
      intro y hy
      have hyX : y ∈ X := (Finset.erase_subset x X) hy
      have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
      have hδy0 : δ ≤ distToInt (y - x) := hws hyX hx hyx
      have hδy : δ ≤ distToInt (x - y) := by
        rwa [distToInt_sub_comm y x] at hδy0
      have hρ0 : 0 < distToInt (x - y) := lt_of_lt_of_le hδ hδy
      have hρ : distToInt (x - y) ≤ 1 / 2 := distToInt_le_half (x - y)
      have hJρ : (1 / 2 : ℝ) ^ J < distToInt (x - y) := lt_of_lt_of_le hJδ hδy
      exact shell_geom_bound hρ0 hρ hJρ
    have hshell : (∑ y ∈ X.erase x, 1 / (2 * distToInt (x - y))) ≤
        ∑ j ∈ Finset.Icc 2 J, (2 : ℝ) ^ (j - 1) *
          ((X.filter fun y => distToInt (x - y) ≤ (1 / 2 : ℝ) ^ (j - 1)).card : ℝ) := by
      calc
        (∑ y ∈ X.erase x, 1 / (2 * distToInt (x - y)))
            ≤ ∑ y ∈ X.erase x,
                ∑ j ∈ Finset.Icc 2 J, (2 : ℝ) ^ (j - 1) *
                  if distToInt (x - y) ≤ (1 / 2 : ℝ) ^ (j - 1) then (1 : ℝ) else 0 := by
                  exact Finset.sum_le_sum hpt
        _ = ∑ j ∈ Finset.Icc 2 J,
                ∑ y ∈ X.erase x, (2 : ℝ) ^ (j - 1) *
                  if distToInt (x - y) ≤ (1 / 2 : ℝ) ^ (j - 1) then (1 : ℝ) else 0 := by
                  rw [Finset.sum_comm]
        _ ≤ ∑ j ∈ Finset.Icc 2 J, (2 : ℝ) ^ (j - 1) *
              ((X.filter fun y => distToInt (x - y) ≤ (1 / 2 : ℝ) ^ (j - 1)).card : ℝ) := by
              apply Finset.sum_le_sum
              intro j hj
              have hle : (∑ y ∈ X.erase x, (2 : ℝ) ^ (j - 1) *
                    if distToInt (x - y) ≤ (1 / 2 : ℝ) ^ (j - 1) then (1 : ℝ) else 0) ≤
                  (∑ y ∈ X, (2 : ℝ) ^ (j - 1) *
                    if distToInt (x - y) ≤ (1 / 2 : ℝ) ^ (j - 1) then (1 : ℝ) else 0) := by
                exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset x X)
                  (by intro y hy hyneg; positivity)
              have hb : (∑ y ∈ X, (2 : ℝ) ^ (j - 1) *
                    if distToInt (x - y) ≤ (1 / 2 : ℝ) ^ (j - 1) then (1 : ℝ) else 0) =
                  (2 : ℝ) ^ (j - 1) *
                    ((X.filter fun y => distToInt (x - y) ≤ (1 / 2 : ℝ) ^ (j - 1)).card : ℝ) := by
                rw [← Finset.mul_sum]
                congr 1
                exact Finset.sum_boole (fun y => distToInt (x - y) ≤ (1 / 2 : ℝ) ^ (j - 1)) X
              rw [← hb]
              exact hle
    have hballs : ∀ j ∈ Finset.Icc 2 J,
        ((X.filter fun y => distToInt (x - y) ≤ (1 / 2 : ℝ) ^ (j - 1)).card : ℝ) ≤
          2 * (1 / 2 : ℝ) ^ (j - 1) / δ + 2 := by
      intro j hj
      have hj2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
      have hjm1 : 1 ≤ j - 1 := by omega
      have hjr : (1 / 2 : ℝ) ^ (j - 1) ≤ 1 / 2 := half_pow_le_half hjm1
      have hjr0 : 0 ≤ (1 / 2 : ℝ) ^ (j - 1) := by positivity
      exact wellSpaced_ball_card_le X hδ hws x hjr0 hjr
    have hshell2 : (∑ j ∈ Finset.Icc 2 J, (2 : ℝ) ^ (j - 1) *
          ((X.filter fun y => distToInt (x - y) ≤ (1 / 2 : ℝ) ^ (j - 1)).card : ℝ)) ≤
        ∑ j ∈ Finset.Icc 2 J, (2 : ℝ) ^ (j - 1) * (2 * (1 / 2 : ℝ) ^ (j - 1) / δ + 2) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hballs j hj) (pow_nonneg (by norm_num) (j - 1))
    have hterm : ∀ j ∈ Finset.Icc 2 J,
        (2 : ℝ) ^ (j - 1) * (2 * (1 / 2 : ℝ) ^ (j - 1) / δ + 2) =
          (2 : ℝ) / δ + (2 : ℝ) ^ j := by
      intro j hj
      have hcancel : (1 / 2 : ℝ) ^ (j - 1) * (2 : ℝ) ^ (j - 1) = 1 :=
        half_pow_mul_two_pow (j - 1)
      have h1 : (2 : ℝ) ^ (j - 1) * (2 * (1 / 2 : ℝ) ^ (j - 1) / δ) = (2 : ℝ) / δ := by
        calc
          (2 : ℝ) ^ (j - 1) * (2 * (1 / 2 : ℝ) ^ (j - 1) / δ)
              = (2 : ℝ) ^ (j - 1) * (2 * (1 / 2 : ℝ) ^ (j - 1)) / δ := by ring
          _ = 2 * ((1 / 2 : ℝ) ^ (j - 1) * (2 : ℝ) ^ (j - 1)) / δ := by ring
          _ = 2 / δ := by rw [hcancel]; ring
      have h2 : (2 : ℝ) ^ (j - 1) * 2 = (2 : ℝ) ^ j := by
        have hj' : 2 ≤ j ∧ j ≤ J := Finset.mem_Icc.mp hj
        have hjj : j - 1 + 1 = j := by omega
        nth_rewrite 2 [← hjj]
        rw [pow_succ]
      calc
        (2 : ℝ) ^ (j - 1) * (2 * (1 / 2 : ℝ) ^ (j - 1) / δ + 2)
            = (2 : ℝ) ^ (j - 1) * (2 * (1 / 2 : ℝ) ^ (j - 1) / δ) + (2 : ℝ) ^ (j - 1) * 2 := by ring
        _ = (2 : ℝ) / δ + (2 : ℝ) ^ j := by rw [h1, h2]
    have hshell3 : (∑ j ∈ Finset.Icc 2 J, (2 : ℝ) ^ (j - 1) * (2 * (1 / 2 : ℝ) ^ (j - 1) / δ + 2)) =
        (∑ j ∈ Finset.Icc 2 J, (2 : ℝ) / δ) + (∑ j ∈ Finset.Icc 2 J, (2 : ℝ) ^ j) := by
      have hcong : (∑ j ∈ Finset.Icc 2 J, (2 : ℝ) ^ (j - 1) * (2 * (1 / 2 : ℝ) ^ (j - 1) / δ + 2)) =
          ∑ j ∈ Finset.Icc 2 J, ((2 : ℝ) / δ + (2 : ℝ) ^ j) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hterm j hj
      rw [hcong, Finset.sum_add_distrib]
    have hcardJ : ((Finset.Icc 2 J).card : ℝ) ≤ (J : ℝ) + 1 := by
      have hsub : Finset.Icc 2 J ⊆ Finset.range (J + 1) := by
        intro j hj
        have hj' : 2 ≤ j ∧ j ≤ J := Finset.mem_Icc.mp hj
        exact Finset.mem_range.mpr (by omega)
      have hc : (Finset.Icc 2 J).card ≤ (Finset.range (J + 1)).card := Finset.card_le_card hsub
      have hcr : (Finset.range (J + 1)).card = J + 1 := by simp
      have hc' : (Finset.Icc 2 J).card ≤ J + 1 := by
        rw [hcr] at hc
        exact hc
      exact_mod_cast hc'
    have hsum2 : (∑ j ∈ Finset.Icc 2 J, (2 : ℝ) / δ) ≤ (2 * (K : ℝ) + 4) / δ := by
      have hsc : (∑ j ∈ Finset.Icc 2 J, (2 : ℝ) / δ) =
          (2 / δ) * ((Finset.Icc 2 J).card : ℝ) := by
        rw [Finset.sum_const]
        simp [nsmul_eq_mul]
        ring
      rw [hsc]
      have hpos : 0 ≤ 2 / δ := by positivity
      have hm : (2 / δ) * ((Finset.Icc 2 J).card : ℝ) ≤ (2 / δ) * ((J : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hcardJ hpos
      have hcalc : (2 / δ) * ((J : ℝ) + 1) = (2 * (K : ℝ) + 4) / δ := by
        have hJ : (J : ℝ) = (K : ℝ) + 1 := by
          simp [J]
        rw [hJ]
        ring
      exact le_trans hm (le_of_eq hcalc)
    have hsumj : (∑ j ∈ Finset.Icc 2 J, (2 : ℝ) ^ j) ≤ (2 : ℝ) ^ (J + 1) := by
      have hsub : Finset.Icc 2 J ⊆ Finset.range (J + 1) := by
        intro j hj
        have hj' : 2 ≤ j ∧ j ≤ J := Finset.mem_Icc.mp hj
        exact Finset.mem_range.mpr (by omega)
      have hle : (∑ j ∈ Finset.Icc 2 J, (2 : ℝ) ^ j) ≤
          ∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j hj hjn => by positivity)
      have hgeom : (∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j) = (2 : ℝ) ^ (J + 1) - 1 := by
        have hg := geom_sum_mul (2 : ℝ) (J + 1)
        have htwo : (2 : ℝ) - 1 = 1 := by norm_num
        rw [htwo] at hg
        simpa using hg
      calc
        (∑ j ∈ Finset.Icc 2 J, (2 : ℝ) ^ j) ≤ ∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j := hle
        _ = (2 : ℝ) ^ (J + 1) - 1 := hgeom
        _ ≤ (2 : ℝ) ^ (J + 1) := by linarith
    have hpowK : (2 : ℝ) ^ (K + 2) ≤ 8 / δ := by
      have hK : (2 : ℝ) ^ K < 2 / δ := log2_ceil_two_pow_lt hδ hδle1
      calc
        (2 : ℝ) ^ (K + 2) = (2 : ℝ) ^ K * (2 : ℝ) ^ 2 := by
          rw [pow_add]
        _ ≤ (2 / δ) * 4 := by nlinarith [hK]
        _ = 8 / δ := by ring
    have hpowJ : (2 : ℝ) ^ (J + 1) ≤ 8 / δ := by
      dsimp [J]
      simpa [Nat.add_assoc] using hpowK
    calc
      (∑ y ∈ X, ‖charRealSubIcc M N (x - y)‖)
          = (N : ℝ) + ∑ y ∈ X.erase x, ‖charRealSubIcc M N (x - y)‖ := hsplit
      _ ≤ (N : ℝ) + ∑ y ∈ X.erase x, 1 / (2 * distToInt (x - y)) := by
            exact add_le_add (le_rfl : (N : ℝ) ≤ (N : ℝ)) hfar
      _ ≤ (N : ℝ) + (∑ j ∈ Finset.Icc 2 J, (2 : ℝ) ^ (j - 1) *
            ((X.filter fun y => distToInt (x - y) ≤ (1 / 2 : ℝ) ^ (j - 1)).card : ℝ)) := by
            exact add_le_add (le_rfl : (N : ℝ) ≤ (N : ℝ)) hshell
      _ ≤ (N : ℝ) + (∑ j ∈ Finset.Icc 2 J,
            (2 : ℝ) ^ (j - 1) * (2 * (1 / 2 : ℝ) ^ (j - 1) / δ + 2)) := by
            exact add_le_add (le_rfl : (N : ℝ) ≤ (N : ℝ)) hshell2
      _ = (N : ℝ) + ((∑ j ∈ Finset.Icc 2 J, (2 : ℝ) / δ) + (∑ j ∈ Finset.Icc 2 J, (2 : ℝ) ^ j)) := by
            rw [hshell3]
      _ ≤ (N : ℝ) + ((2 * (K : ℝ) + 4) / δ + (2 : ℝ) ^ (J + 1)) := by
            exact add_le_add (le_rfl : (N : ℝ) ≤ (N : ℝ)) (add_le_add hsum2 hsumj)
      _ ≤ (N : ℝ) + (2 * (K : ℝ) + 12) / δ := by
            have h1 : (2 * (K : ℝ) + 4) / δ + (2 : ℝ) ^ (J + 1) ≤ (2 * (K : ℝ) + 4) / δ + 8 / δ := by
              exact add_le_add (le_rfl : (2 * (K : ℝ) + 4) / δ ≤ (2 * (K : ℝ) + 4) / δ) hpowJ
            have h2 : (2 * (K : ℝ) + 4) / δ + 8 / δ = (2 * (K : ℝ) + 12) / δ := by ring
            linarith
      _ = largeSieveBound N δ := by
            dsimp [largeSieveBound, K]
  · -- Spacing greater than one half forces X to consist of the selected point.
    have hX : X = {x} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hx, ?_⟩
      intro y hy
      by_contra hyx
      have hsep := hws hy hx hyx
      have hhalf := distToInt_le_half (y - x)
      linarith
    have hbound : (N : ℝ) ≤ largeSieveBound N δ := by
      unfold largeSieveBound
      exact le_add_of_nonneg_right (by positivity)
    simpa [hX, charRealSubIcc_zero] using hbound

/- ## 4. The Schur test and the additive large sieve -/

/-- **Schur/Cauchy--Schwarz test**: if the kernel has symmetric norms
(`|K xy| = |K yx|`, as for a Hermitian kernel) and row sums at most `C`,
then `|Σ_x Σ_y b_x·conj(b_y)·K_xy| ≤ C·Σ_x |b_x|²`.
Use the triangle inequality and Cauchy--Schwarz for the complex
bilinear form on the product Finset. -/
theorem quadraticFormBound {ι : Type*} (s : Finset ι) (K : ι → ι → ℂ) (b : ι → ℂ)
    {C : ℝ} (hC : 0 ≤ C)
    (hsym : ∀ x ∈ s, ∀ y ∈ s, ‖K x y‖ = ‖K y x‖)
    (hrow : ∀ x ∈ s, (∑ y ∈ s, ‖K x y‖) ≤ C) :
    ‖(∑ x ∈ s, ∑ y ∈ s, b x * star (b y) * K x y : ℂ)‖ ≤ C * ∑ x ∈ s, ‖b x‖ ^ 2 := by
  let u : ι × ι → ℝ := fun p => ‖b p.1‖ * Real.sqrt (‖K p.1 p.2‖)
  let v : ι × ι → ℝ := fun p => ‖b p.2‖ * Real.sqrt (‖K p.1 p.2‖)
  have htri : ‖∑ x ∈ s, ∑ y ∈ s, b x * star (b y) * K x y‖ ≤
      ∑ x ∈ s, ∑ y ∈ s, ‖b x‖ * ‖b y‖ * ‖K x y‖ := by
    calc
      ‖∑ x ∈ s, ∑ y ∈ s, b x * star (b y) * K x y‖
          ≤ ∑ x ∈ s, ‖∑ y ∈ s, b x * star (b y) * K x y‖ :=
            norm_sum_le s (fun x => ∑ y ∈ s, b x * star (b y) * K x y)
      _ ≤ ∑ x ∈ s, ∑ y ∈ s, ‖b x * star (b y) * K x y‖ := by
            apply Finset.sum_le_sum
            intro x hx
            exact norm_sum_le s (fun y => b x * star (b y) * K x y)
      _ = ∑ x ∈ s, ∑ y ∈ s, ‖b x‖ * ‖b y‖ * ‖K x y‖ := by
            apply Finset.sum_congr rfl
            intro x hx
            apply Finset.sum_congr rfl
            intro y hy
            rw [norm_mul, norm_mul, norm_star]
  have hsumU : (∑ p ∈ s ×ˢ s, u p ^ 2) ≤ C * (∑ x ∈ s, ‖b x‖ ^ 2) := by
    calc
      (∑ p ∈ s ×ˢ s, (‖b p.1‖ * Real.sqrt (‖K p.1 p.2‖)) ^ 2)
          = ∑ x ∈ s, ∑ y ∈ s, ‖b x‖ ^ 2 * ‖K x y‖ := by
            rw [Finset.sum_product]
            apply Finset.sum_congr rfl
            intro x hx
            apply Finset.sum_congr rfl
            intro y hy
            rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
      _ = ∑ x ∈ s, ‖b x‖ ^ 2 * (∑ y ∈ s, ‖K x y‖) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [Finset.mul_sum]
      _ ≤ ∑ x ∈ s, ‖b x‖ ^ 2 * C := by
            apply Finset.sum_le_sum
            intro x hx
            exact mul_le_mul_of_nonneg_left (hrow x hx) (sq_nonneg _)
      _ = C * (∑ x ∈ s, ‖b x‖ ^ 2) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x hx
            ring
  have hsumV : (∑ p ∈ s ×ˢ s, v p ^ 2) ≤ C * (∑ x ∈ s, ‖b x‖ ^ 2) := by
    calc
      (∑ p ∈ s ×ˢ s, (‖b p.2‖ * Real.sqrt (‖K p.1 p.2‖)) ^ 2)
          = ∑ x ∈ s, ∑ y ∈ s, ‖b y‖ ^ 2 * ‖K x y‖ := by
            rw [Finset.sum_product]
            apply Finset.sum_congr rfl
            intro x hx
            apply Finset.sum_congr rfl
            intro y hy
            rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
      _ = ∑ y ∈ s, ‖b y‖ ^ 2 * (∑ x ∈ s, ‖K x y‖) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro y hy
            rw [Finset.mul_sum]
      _ ≤ ∑ y ∈ s, ‖b y‖ ^ 2 * C := by
            apply Finset.sum_le_sum
            intro y hy
            have hxy : (∑ x ∈ s, ‖K x y‖) = ∑ x ∈ s, ‖K y x‖ := by
              apply Finset.sum_congr rfl
              intro x hx
              exact hsym x hx y hy
            have hle : (∑ x ∈ s, ‖K y x‖) ≤ C := hrow y hy
            rw [hxy]
            exact mul_le_mul_of_nonneg_left hle (sq_nonneg _)
      _ = C * (∑ x ∈ s, ‖b x‖ ^ 2) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x hx
            ring
  have hcs : (∑ p ∈ s ×ˢ s, u p * v p) ≤
      Real.sqrt (∑ p ∈ s ×ˢ s, u p ^ 2) * Real.sqrt (∑ p ∈ s ×ˢ s, v p ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt (s ×ˢ s) u v
  have htri2 : ‖∑ x ∈ s, ∑ y ∈ s, b x * star (b y) * K x y‖ ≤
      ∑ p ∈ s ×ˢ s, u p * v p := by
    calc
      ‖∑ x ∈ s, ∑ y ∈ s, b x * star (b y) * K x y‖
          ≤ ∑ x ∈ s, ∑ y ∈ s, ‖b x‖ * ‖b y‖ * ‖K x y‖ := htri
      _ = ∑ p ∈ s ×ˢ s, ‖b p.1‖ * ‖b p.2‖ * ‖K p.1 p.2‖ := by
            rw [Finset.sum_product]
      _ = ∑ p ∈ s ×ˢ s, u p * v p := by
            apply Finset.sum_congr rfl
            intro p hp
            dsimp [u, v]
            have hsq : Real.sqrt (‖K p.1 p.2‖) * Real.sqrt (‖K p.1 p.2‖) = ‖K p.1 p.2‖ := by
              rw [← pow_two, Real.sq_sqrt (norm_nonneg _)]
            calc
              ‖b p.1‖ * ‖b p.2‖ * ‖K p.1 p.2‖
                  = (‖b p.1‖ * Real.sqrt (‖K p.1 p.2‖)) *
                      (‖b p.2‖ * Real.sqrt (‖K p.1 p.2‖)) := by
                    conv_lhs =>
                      rw [hsq.symm]
                    ring
              _ = u p * v p := rfl
  have hS : 0 ≤ ∑ x ∈ s, ‖b x‖ ^ 2 := Finset.sum_nonneg (fun x hx => sq_nonneg _)
  have hCS : 0 ≤ C * (∑ x ∈ s, ‖b x‖ ^ 2) := mul_nonneg hC hS
  calc
    ‖(∑ x ∈ s, ∑ y ∈ s, b x * star (b y) * K x y : ℂ)‖
        ≤ ∑ p ∈ s ×ˢ s, u p * v p := htri2
    _ ≤ Real.sqrt (∑ p ∈ s ×ˢ s, u p ^ 2) * Real.sqrt (∑ p ∈ s ×ˢ s, v p ^ 2) := hcs
    _ ≤ C * (∑ x ∈ s, ‖b x‖ ^ 2) := by
          have hU : Real.sqrt (∑ p ∈ s ×ˢ s, u p ^ 2) ≤
              Real.sqrt (C * ∑ x ∈ s, ‖b x‖ ^ 2) :=
            (Real.sqrt_le_sqrt_iff hCS).2 hsumU
          have hV : Real.sqrt (∑ p ∈ s ×ˢ s, v p ^ 2) ≤
              Real.sqrt (C * ∑ x ∈ s, ‖b x‖ ^ 2) :=
            (Real.sqrt_le_sqrt_iff hCS).2 hsumV
          calc
            Real.sqrt (∑ p ∈ s ×ˢ s, u p ^ 2) * Real.sqrt (∑ p ∈ s ×ˢ s, v p ^ 2)
                ≤ Real.sqrt (C * ∑ x ∈ s, ‖b x‖ ^ 2) * Real.sqrt (C * ∑ x ∈ s, ‖b x‖ ^ 2) :=
                  mul_le_mul hU hV (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
            _ = C * (∑ x ∈ s, ‖b x‖ ^ 2) := by
                  rw [← pow_two, Real.sq_sqrt hCS]

/-- **Dual additive large sieve (real version, weaker constant)**:
for a `δ`-well-spaced set `X` modulo 1,
`Σ_{M<n≤M+N} |Σ_{x∈X} conj(e(nx))·b_x|² ≤ C(N,δ)·Σ_{x∈X} |b_x|²`. -/
theorem largeSieveDual_wellSpaced (M : ℤ) (N : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (X : Finset ℝ) (hws : wellSpacedReal X δ) (b : ℝ → ℂ) :
    (∑ n ∈ Finset.Icc (M + 1) (M + N),
        ‖∑ x ∈ X, star (charReal ((n : ℝ) * x)) * b x‖ ^ 2)
      ≤ largeSieveBound N δ * (∑ x ∈ X, ‖b x‖ ^ 2) := by
  let S : ℝ := ∑ n ∈ Finset.Icc (M + 1) (M + N),
    ‖∑ x ∈ X, star (charReal ((n : ℝ) * x)) * b x‖ ^ 2
  have hS : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg (fun n hn => sq_nonneg _)
  have hnorm : S = ‖(S : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_of_nonneg hS]
  have hdq := dualQuadraticIdentity_Icc M N X b
  have hinner : ∀ x y : ℝ,
      (∑ n ∈ Finset.Icc (M + 1) (M + N), star (charReal ((n : ℝ) * (x - y)))) =
        star (charRealSubIcc M N (x - y)) := by
    intro x y
    have hm1 := star_sum (s := Finset.Icc (M + 1) (M + N))
      (fun n : ℤ => charReal ((n : ℝ) * (x - y)))
    exact hm1.symm
  have hqb := quadraticFormBound X (fun x y => star (charRealSubIcc M N (x - y))) b
    (largeSieveBound_nonneg N hδ)
    (by
      intro x hx y hy
      rw [norm_star, norm_star, charRealSubIcc_norm_sym])
    (by
      intro x hx
      simpa [norm_star] using wellSpacedRowSum M N hδ X hws x hx)
  have hchain : (↑(∑ n ∈ Finset.Icc (M + 1) (M + N),
        ‖∑ x ∈ X, star (charReal ((n : ℝ) * x)) * b x‖ ^ 2 : ℝ) : ℂ) =
      ∑ x ∈ X, ∑ y ∈ X, b x * star (b y) * star (charRealSubIcc M N (x - y)) := by
    rw [hdq]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    rw [hinner x y]
  calc
    S = ‖(S : ℂ)‖ := hnorm
    _ = ‖(∑ x ∈ X, ∑ y ∈ X, b x * star (b y) * star (charRealSubIcc M N (x - y)) : ℂ)‖ := by
          rw [hchain]
    _ ≤ largeSieveBound N δ * (∑ x ∈ X, ‖b x‖ ^ 2) := hqb

/-- **Additive large sieve (real version, weaker constant)**:
for a `δ`-well-spaced set `X` modulo 1 and any finitely supported
complex sequence `a`, the primal bound is
`Σ_{x∈X} |Σ_{M<n≤M+N} a_n·e(nx)|² ≤ C(N,δ)·Σ_n |a_n|²`.
It follows from the dual bound by `largeSieveDuality`. -/
theorem largeSievePrimal_wellSpaced (M : ℤ) (N : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (X : Finset ℝ) (hws : wellSpacedReal X δ) (a : ℤ → ℂ) :
    (∑ x ∈ X, ‖∑ n ∈ Finset.Icc (M + 1) (M + N), (charReal ((n : ℝ) * x) : ℂ) * a n‖ ^ 2)
      ≤ largeSieveBound N δ * (∑ n ∈ Finset.Icc (M + 1) (M + N), ‖a n‖ ^ 2) := by
  have hdual := largeSieveDual_wellSpaced M N hδ X hws
  exact (largeSieveDuality (s := X) (t := Finset.Icc (M + 1) (M + N))
    (A := fun x n => (charReal ((n : ℝ) * x) : ℂ)) (largeSieveBound_nonneg N hδ)).2 hdual a

end
end AnalyticNumberTheory.LargeSieve
end

/- BEGIN SOURCE: Erdos12/NaturalLargeSieve.lean -/
section
/- # The additive large sieve for finite sets of positive integers -/

namespace Erdos12Proof

theorem natural_large_sieve {κ : Type*} (S : Finset κ) (a : κ → ℝ)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      δ ≤ dist (a i : UnitAddCircle) (a j : UnitAddCircle))
    (T : Finset ℕ) (N : ℕ) (hT : ∀ n ∈ T, 1 ≤ n ∧ n ≤ N) :
    (∑ i ∈ S, ‖∑ n ∈ T, unitExp ((n : ℝ) * a i)‖ ^ 2) ≤
      AnalyticNumberTheory.LargeSieve.largeSieveBound N δ * T.card := by
  classical
  let U := naturalIntegerSet T
  let I := Finset.Icc (1 : ℤ) (N : ℤ)
  let b : ℤ → ℂ := fun n => if n ∈ U then 1 else 0
  let X := S.image a
  have hUI : U ⊆ I := by
    intro n hn
    obtain ⟨m, hm, rfl⟩ := Finset.mem_map.mp hn
    apply Finset.mem_Icc.mpr
    change (1 : ℤ) ≤ (m : ℤ) ∧ (m : ℤ) ≤ N
    exact ⟨by exact_mod_cast (hT m hm).1, by exact_mod_cast (hT m hm).2⟩
  have hinj : Set.InjOn a S := by
    intro i hi j hj hij
    by_contra hne
    have h := hsep i hi j hj hne
    rw [hij, dist_self] at h
    linarith
  have hws : AnalyticNumberTheory.LargeSieve.wellSpacedReal X δ := by
    intro x hx y hy hxy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    have hij : i ≠ j := fun h => hxy (congrArg a h)
    rw [distToInt_eq_circle_norm, AddCircle.coe_sub, ← dist_eq_norm]
    exact hsep i hi j hj hij
  have hsum (x : ℝ) :
      (∑ n ∈ I, AnalyticNumberTheory.LargeSieve.charReal ((n : ℝ) * x) * b n) =
        ∑ n ∈ T, unitExp ((n : ℝ) * x) := by
    calc
      _ = ∑ n ∈ U, AnalyticNumberTheory.LargeSieve.charReal ((n : ℝ) * x) * b n := by
        symm
        apply Finset.sum_subset hUI
        intro n _ hn
        simp only [b, ite_eq_right hn, mul_zero]
      _ = ∑ n ∈ U, unitExp ((n : ℝ) * x) := by
        apply Finset.sum_congr rfl
        intro n hn
        simp only [b, ite_eq_left hn, mul_one, unitExp_eq_charReal]
      _ = _ := by
        simp only [U, naturalIntegerSet, Finset.sum_map, Function.Embedding.coeFn_mk, Int.cast_natCast]
  have henergy : (∑ n ∈ I, ‖b n‖ ^ 2) = (T.card : ℝ) := by
    calc
      _ = ∑ n ∈ U, ‖b n‖ ^ 2 := by
        symm
        apply Finset.sum_subset hUI
        intro n _ hn
        simp only [b, ite_eq_right hn, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      _ = (U.card : ℝ) := by
        calc
          _ = ∑ _n ∈ U, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro n hn
            simp only [b, ite_eq_left hn, norm_one, one_pow]
          _ = _ := by simp
      _ = _ := by simp only [U, naturalIntegerSet, Finset.card_map]
  have hraw := AnalyticNumberTheory.LargeSieve.largeSievePrimal_wellSpaced 0 N hδ X hws b
  simp only [zero_add] at hraw
  rw [henergy] at hraw
  have hsum' := fun x => hsum x
  dsimp only [I] at hsum'
  simp_rw [hsum'] at hraw
  change (∑ x ∈ S.image a, ‖∑ n ∈ T, unitExp ((n : ℝ) * x)‖ ^ 2) ≤ _ at hraw
  rw [Finset.sum_image hinj] at hraw
  exact hraw

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/PrimeFrequencyFamily.lean -/
section
/- # A separated family of nonzero frequencies at prime moduli -/

namespace Erdos12Proof

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → ℕ) [∀ i, NeZero (m i)]

abbrev PrimeFrequencyIndex := Σ i, ((Finset.univ : Finset (ZMod (m i))).erase 0)

noncomputable def singleFrequencyCube (u : PrimeFrequencyIndex m) : ComplexSieveCube m :=
  Pi.single u.1 u.2.val

omit [Fintype ι] in
theorem singleFrequencyCube_injective : Function.Injective (singleFrequencyCube m) := by
  rintro ⟨i, k⟩ ⟨j, l⟩ h
  have hij : i = j := by
    by_contra hij
    have hi := congrFun h i
    simp only [singleFrequencyCube, Pi.single_eq_same, Pi.single_eq_of_ne hij] at hi
    exact (Finset.ne_of_mem_erase k.property) hi
  subst j
  have hkl : k.val = l.val := Pi.single_injective i h
  have hsub : k = l := Subtype.ext hkl
  subst l
  rfl

theorem singleFrequencyCube_support (u : PrimeFrequencyIndex m) :
    frequencySupport m (singleFrequencyCube m u) = {u.1} := by
  apply Finset.ext
  intro i
  rw [frequencySupport, Finset.mem_filter, Finset.mem_singleton]
  simp only [Finset.mem_univ, true_and]
  dsimp only [singleFrequencyCube]
  by_cases hi : i = u.1
  · subst i
    rw [Pi.single_eq_same]
    exact iff_of_true (Finset.ne_of_mem_erase u.2.property) rfl
  · rw [Pi.single_eq_of_ne hi]
    simp only [ne_eq, not_true_eq_false, hi]

theorem singleFrequencyCube_denominator (u : PrimeFrequencyIndex m) :
    spectralDenominator m (singleFrequencyCube m u) = m u.1 := by
  rw [spectralDenominator, singleFrequencyCube_support, Finset.prod_singleton]

theorem singleFrequencyCube_frequency (u : PrimeFrequencyIndex m) :
    sieveFrequency m (singleFrequencyCube m u) = (u.2.val.val : ℝ) / m u.1 := by
  unfold sieveFrequency singleFrequencyCube
  rw [Finset.sum_eq_single u.1]
  · rw [Pi.single_eq_same]
  · intro i _ hi
    simp only [Pi.single_eq_of_ne hi, ZMod.val_zero, Nat.cast_zero, zero_div]
  · simp

noncomputable def primeFrequency (u : PrimeFrequencyIndex m) : ℝ :=
  cyclicFrequency u.2.val

theorem primeFrequency_eq (u : PrimeFrequencyIndex m) :
    primeFrequency m u = -sieveFrequency m (singleFrequencyCube m u) := by
  rw [singleFrequencyCube_frequency]
  exact neg_div _ _

theorem primeFrequency_separated
    (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j)) {U : ℝ} (hU : 0 < U)
    (hmU : ∀ i, (m i : ℝ) ≤ 2 * U) {u v : PrimeFrequencyIndex m} (huv : u ≠ v) :
    1 / (4 * U ^ 2) ≤ dist (primeFrequency m u : UnitAddCircle) (primeFrequency m v : UnitAddCircle) := by
  have hcube : singleFrequencyCube m u ≠ singleFrequencyCube m v :=
    fun h => huv (singleFrequencyCube_injective m h)
  have hprod0 : 0 < (m u.1 : ℝ) * m v.1 :=
    mul_pos (by exact_mod_cast (NeZero.pos (m u.1))) (by exact_mod_cast (NeZero.pos (m v.1)))
  have hprod : (m u.1 : ℝ) * m v.1 ≤ 4 * U ^ 2 := by
    have h := mul_le_mul (hmU u.1) (hmU v.1) (Nat.cast_nonneg (m v.1)) (by linarith : 0 ≤ 2 * U)
    nlinarith
  rw [primeFrequency_eq, primeFrequency_eq, AddCircle.coe_neg, AddCircle.coe_neg,
    dist_neg_neg, dist_eq_norm, ← AddCircle.coe_sub, UnitAddCircle.norm_eq]
  have hsep := sieveFrequency_integer_separation m (fun i => NeZero.pos (m i)) hcop hcube
    (round (sieveFrequency m (singleFrequencyCube m u) - sieveFrequency m (singleFrequencyCube m v)))
  rw [singleFrequencyCube_denominator, singleFrequencyCube_denominator] at hsep
  exact (one_div_le_one_div_of_le hprod0 hprod).trans hsep

omit [DecidableEq ι] in
theorem sum_primeFrequency {K : Type*} [AddCommMonoid K] (f : ℝ → K) :
    (∑ u : PrimeFrequencyIndex m, f (primeFrequency m u)) =
      ∑ i, ∑ k ∈ (Finset.univ : Finset (ZMod (m i))).erase 0, f (cyclicFrequency k) := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_coe_sort _ (fun k => f (cyclicFrequency k))

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/ResidueFourierEnergy.lean -/
section
/- # Fourier energy forced by occupying at most half the residue classes -/

namespace Erdos12Proof

variable {M : ℕ} [NeZero M]

theorem cyclicSetDensity_sum (T : Finset ℕ) :
    (∑ x : ZMod M, cyclicSetDensity T 1 x) = (T.card : ℝ) := by
  have h := cyclicSetDensity_mean (M := M) T 1
  simp only [finiteMean, blockMass, ZMod.card] at h
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne M)
  field_simp at h
  exact h

theorem natural_fourier_parseval (T : Finset ℕ) :
    (∑ k : ZMod M, ‖∑ n ∈ T, unitExp ((n : ℝ) * cyclicFrequency k)‖ ^ 2) =
      (M : ℝ) * ∑ x : ZMod M, cyclicSetDensity T 1 x ^ 2 := by
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne M)
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne M)
  have hterm (k : ZMod M) :
      (∑ n ∈ T, unitExp ((n : ℝ) * cyclicFrequency k)) =
        (M : ℂ) * cyclicFourier (fun x => (cyclicSetDensity T 1 x : ℂ)) k := by
    rw [cyclicSetDensity_fourier]
    push_cast
    field_simp
    simp only [mul_comm]
  have hp := cyclicFourier_parseval (fun x : ZMod M => (cyclicSetDensity T 1 x : ℂ))
  simp only [finiteMean, ZMod.card, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hp
  calc
    _ = (M : ℝ) ^ 2 * ∑ k : ZMod M,
        ‖cyclicFourier (fun x => (cyclicSetDensity T 1 x : ℂ)) k‖ ^ 2 := by
      simp only [hterm, norm_mul, Complex.norm_natCast, mul_pow, Finset.mul_sum]
    _ = _ := by rw [hp]; field_simp

omit [NeZero M] in
theorem natural_fourier_zero (T : Finset ℕ) :
    ‖∑ n ∈ T, unitExp ((n : ℝ) * cyclicFrequency (0 : ZMod M))‖ ^ 2 = (T.card : ℝ) ^ 2 := by
  simp [cyclicFrequency, unitExp]

theorem natural_fourier_energy_of_half_residues (T : Finset ℕ)
    (hhalf : 2 * (T.image (fun n : ℕ => (n : ZMod M))).card ≤ M) :
    (T.card : ℝ) ^ 2 ≤ ∑ k ∈ (Finset.univ : Finset (ZMod M)).erase 0,
      ‖∑ n ∈ T, unitExp ((n : ℝ) * cyclicFrequency k)‖ ^ 2 := by
  classical
  let S := T.image (fun n : ℕ => (n : ZMod M))
  let f := cyclicSetDensity (M := M) T 1
  have hsum : (∑ x ∈ S, f x) = (T.card : ℝ) := by
    rw [← cyclicSetDensity_sum (M := M) T]
    apply Finset.sum_subset (Finset.subset_univ S)
    intro x _ hx
    apply cyclicSetDensity_zero
    intro n hn hnx
    exact hx (Finset.mem_image.mpr ⟨n, hn, hnx.symm⟩)
  have hcs : (T.card : ℝ) ^ 2 ≤ (S.card : ℝ) * ∑ x ∈ S, f x ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) f
    simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, hsum] using h
  have henergy : (∑ x ∈ S, f x ^ 2) ≤ ∑ x : ZMod M, f x ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun x _ _ => sq_nonneg (f x))
  have hhalfR : 2 * (S.card : ℝ) ≤ M := by exact_mod_cast hhalf
  have htotal : 2 * (T.card : ℝ) ^ 2 ≤ (M : ℝ) * ∑ x : ZMod M, f x ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hcs (by norm_num : (0 : ℝ) ≤ 2)
    have h2 := mul_le_mul_of_nonneg_right hhalfR
      (Finset.sum_nonneg (fun x (_ : x ∈ S) => sq_nonneg (f x)))
    have h3 := mul_le_mul_of_nonneg_left henergy (Nat.cast_nonneg M)
    nlinarith
  have hparseval := natural_fourier_parseval (M := M) T
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset (ZMod M))
    (fun k => ‖∑ n ∈ T, unitExp ((n : ℝ) * cyclicFrequency k)‖ ^ 2) (Finset.mem_univ 0)
  rw [natural_fourier_zero, hparseval] at hsplit
  change _ = (M : ℝ) * ∑ x : ZMod M, f x ^ 2 at hsplit
  linarith

theorem opposite_pair_fourier_energy {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : 2 < p)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ p < q)
    (hopposite : ∀ q ∈ T, ∀ r ∈ T, p ∣ q + r → q = r) :
    (T.card : ℝ) ^ 2 ≤ ∑ k ∈ (Finset.univ : Finset (ZMod p)).erase 0,
      ‖∑ n ∈ T, unitExp ((n : ℝ) * cyclicFrequency k)‖ ^ 2 := by
  apply natural_fourier_energy_of_half_residues
  exact (occupied_residue_classes_le_half hp hp2 T hT hopposite).trans (Nat.sub_le _ _)

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/PrimeLargeSieve.lean -/
section
/- # The large sieve with an earlier block of prime moduli -/

namespace Erdos12Proof

theorem prime_moduli_large_sieve (R T : Finset ℕ)
    (hR : ∀ p ∈ R, p.Prime ∧ 2 < p) (hT : ∀ q ∈ T, q.Prime)
    (horder : ∀ p ∈ R, ∀ q ∈ T, p < q)
    (hopposite : ∀ p ∈ R, ∀ q ∈ T, ∀ r ∈ T, p ∣ q + r → q = r)
    (U : ℝ) (hU : 0 < U) (hRU : ∀ p ∈ R, (p : ℝ) ≤ 2 * U)
    (N : ℕ) (hTN : ∀ q ∈ T, q ≤ N) :
    (R.card : ℝ) * (T.card : ℝ) ^ 2 ≤
      AnalyticNumberTheory.LargeSieve.largeSieveBound N (1 / (4 * U ^ 2)) * T.card := by
  classical
  let m : R → ℕ := Subtype.val
  let : ∀ i : R, NeZero (m i) := fun i => ⟨(hR i i.property).1.ne_zero⟩
  have hcop : ∀ i j : R, i ≠ j → (m i).Coprime (m j) := by
    intro i j hij
    exact (Nat.coprime_primes (hR i i.property).1 (hR j j.property).1).mpr
      (fun h => hij (Subtype.ext h))
  have hlarge := natural_large_sieve (Finset.univ : Finset (PrimeFrequencyIndex m))
    (primeFrequency m) (1 / (4 * U ^ 2)) (by positivity)
    (fun i _ j _ hij => primeFrequency_separated m hcop hU
      (fun p => hRU p p.property) hij)
    T N (fun q hq => ⟨(hT q hq).one_lt.le, hTN q hq⟩)
  rw [sum_primeFrequency m (fun t => ‖∑ n ∈ T, unitExp ((n : ℝ) * t)‖ ^ 2)] at hlarge
  have hlower (p : R) : (T.card : ℝ) ^ 2 ≤
      ∑ k ∈ (Finset.univ : Finset (ZMod (m p))).erase 0,
        ‖∑ n ∈ T, unitExp ((n : ℝ) * cyclicFrequency k)‖ ^ 2 :=
    opposite_pair_fourier_energy (hR p p.property).1 (hR p p.property).2 T
      (fun q hq => ⟨hT q hq, horder p p.property q hq⟩) (hopposite p p.property)
  calc
    _ = ∑ _p : R, (T.card : ℝ) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    _ ≤ ∑ p : R, ∑ k ∈ (Finset.univ : Finset (ZMod (m p))).erase 0,
        ‖∑ n ∈ T, unitExp ((n : ℝ) * cyclicFrequency k)‖ ^ 2 :=
      Finset.sum_le_sum (fun p _ => hlower p)
    _ ≤ _ := hlarge

theorem prime_moduli_cardinality (R T : Finset ℕ) (hRne : R.Nonempty)
    (hR : ∀ p ∈ R, p.Prime ∧ 2 < p) (hT : ∀ q ∈ T, q.Prime)
    (horder : ∀ p ∈ R, ∀ q ∈ T, p < q)
    (hopposite : ∀ p ∈ R, ∀ q ∈ T, ∀ r ∈ T, p ∣ q + r → q = r)
    (U : ℝ) (hU : 0 < U) (hRU : ∀ p ∈ R, (p : ℝ) ≤ 2 * U)
    (N : ℕ) (hTN : ∀ q ∈ T, q ≤ N) :
    (T.card : ℝ) ≤ AnalyticNumberTheory.LargeSieve.largeSieveBound N (1 / (4 * U ^ 2)) / R.card := by
  have hRpos : (0 : ℝ) < R.card := by exact_mod_cast Finset.card_pos.mpr hRne
  by_cases hTne : T.Nonempty
  · have hTpos : (0 : ℝ) < T.card := by exact_mod_cast Finset.card_pos.mpr hTne
    have h := prime_moduli_large_sieve R T hR hT horder hopposite U hU hRU N hTN
    apply (le_div_iff₀ hRpos).mpr
    apply (mul_le_mul_iff_of_pos_right hTpos).mp
    nlinarith [h]
  · have hTempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hTne
    rw [hTempty, Finset.card_empty, Nat.cast_zero]
    exact div_nonneg (AnalyticNumberTheory.LargeSieve.largeSieveBound_nonneg N (by positivity)) hRpos.le

theorem largeSieveBound_dyadic (N J : ℕ) :
    AnalyticNumberTheory.LargeSieve.largeSieveBound N (1 / (4 * ((2 : ℝ) ^ J) ^ 2)) =
      N + (16 * (J : ℝ) + 64) * ((2 : ℝ) ^ J) ^ 2 := by
  have hl2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hpower : 4 * ((2 : ℝ) ^ J) ^ 2 = (2 : ℝ) ^ (2 + 2 * J) := by
    rw [pow_add, ← pow_mul, Nat.mul_comm J 2]
    norm_num
  have hlog : Real.log (1 / (1 / (4 * ((2 : ℝ) ^ J) ^ 2))) / Real.log 2 =
      ((2 + 2 * J : ℕ) : ℝ) := by
    rw [one_div_one_div, hpower, Real.log_pow]
    field_simp
  unfold AnalyticNumberTheory.LargeSieve.largeSieveBound
  rw [hlog, Nat.ceil_natCast]
  push_cast
  field_simp
  ring

theorem largeSieveBound_dyadic_le (N J : ℕ) (hJ : 1 ≤ J) :
    AnalyticNumberTheory.LargeSieve.largeSieveBound N (1 / (4 * ((2 : ℝ) ^ J) ^ 2)) ≤
      N + 80 * (J : ℝ) * ((2 : ℝ) ^ J) ^ 2 := by
  rw [largeSieveBound_dyadic]
  have hJR : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  nlinarith [sq_nonneg ((2 : ℝ) ^ J)]

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/PrimeMiddleBins.lean -/
section
/- # Summing the large-sieve estimate beyond a first dense prime bin -/

namespace Erdos12Proof

theorem finite_dyadic_geometric_tail (S : Finset ℕ) (B : ℕ) (hS : ∀ i ∈ S, B ≤ i) :
    (∑ i ∈ S, (1 / 2 : ℝ) ^ i) ≤ 2 * (1 / 2 : ℝ) ^ B := by
  classical
  let T := S.image (fun i => i - B)
  have hinj : Set.InjOn (fun i => i - B) S := by
    intro i hi j hj heq
    have hiB := hS i hi
    have hjB := hS j hj
    change i - B = j - B at heq
    omega
  have hgeom : (∑ j ∈ T, (1 / 2 : ℝ) ^ j) ≤ 2 := by
    have hs := hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
    have h := hs.summable.sum_le_tsum T (fun j _ => by positivity)
    rw [hs.tsum_eq] at h
    norm_num at h
    exact h
  calc
    _ = (1 / 2 : ℝ) ^ B * ∑ i ∈ S, (1 / 2 : ℝ) ^ (i - B) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← pow_add, Nat.add_sub_of_le (hS i hi)]
    _ = (1 / 2 : ℝ) ^ B * ∑ j ∈ T, (1 / 2 : ℝ) ^ j := by rw [Finset.sum_image hinj]
    _ ≤ (1 / 2 : ℝ) ^ B * 2 := mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = _ := by ring

theorem prime_middle_bin_bound (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (hP : PropertyP (Q : Set ℕ)) (J i : ℕ) (hJ : 2 ≤ J) (hJi : J + 1 ≤ i)
    (hne : (dyadicBin Q J).Nonempty) :
    harmonic (dyadicBin Q i) ≤
      2 / ((dyadicBin Q J).card : ℝ) +
        (80 * (J : ℝ) * ((2 : ℝ) ^ J) ^ 2 / (dyadicBin Q J).card) * (1 / 2 : ℝ) ^ i := by
  let E := dyadicBin Q J
  let T := dyadicBin Q i
  have hE : ∀ p ∈ E, p.Prime ∧ 2 < p := by
    intro p hp
    have hpQ := dyadicBin_subset Q J hp
    have hpLo := (dyadicBin_interval Q J hp).1
    have hfour : 4 ≤ (2 : ℕ) ^ J := by
      have h := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hJ
      norm_num at h
      exact h
    exact ⟨hQ p hpQ, by omega⟩
  have horder : ∀ p ∈ E, ∀ q ∈ T, p < q := by
    intro p hp q hq
    have hpHi := (Finset.mem_filter.mp hp).2.2
    have hqLo := (dyadicBin_interval Q i hq).1
    exact hpHi.trans_le ((Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hJi).trans hqLo)
  have hopposite : ∀ p ∈ E, ∀ q ∈ T, ∀ r ∈ T, p ∣ q + r → q = r := by
    intro p hp q hq r hr hdiv
    exact hP (dyadicBin_subset Q J hp) (dyadicBin_subset Q i hq) (dyadicBin_subset Q i hr)
      hdiv (horder p hp q hq) (horder p hp r hr)
  have hcount := prime_moduli_cardinality E T hne hE
    (fun q hq => hQ q (dyadicBin_subset Q i hq)) horder hopposite
    ((2 : ℝ) ^ J) (by positivity)
    (fun p hp => by exact_mod_cast (dyadicBin_interval Q J hp).2.le)
    (2 ^ (i + 1)) (fun q hq => (Finset.mem_filter.mp hq).2.2.le)
  have hEpos : (0 : ℝ) < E.card := by exact_mod_cast Finset.card_pos.mpr hne
  have hpow : (0 : ℝ) < 2 ^ i := by positivity
  have hraw := largeSieveBound_dyadic_le (2 ^ (i + 1)) J (by omega)
  have hupper : (T.card : ℝ) ≤ (2 * (2 : ℝ) ^ i + 80 * (J : ℝ) * ((2 : ℝ) ^ J) ^ 2) / E.card := by
    apply hcount.trans
    apply div_le_div_of_nonneg_right _ hEpos.le
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul, pow_succ,
      mul_comm ((2 : ℝ) ^ i) 2] using hraw
  calc
    harmonic T ≤ T.card / (2 : ℝ) ^ i := harmonic_le_card_div T hpow
      (fun p hp => by exact_mod_cast (dyadicBin_interval Q i hp).1)
    _ ≤ ((2 * (2 : ℝ) ^ i + 80 * (J : ℝ) * ((2 : ℝ) ^ J) ^ 2) / E.card) / (2 : ℝ) ^ i :=
      div_le_div_of_nonneg_right hupper hpow.le
    _ = _ := by rw [one_div_pow]; field_simp; ring

theorem prime_middle_bins_bound (Q S : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (hP : PropertyP (Q : Set ℕ)) (J B : ℕ) (hJ : 2 ≤ J) (hJB : J + 1 ≤ B)
    (hS : ∀ i ∈ S, B ≤ i) (hne : (dyadicBin Q J).Nonempty) :
    (∑ i ∈ S, harmonic (dyadicBin Q i)) ≤
      2 * S.card / ((dyadicBin Q J).card : ℝ) +
        (160 * (J : ℝ) * ((2 : ℝ) ^ J) ^ 2 / (dyadicBin Q J).card) * (1 / 2 : ℝ) ^ B := by
  have hcoeff : 0 ≤ 80 * (J : ℝ) * ((2 : ℝ) ^ J) ^ 2 / (dyadicBin Q J).card := by positivity
  calc
    _ ≤ ∑ i ∈ S, (2 / ((dyadicBin Q J).card : ℝ) +
        (80 * (J : ℝ) * ((2 : ℝ) ^ J) ^ 2 / (dyadicBin Q J).card) * (1 / 2 : ℝ) ^ i) :=
      Finset.sum_le_sum (fun i hi => prime_middle_bin_bound Q hQ hP J i hJ (hJB.trans (hS i hi)) hne)
    _ = 2 * S.card / ((dyadicBin Q J).card : ℝ) +
        (80 * (J : ℝ) * ((2 : ℝ) ^ J) ^ 2 / (dyadicBin Q J).card) *
          ∑ i ∈ S, (1 / 2 : ℝ) ^ i := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ 2 * S.card / ((dyadicBin Q J).card : ℝ) +
        (80 * (J : ℝ) * ((2 : ℝ) ^ J) ^ 2 / (dyadicBin Q J).card) *
          (2 * (1 / 2 : ℝ) ^ B) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (finite_dyadic_geometric_tail S B hS) hcoeff)
    _ = _ := by ring

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/PrimeTailAssembly.lean -/
section
/- # Assembly of the four prime-tail ranges after the first heavy bin -/

namespace Erdos12Proof

noncomputable def primeTailIndexConstant : ℝ :=
  170 + primeNearIndexConstant + 2 * primeHarmonicWindowConstant

theorem primeTailIndexConstant_pos : 0 < primeTailIndexConstant := by
  unfold primeTailIndexConstant
  linarith [primeNearIndexConstant_pos, primeHarmonicWindowConstant_pos]

theorem prime_tail_bound_after_heavy_bin (R Q : Finset ℕ)
    (hR : ∀ r ∈ R, r.Prime ∧ 2 < r)
    (hQ : ∀ p ∈ Q, p.Prime ∧ 2 < p) (hP : PropertyP (Q : Set ℕ))
    (horder : ∀ r ∈ R, ∀ p ∈ Q, r < p)
    (hopposite : ∀ r ∈ R, ∀ p ∈ Q, ∀ q ∈ Q, r ∣ p + q → p = q)
    (J₀ J : ℕ) (hJ₀ : 0 < J₀) (hJ₀J : J₀ ≤ J) (hJ : 2 ≤ J)
    (hQlower : ∀ p ∈ Q, 2 ^ J₀ ≤ p)
    (hlight : ∀ i ∈ Q.image Nat.log2, i < J →
      ((dyadicBin Q i).card : ℝ) ≤ (1 / 2 : ℝ) ^ R.card * (2 : ℝ) ^ i / (i : ℝ) ^ 2)
    (hheavy : (1 / 2 : ℝ) ^ R.card * (2 : ℝ) ^ J / (J : ℝ) ^ 2 < (dyadicBin Q J).card)
    (hmodulus : primeModulus R ^ 2 ≤ 2 ^ J)
    (hD : roughSieveThreshold ≤ (2 : ℝ) ^ J / 2)
    (hspan : (2 : ℝ) ^ (primeTailNearEnd R.card J - J) ≤
      ((2 : ℝ) ^ J / 2) ^ roughSieveExponent)
    (hbudget : (primeTailSelectionSize J + 1 : ℝ) * (J : ℝ) ^ 4 ≤
      ((1 / 2 : ℝ) ^ R.card) ^ 2 * (2 : ℝ) ^ J) :
    harmonic Q ≤ primeTailIndexConstant * (1 / 2 : ℝ) ^ R.card * (1 + R.card) / J₀ := by
  classical
  let k := R.card
  let δ : ℝ := (1 / 2 : ℝ) ^ k
  let s := primeTailSelectionSize J
  let B := primeTailNearEnd k J
  let I := Q.image Nat.log2
  let n : ℝ := (dyadicBin Q J).card
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hJpos : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hJ₀pos : (0 : ℝ) < J₀ := by exact_mod_cast hJ₀
  have hn : 0 < n := (by positivity : (0 : ℝ) < δ * (2 : ℝ) ^ J / (J : ℝ) ^ 2).trans hheavy
  have hnonempty : (dyadicBin Q J).Nonempty := Finset.card_pos.mp
    (by exact_mod_cast (show (0 : ℝ) < (dyadicBin Q J).card from hn))
  have hselect : s ≤ (dyadicBin Q J).card := by
    have hb := heavy_bin_budget (by omega : 1 ≤ J) hheavy.le hbudget
    have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast (show 1 ≤ J by omega)
    have hsn : (s : ℝ) ≤ n := by
      have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
      have hδn := mul_le_of_le_one_left hn.le hδ1
      change (s + 1 : ℝ) * (J : ℝ) ^ 2 ≤ δ * n at hb
      have hJsq : (1 : ℝ) ≤ (J : ℝ) ^ 2 := by nlinarith
      have hlow : (s + 1 : ℝ) ≤ (s + 1 : ℝ) * (J : ℝ) ^ 2 :=
        le_mul_of_one_le_right (by positivity) hJsq
      linarith
    change (s : ℝ) ≤ ((dyadicBin Q J).card : ℝ) at hsn
    exact_mod_cast hsn
  obtain ⟨E, hEsub, hEcard⟩ := Finset.exists_subset_card_eq hselect
  have hEQ : E ⊆ Q := hEsub.trans (dyadicBin_subset Q J)
  have hRE : Disjoint R E := external_selected_disjoint R Q E hEQ horder
  let M := primeModulus (R ∪ E)
  let H := (s + 1) * (J + 1)
  have hM : M ≤ 2 ^ H := by
    have hRsmall : primeModulus R ≤ 2 ^ J := by
      have hRpos := primeModulus_pos R (fun r hr => (hR r hr).1)
      nlinarith
    have h := selected_modulus_dyadic_bound R E hRE J hRsmall
      (fun p hp => (Finset.mem_filter.mp (hEsub hp)).2.2.le)
    simpa only [hEcard, H, M] using h
  have hB : J + 1 ≤ B := by dsimp only [B, primeTailNearEnd]; omega
  have hI : ∀ i ∈ I, J₀ ≤ i := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
    exact dyadic_index_lower (hQlower p hp)
  have hlightBound : (∑ i ∈ I.filter (fun i => i < J), harmonic (dyadicBin Q i)) ≤ 2 * δ / J₀ := by
    apply light_dyadic_bins_bound Q _ δ hδ.le hJ₀
    · intro i hi
      exact hI i (Finset.mem_filter.mp hi).1
    · intro i hi
      exact hlight i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2
  have hnearBound : (∑ i ∈ I.filter (fun i => J ≤ i ∧ i < B), harmonic (dyadicBin Q i)) ≤
      primeNearIndexConstant * δ * (1 + k) / J := by
    apply prime_near_bins_bound R Q _ hR (fun p hp => (hQ p hp).1) hP horder hopposite J B hJ
      (fun _ hi => (Finset.mem_filter.mp hi).2) hD (by exact_mod_cast hmodulus) hspan
  let S := I.filter (fun i => B ≤ i ∧ 2 ^ i < M ^ 2)
  have hS : ∀ i ∈ S, B ≤ i := fun _ hi => (Finset.mem_filter.mp hi).2.1
  have hScard : (S.card : ℝ) ≤ 2 * (s + 1 : ℝ) * ((J : ℝ) + 1) := by
    have hM2 : M ^ 2 ≤ 2 ^ (2 * H) := by
      have h := Nat.pow_le_pow_left hM 2
      simpa only [← pow_mul, Nat.mul_comm H 2] using h
    have hsub : S ⊆ Finset.range (2 * H) := by
      intro i hi
      have h := (Finset.mem_filter.mp hi).2.2
      exact Finset.mem_range.mpr ((pow_lt_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).mp (h.trans_le hM2))
    have hcard : S.card ≤ 2 * H := by simpa only [Finset.card_range] using Finset.card_le_card hsub
    have hc : (S.card : ℝ) ≤ 2 * (H : ℝ) := by exact_mod_cast hcard
    simpa only [H, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_assoc] using hc
  have hmiddleRaw := prime_middle_bins_bound Q S (fun p hp => (hQ p hp).1) hP J B hJ hB hS hnonempty
  have hmiddleNum := middle_range_numerical_bound (k := k) (by omega : 1 ≤ J) hn hScard hheavy.le hbudget
  have hmiddleBound : (∑ i ∈ S, harmonic (dyadicBin Q i)) ≤ 168 * δ / J :=
    hmiddleRaw.trans hmiddleNum
  have hfarRaw := prime_selected_tail_bound R Q E hR hQ hP hEQ hRE hopposite
  have hfarBound : harmonic (Q.filter (fun p => M ^ 2 ≤ p)) ≤
      2 * primeHarmonicWindowConstant * δ / J := by
    rw [hEcard] at hfarRaw
    apply hfarRaw.trans
    apply (le_div_iff₀ hJpos).mpr
    have hCoeff : (0 : ℝ) ≤ 2 * primeHarmonicWindowConstant * δ :=
      mul_nonneg (mul_nonneg (by norm_num) primeHarmonicWindowConstant_pos.le) hδ.le
    have h := mul_le_mul_of_nonneg_left (selection_dyadic_reciprocal J) hCoeff
    nlinarith
  have hsplit := prime_tail_four_ranges Q (fun p hp => (hQ p hp).1.pos) J B M (by omega)
  have hJorder : (J₀ : ℝ) ≤ J := by exact_mod_cast hJ₀J
  have hnear0 : 0 ≤ primeNearIndexConstant * δ * (1 + (k : ℝ)) := by
    have hC := primeNearIndexConstant_pos
    positivity
  have hnearBound' := hnearBound.trans (div_le_div_of_nonneg_left hnear0 hJ₀pos hJorder)
  have hmiddleBound' := hmiddleBound.trans
    (div_le_div_of_nonneg_left (by positivity : 0 ≤ 168 * δ) hJ₀pos hJorder)
  have hfar0 : 0 ≤ 2 * primeHarmonicWindowConstant * δ := by
    have hC := primeHarmonicWindowConstant_pos
    positivity
  have hfarBound' := hfarBound.trans (div_le_div_of_nonneg_left hfar0 hJ₀pos hJorder)
  apply (le_div_iff₀ hJ₀pos).mpr
  have hL := (le_div_iff₀ hJ₀pos).mp hlightBound
  have hN := (le_div_iff₀ hJ₀pos).mp hnearBound'
  have hM' := (le_div_iff₀ hJ₀pos).mp hmiddleBound'
  have hF := (le_div_iff₀ hJ₀pos).mp hfarBound'
  have hTotal := mul_le_mul_of_nonneg_right hsplit hJ₀pos.le
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hC0 := primeHarmonicWindowConstant_pos.le
  change _ ≤ primeTailIndexConstant * δ * (1 + (k : ℝ))
  unfold primeTailIndexConstant
  nlinarith [mul_nonneg hδ.le hk0, mul_nonneg (mul_nonneg hC0 hδ.le) hk0]

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/PrimeTailScales.lean -/
section
/- # A uniform admissible choice of the prime-tail scales -/

open Filter
open scoped Topology

namespace Erdos12Proof

theorem prime_tail_scale_parameters {c : ℝ} (hc : 0 < c) (D : ℝ) :
    ∃ A J₀ : ℕ, 4 ≤ A ∧ 2 ≤ J₀ ∧ ∀ J ≥ J₀, ∀ k : ℕ, k * A ≤ J →
      D ≤ (2 : ℝ) ^ J / 2 ∧
      (2 : ℝ) ^ (primeTailNearEnd k J - J) ≤ ((2 : ℝ) ^ J / 2) ^ c ∧
      (primeTailSelectionSize J + 1 : ℝ) * (J : ℝ) ^ 4 ≤
        ((1 / 2 : ℝ) ^ k) ^ 2 * (2 : ℝ) ^ J := by
  let A := max 4 ⌈32 / c⌉₊
  have hA : 4 ≤ A := le_max_left _ _
  have hAc : 32 ≤ c * (A : ℝ) := by
    have hceil : 32 / c ≤ (A : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 4 ⌈32 / c⌉₊)
    have h := (div_le_iff₀ hc).mp hceil
    nlinarith
  have hD : ∀ᶠ J : ℕ in atTop, 2 * D ≤ (2 : ℝ) ^ J :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_ge_atTop _
  have hlarge : ∀ᶠ J : ℕ in atTop, (4 / c : ℝ) ≤ J :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  have hmain : ∀ᶠ J : ℕ in atTop, 4 ≤ J ∧ ∀ k : ℕ, k * A ≤ J →
      D ≤ (2 : ℝ) ^ J / 2 ∧
      (2 : ℝ) ^ (primeTailNearEnd k J - J) ≤ ((2 : ℝ) ^ J / 2) ^ c ∧
      (primeTailSelectionSize J + 1 : ℝ) * (J : ℝ) ^ 4 ≤
        ((1 / 2 : ℝ) ^ k) ^ 2 * (2 : ℝ) ^ J := by
    filter_upwards [hD, hlarge, eventual_clog_linear (ε := c / 32) (by positivity),
      selection_polynomial_budget_eventually, eventually_ge_atTop (4 : ℕ)] with J hJD hlargeJ hclog hbudget hJ4
    refine ⟨hJ4, ?_⟩
    intro k hk
    have hk4 : 4 * k ≤ J := by nlinarith
    refine ⟨by linarith, ?_, hbudget k hk4⟩
    have hkR : (k : ℝ) * A ≤ J := by exact_mod_cast hk
    have hAterm := mul_le_mul_of_nonneg_left hAc (Nat.cast_nonneg k)
    have hkterm := mul_le_mul_of_nonneg_left hkR hc.le
    have hkBound : 8 * (k : ℝ) ≤ c * J / 4 := by nlinarith
    have hunit : 1 ≤ c * J / 4 := by
      have h := (div_le_iff₀ hc).mp hlargeJ
      nlinarith
    have hJ4R : (4 : ℝ) ≤ J := by exact_mod_cast hJ4
    have hspan : ((primeTailNearEnd k J - J : ℕ) : ℝ) ≤ ((J : ℝ) - 1) * c := by
      have hsub : primeTailNearEnd k J - J = 8 * k + 8 * Nat.clog 2 J + 1 := by
        dsimp only [primeTailNearEnd]
        omega
      rw [hsub]
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hJ4R hc.le]
    have hbase : (2 : ℝ) ^ J / 2 = (2 : ℝ) ^ ((J : ℝ) - 1) := by
      rw [Real.rpow_sub (by norm_num), Real.rpow_natCast, Real.rpow_one]
    calc
      _ = (2 : ℝ) ^ (((primeTailNearEnd k J - J : ℕ) : ℝ)) := (Real.rpow_natCast _ _).symm
      _ ≤ (2 : ℝ) ^ (((J : ℝ) - 1) * c) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hspan
      _ = _ := by rw [hbase, ← Real.rpow_mul (by norm_num)]
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.mp hmain
  refine ⟨A, max 2 J₀, hA, le_max_left _ _, ?_⟩
  intro J hJ k hk
  exact (hJ₀ J ((le_max_right 2 J₀).trans hJ)).2 k hk

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/PrimeTailDyadic.lean -/
section
/- # The guarded prime-tail theorem at dyadic starting points -/

namespace Erdos12Proof

theorem prime_tail_dyadic :
    ∃ A J₀ : ℕ, 4 ≤ A ∧ 2 ≤ J₀ ∧ ∀ I ≥ J₀, ∀ R Q : Finset ℕ,
      (∀ r ∈ R, r.Prime ∧ 2 < r) →
      (∀ p ∈ Q, p.Prime ∧ 2 < p) → PropertyP (Q : Set ℕ) →
      (∀ r ∈ R, ∀ p ∈ Q, r < p) →
      (∀ r ∈ R, ∀ p ∈ Q, ∀ q ∈ Q, r ∣ p + q → p = q) →
      (∀ p ∈ Q, 2 ^ I ≤ p) → primeModulus R ^ A ≤ 2 ^ I →
      harmonic Q ≤ primeTailIndexConstant * (1 / 2 : ℝ) ^ R.card * (1 + R.card) / I := by
  classical
  obtain ⟨A, J₀, hA, hJ₀, hscales⟩ :=
    prime_tail_scale_parameters roughSieveExponent_pos roughSieveThreshold
  refine ⟨A, J₀, hA, hJ₀, ?_⟩
  intro I hI R Q hR hQ hP horder hopposite hQlower hM
  have hIpos : 0 < I := by omega
  have hIR : (0 : ℝ) < I := by exact_mod_cast hIpos
  have hQpos : ∀ p ∈ Q, 0 < p := fun p hp => (hQ p hp).1.pos
  let S := Q.image Nat.log2
  let bad := S.filter (fun i => ¬((dyadicBin Q i).card : ℝ) ≤
    (1 / 2 : ℝ) ^ R.card * (2 : ℝ) ^ i / (i : ℝ) ^ 2)
  have hS : ∀ i ∈ S, I ≤ i := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
    exact dyadic_index_lower (hQlower p hp)
  by_cases hbad : bad.Nonempty
  · let J := bad.min' hbad
    have hJbad : J ∈ bad := Finset.min'_mem bad hbad
    have hJS : J ∈ S := (Finset.mem_filter.mp hJbad).1
    have hIJ : I ≤ J := hS J hJS
    have hJ : 2 ≤ J := by omega
    have hheavy : (1 / 2 : ℝ) ^ R.card * (2 : ℝ) ^ J / (J : ℝ) ^ 2 < (dyadicBin Q J).card :=
      lt_of_not_ge (Finset.mem_filter.mp hJbad).2
    have hlight : ∀ i ∈ Q.image Nat.log2, i < J →
        ((dyadicBin Q i).card : ℝ) ≤ (1 / 2 : ℝ) ^ R.card * (2 : ℝ) ^ i / (i : ℝ) ^ 2 := by
      intro i hi hij
      by_contra hn
      have hib : i ∈ bad := Finset.mem_filter.mpr ⟨hi, hn⟩
      have hle : J ≤ i := Finset.min'_le bad i hib
      omega
    have hcount : R.card * A ≤ J :=
      (prime_guard_count_bound R (fun r hr => (hR r hr).1) A I hM).trans hIJ
    obtain ⟨hD, hspan, hbudget⟩ := hscales J (hI.trans hIJ) R.card hcount
    have hM1 : 1 ≤ primeModulus R := primeModulus_pos R (fun r hr => (hR r hr).1)
    have hmodulus : primeModulus R ^ 2 ≤ 2 ^ J := by
      exact (Nat.pow_le_pow_right hM1 (show 2 ≤ A by omega)).trans
        (hM.trans (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hIJ))
    exact prime_tail_bound_after_heavy_bin R Q hR hQ hP horder hopposite I J hIpos hIJ hJ
      hQlower hlight hheavy hmodulus hD hspan hbudget
  · have hlight : ∀ i ∈ S, ((dyadicBin Q i).card : ℝ) ≤
        (1 / 2 : ℝ) ^ R.card * (2 : ℝ) ^ i / (i : ℝ) ^ 2 := by
      intro i hi
      by_contra hn
      exact hbad ⟨i, Finset.mem_filter.mpr ⟨hi, hn⟩⟩
    have h := light_dyadic_bins_bound Q S ((1 / 2 : ℝ) ^ R.card) (by positivity) hIpos hS hlight
    rw [← harmonic_dyadic_decomposition Q hQpos] at h
    have hC : 2 ≤ primeTailIndexConstant := by
      unfold primeTailIndexConstant
      linarith [primeNearIndexConstant_pos, primeHarmonicWindowConstant_pos]
    have hδ : 0 ≤ (1 / 2 : ℝ) ^ R.card := by positivity
    have hk : (0 : ℝ) ≤ R.card := Nat.cast_nonneg _
    apply h.trans
    apply div_le_div_of_nonneg_right _ hIR.le
    have h1 := mul_le_mul_of_nonneg_right hC hδ
    have h2 := mul_nonneg (mul_nonneg primeTailIndexConstant_pos.le hδ) hk
    nlinarith

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/PrimeTail.lean -/
section
/- # Reciprocal tails of prime sets with inherited opposite-pair restrictions -/

namespace Erdos12Proof

theorem inverse_primeModulus_le_density (R : Finset ℕ) (hR : ∀ r ∈ R, r.Prime) :
    1 / (primeModulus R : ℝ) ≤ (1 / 2 : ℝ) ^ R.card := by
  have h : (2 : ℝ) ^ R.card ≤ primeModulus R := by exact_mod_cast two_pow_card_le_primeModulus R hR
  have hi := one_div_le_one_div_of_le (by positivity) h
  simpa only [one_div_pow] using hi

theorem prime_tail_harmonic_bound :
    ∃ A₀ : ℕ, 3 ≤ A₀ ∧ ∃ C : ℝ, 0 < C ∧ ∀ R Q : Finset ℕ,
      (∀ r ∈ R, r.Prime ∧ 2 < r) → (∀ p ∈ Q, p.Prime) → PropertyP (Q : Set ℕ) →
      (∀ r ∈ R, ∀ p ∈ Q, r < p) →
      (∀ r ∈ R, ∀ p ∈ Q, ∀ q ∈ Q, r ∣ p + q → p = q) →
      ∀ Y : ℝ, 2 ≤ Y → (primeModulus R : ℝ) ^ A₀ ≤ Y →
      (∀ p ∈ Q, Y ≤ (p : ℝ)) →
      harmonic Q ≤ C * (1 / 2 : ℝ) ^ R.card * (1 + R.card) / Real.log (2 * Y) := by
  obtain ⟨A, J₀, hA, hJ₀, hdyadic⟩ := prime_tail_dyadic
  let T : ℝ := (2 : ℝ) ^ (J₀ + 1)
  let C : ℝ := 2 * Real.log 2 * primeTailIndexConstant +
    primeHarmonicConstant * T * Real.log (2 * T) + 1
  have hT : 2 ≤ T := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 1 ≤ J₀ + 1 by omega)
    simpa only [pow_one] using h
  have hT0 : 0 < T := by linarith
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogT : 0 < Real.log (2 * T) := Real.log_pos (by linarith)
  have hC : 0 < C := by
    have h1 := primeTailIndexConstant_pos
    have h2 := primeHarmonicConstant_pos
    dsimp only [C]
    positivity
  have hClarge : 2 * Real.log 2 * primeTailIndexConstant ≤ C := by
    dsimp only [C]
    have h := mul_pos (mul_pos primeHarmonicConstant_pos hT0) hlogT
    linarith
  have hCsmall : primeHarmonicConstant * T * Real.log (2 * T) ≤ C := by
    dsimp only [C]
    have h := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hl2) primeTailIndexConstant_pos
    linarith
  refine ⟨2 * A, by omega, C, hC, ?_⟩
  intro R Q hR hQ hP horder hopposite Y hY hsize hQY
  let δ : ℝ := (1 / 2 : ℝ) ^ R.card
  let K : ℝ := 1 + R.card
  have hδ : 0 < δ := by positivity
  have hK : 1 ≤ K := by
    dsimp only [K]
    have hcard : (0 : ℝ) ≤ R.card := Nat.cast_nonneg _
    linarith
  have hY0 : 0 < Y := by linarith
  have hlogY : 0 < Real.log (2 * Y) := Real.log_pos (by linarith)
  have hM1 : 1 ≤ primeModulus R := primeModulus_pos R (fun r hr => (hR r hr).1)
  by_cases hsmall : Y ≤ T
  · have hMY : (primeModulus R : ℝ) ≤ Y := by
      have hpow : primeModulus R ≤ primeModulus R ^ (2 * A) := by
        have h := Nat.pow_le_pow_right hM1 (show 1 ≤ 2 * A by omega)
        simpa only [pow_one] using h
      exact (by exact_mod_cast hpow : (primeModulus R : ℝ) ≤ (primeModulus R : ℝ) ^ (2 * A)).trans hsize
    have hδT : 1 ≤ T * δ := by
      have hMT : (primeModulus R : ℝ) ≤ T := hMY.trans hsmall
      have hMR : (0 : ℝ) < primeModulus R := by exact_mod_cast primeModulus_pos R (fun r hr => (hR r hr).1)
      have hi := (one_div_le_one_div_of_le hMR hMT).trans
        (inverse_primeModulus_le_density R (fun r hr => (hR r hr).1))
      have h := (div_le_iff₀ hT0).mp hi
      nlinarith
    have hlogBound : Real.log (2 * Y) ≤ Real.log (2 * T) :=
      Real.log_le_log (by positivity) (by linarith)
    have hH := prime_harmonic_uniform Q hQ hP
    apply (le_div_iff₀ hlogY).mpr
    calc
      harmonic Q * Real.log (2 * Y) ≤ primeHarmonicConstant * Real.log (2 * Y) :=
        mul_le_mul_of_nonneg_right hH hlogY.le
      _ ≤ primeHarmonicConstant * Real.log (2 * T) :=
        mul_le_mul_of_nonneg_left hlogBound primeHarmonicConstant_pos.le
      _ ≤ (primeHarmonicConstant * T * Real.log (2 * T)) * δ := by
        nlinarith [mul_le_mul_of_nonneg_left hδT (mul_nonneg primeHarmonicConstant_pos.le hlogT.le)]
      _ ≤ C * δ := mul_le_mul_of_nonneg_right hCsmall hδ.le
      _ ≤ C * δ * K := le_mul_of_one_le_right (mul_nonneg hC.le hδ.le) hK
  · have hTY : T < Y := lt_of_not_ge hsmall
    obtain ⟨J, hJlo, hJhi⟩ := exists_nat_pow_near (by linarith : (1 : ℝ) ≤ Y)
      (by norm_num : (1 : ℝ) < 2)
    have hJ₀J : J₀ ≤ J := by
      have hpower : (2 : ℝ) ^ (J₀ + 1) < (2 : ℝ) ^ (J + 1) := hTY.trans hJhi
      have hidx := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hpower
      omega
    have hJ2 : 2 ≤ J := hJ₀.trans hJ₀J
    have hJR : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
    have hU2 : (2 : ℝ) ≤ (2 : ℝ) ^ J := by
      simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 1 ≤ J by omega)
    have hMpower : primeModulus R ^ A ≤ 2 ^ J := by
      have hsquared : (((primeModulus R ^ A : ℕ) : ℝ)) ^ 2 ≤ Y := by
        rw [Nat.mul_comm 2 A, pow_mul] at hsize
        simpa only [Nat.cast_pow] using hsize
      by_contra h
      have hu : (2 : ℝ) ^ J < ((primeModulus R ^ A : ℕ) : ℝ) := by exact_mod_cast lt_of_not_ge h
      have ha2 : (2 : ℝ) ≤ ((primeModulus R ^ A : ℕ) : ℝ) := by linarith
      have ha0 : (0 : ℝ) ≤ ((primeModulus R ^ A : ℕ) : ℝ) := Nat.cast_nonneg _
      have hmul := mul_le_mul_of_nonneg_right ha2 ha0
      rw [pow_succ] at hJhi
      nlinarith
    have hodd : ∀ p ∈ Q, p.Prime ∧ 2 < p := by
      intro p hp
      refine ⟨hQ p hp, ?_⟩
      have hpY := hQY p hp
      have hreal : (2 : ℝ) < p := by linarith
      exact_mod_cast hreal
    have hLower : ∀ p ∈ Q, 2 ^ J ≤ p := by
      intro p hp
      exact_mod_cast hJlo.trans (hQY p hp)
    have hH := hdyadic J hJ₀J R Q hR hodd hP horder hopposite hLower hMpower
    have hlogBound : Real.log (2 * Y) ≤ 2 * (J : ℝ) * Real.log 2 := by
      have hYlog := Real.log_le_log hY0 hJhi.le
      rw [Real.log_pow] at hYlog
      rw [Real.log_mul (by norm_num) hY0.ne']
      have hJ2R : (2 : ℝ) ≤ J := by exact_mod_cast hJ2
      push_cast at hYlog
      nlinarith
    apply (le_div_iff₀ hlogY).mpr
    calc
      harmonic Q * Real.log (2 * Y) ≤
          (primeTailIndexConstant * δ * K / J) * Real.log (2 * Y) :=
        mul_le_mul_of_nonneg_right hH hlogY.le
      _ ≤ (primeTailIndexConstant * δ * K / J) * (2 * (J : ℝ) * Real.log 2) :=
        mul_le_mul_of_nonneg_left hlogBound
          (div_nonneg (mul_nonneg (mul_nonneg primeTailIndexConstant_pos.le hδ.le)
            (by linarith)) hJR.le)
      _ = (2 * Real.log 2 * primeTailIndexConstant) * δ * K := by field_simp
      _ ≤ C * δ * K := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hClarge hδ.le) (by linarith)

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/FinitePrimeFibre.lean -/
section
/- # Finite prime fibres and their harmonic estimates -/

namespace Erdos12Proof

noncomputable def finitePrimeFibre (A : Finset ℕ) (g : ℕ) : Finset ℕ := by
  classical
  exact (A.image Nat.maxPrimeFac).filter (fun p => p ∈ primeFibre (A : Set ℕ) g)

theorem mem_finitePrimeFibre_iff (A : Finset ℕ) (hA : ∀ n ∈ A, 1 < n) (g p : ℕ) :
    p ∈ finitePrimeFibre A g ↔ p ∈ primeFibre (A : Set ℕ) g := by
  classical
  constructor
  · exact fun hp => (Finset.mem_filter.mp hp).2
  · intro hp
    have hg : 0 < g := primeFibre_prefix_pos hA hp
    refine Finset.mem_filter.mpr ⟨?_, hp⟩
    exact Finset.mem_image.mpr ⟨g * p, hp.2.2, maxPrimeFac_eq_of_fibre hg hp⟩

theorem finitePrimeFibre_prime (A : Finset ℕ) (g : ℕ) {p : ℕ} (hp : p ∈ finitePrimeFibre A g) :
    p.Prime := by
  classical
  exact (Finset.mem_filter.mp hp).2.1

theorem finitePrimeFibre_product_mem (A : Finset ℕ) (g : ℕ) {p : ℕ} (hp : p ∈ finitePrimeFibre A g) :
    g * p ∈ A := by
  classical
  exact (Finset.mem_filter.mp hp).2.2.2

theorem finitePrimeFibre_propertyP (A : Finset ℕ) (hA : PropertyP (A : Set ℕ))
    {g : ℕ} (hg : 0 < g) : PropertyP (finitePrimeFibre A g : Set ℕ) := by
  classical
  apply (primeFibre_propertyP hA hg).mono
  intro p hp
  exact (Finset.mem_filter.mp hp).2

theorem finitePrimeFibre_uniform (A : Finset ℕ) (hA : PropertyP (A : Set ℕ))
    {g : ℕ} (hg : 0 < g) : harmonic (finitePrimeFibre A g) ≤ primeHarmonicConstant :=
  prime_harmonic_uniform _ (fun _ hp => finitePrimeFibre_prime A g hp) (finitePrimeFibre_propertyP A hA hg)

theorem finitePrimeFibre_bounded (A : Finset ℕ) (N : ℕ) (hA : ∀ n ∈ A, n ≤ N)
    {g p : ℕ} (hg : 0 < g) (hp : p ∈ finitePrimeFibre A g) : p ≤ N := by
  exact (Nat.le_mul_of_pos_left p hg).trans (hA _ (finitePrimeFibre_product_mem A g hp))

noncomputable def terminalPrime (A : Finset ℕ) (g : ℕ) : ℕ :=
  if h : (finitePrimeFibre A g).Nonempty then (finitePrimeFibre A g).min' h else 0

theorem terminalPrime_mem (A : Finset ℕ) (g : ℕ) (h : (finitePrimeFibre A g).Nonempty) :
    terminalPrime A g ∈ finitePrimeFibre A g := by
  rw [terminalPrime, dite_eq_left h]
  exact Finset.min'_mem _ _

theorem terminalPrime_le (A : Finset ℕ) (g : ℕ) (h : (finitePrimeFibre A g).Nonempty)
    {p : ℕ} (hp : p ∈ finitePrimeFibre A g) : terminalPrime A g ≤ p := by
  rw [terminalPrime, dite_eq_left h]
  exact Finset.min'_le _ _ hp

theorem terminalPrime_prime (A : Finset ℕ) (g : ℕ) (h : (finitePrimeFibre A g).Nonempty) :
    (terminalPrime A g).Prime := finitePrimeFibre_prime A g (terminalPrime_mem A g h)

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/FiniteFibreDecomposition.lean -/
section
/- # Exact harmonic decomposition into finite largest-prime fibres -/

namespace Erdos12Proof

theorem harmonic_finite_fibre_decomposition (A : Finset ℕ) (hA : ∀ n ∈ A, 1 < n)
    (N : ℕ) (hN : ∀ n ∈ A, n ≤ N) :
    harmonic A = ∑ g ∈ Finset.range (N + 1), (1 / g : ℝ) * harmonic (finitePrimeFibre A g) := by
  classical
  let S := (Finset.range (N + 1)).sigma (finitePrimeFibre A)
  have hpair : (∑ gp ∈ S, (1 / (gp.1 * gp.2 : ℕ) : ℝ)) = harmonic A := by
    apply Finset.sum_bij (fun gp _ => gp.1 * gp.2)
    · intro gp hgp
      exact finitePrimeFibre_product_mem A gp.1 (Finset.mem_sigma.mp hgp).2
    · rintro ⟨g, p⟩ hgp ⟨h, q⟩ hhq heq
      have hp := (mem_finitePrimeFibre_iff A hA g p).mp (Finset.mem_sigma.mp hgp).2
      have hq := (mem_finitePrimeFibre_iff A hA h q).mp (Finset.mem_sigma.mp hhq).2
      have hg := primeFibre_prefix_pos hA hp
      have hh := primeFibre_prefix_pos hA hq
      obtain ⟨hgh, hpq⟩ := primeFibre_representation_unique hg hh hp hq heq
      subst h
      subst q
      rfl
    · intro n hn
      let p := n.maxPrimeFac
      let g := n / p
      have hp : p ∈ finitePrimeFibre A g :=
        (mem_finitePrimeFibre_iff A hA g p).mpr (quotient_maxPrimeFac_mem hn (hA n hn))
      have hg : g ∈ Finset.range (N + 1) := Finset.mem_range.mpr
        (Nat.lt_succ_of_le ((Nat.div_le_self n p).trans (hN n hn)))
      exact ⟨⟨g, p⟩, Finset.mem_sigma.mpr ⟨hg, hp⟩, Nat.div_mul_cancel Nat.maxPrimeFac_dvd⟩
    · intro gp _
      rfl
  have hinner (g : ℕ) : (∑ p ∈ finitePrimeFibre A g, (1 / (g * p : ℕ) : ℝ)) =
      (1 / g : ℝ) * harmonic (finitePrimeFibre A g) := by
    simp only [Nat.cast_mul, one_div, mul_inv, harmonic, Finset.mul_sum]
  dsimp only [S] at hpair
  rw [Finset.sum_sigma] at hpair
  simp only [hinner] at hpair
  exact hpair.symm

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/PrefixScoreReduction.lean -/
section
/- # Reduction of a finite reciprocal sum to expected prefix scores -/

namespace Erdos12Proof

noncomputable def prefixScore (A : Finset ℕ) (g : ℕ) : ℝ :=
  Real.log (2 * (g.maxPrimeFac : ℝ)) * harmonic (finitePrimeFibre A g)

noncomputable def expectedPrefixScore (N : ℕ) (A : Finset ℕ) : ℝ :=
  weightedSum (primeSampleWeight N) (fun ω =>
    ∑ g ∈ Finset.Icc 2 N, if primePrefixCondition N g ω then prefixScore A g else 0)

theorem weighted_prefix_score (N g : ℕ) (W : ℝ) :
    weightedSum (primeSampleWeight N) (fun ω => if primePrefixCondition N g ω then W else 0) =
      primePrefixProbability N g * W := by
  unfold primePrefixProbability weightedSum
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : primePrefixCondition N g ω
  · simp only [ite_eq_left h, mul_one]
  · simp only [ite_eq_right h, mul_zero, zero_mul]

theorem expectedPrefixScore_eq (N : ℕ) (A : Finset ℕ) :
    expectedPrefixScore N A = ∑ g ∈ Finset.Icc 2 N, primePrefixProbability N g * prefixScore A g := by
  unfold expectedPrefixScore
  rw [weightedSum_finite_sum]
  simp only [weighted_prefix_score]

theorem expectedPrefixScore_lower (N : ℕ) (A : Finset ℕ) :
    prefixWeightConstant * ∑ g ∈ Finset.Icc 2 N, (1 / g : ℝ) * harmonic (finitePrimeFibre A g) ≤
      expectedPrefixScore N A := by
  rw [expectedPrefixScore_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro g hg
  have hg' := Finset.mem_Icc.mp hg
  have h := mul_le_mul_of_nonneg_right (prefix_weight_lower N g (by omega) hg'.2)
    (harmonic_nonneg (finitePrimeFibre A g))
  dsimp only [prefixScore]
  convert h using 1 <;> ring

theorem harmonic_le_expected_prefix_score (A : Finset ℕ) (hA : ∀ n ∈ A, 1 < n)
    (hP : PropertyP (A : Set ℕ)) (N : ℕ) (hN : ∀ n ∈ A, n ≤ N) (hN2 : 2 ≤ N) :
    harmonic A ≤ primeHarmonicConstant + expectedPrefixScore N A / prefixWeightConstant := by
  let f := fun g : ℕ => (1 / g : ℝ) * harmonic (finitePrimeFibre A g)
  have hdecomp := harmonic_finite_fibre_decomposition A hA N hN
  have hsplit := Finset.sum_range_add_sum_Ico f (show 2 ≤ N + 1 by omega)
  have hIco : Finset.Ico 2 (N + 1) = Finset.Icc 2 N := by
    apply Finset.ext
    intro g
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [hIco] at hsplit
  have htwo : (∑ g ∈ Finset.range 2, f g) = harmonic (finitePrimeFibre A 1) := by
    simp [f, Finset.sum_range_succ]
  rw [htwo] at hsplit
  have htail : (∑ g ∈ Finset.Icc 2 N, f g) ≤ expectedPrefixScore N A / prefixWeightConstant := by
    apply (le_div_iff₀ prefixWeightConstant_pos).mpr
    have h := expectedPrefixScore_lower N A
    dsimp only [f]
    nlinarith
  have hone := finitePrimeFibre_uniform A hP (by decide : 0 < (1 : ℕ))
  change harmonic A = ∑ g ∈ Finset.range (N + 1), f g at hdecomp
  linarith

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/FibreTailBounds.lean -/
section
/- # Uniform and guarded bounds for finite prime-fibre scores -/

namespace Erdos12Proof

noncomputable def primeTailExponent : ℕ := Classical.choose prime_tail_harmonic_bound

theorem primeTailExponent_ge_three : 3 ≤ primeTailExponent :=
  (Classical.choose_spec prime_tail_harmonic_bound).1

noncomputable def primeTailConstant : ℝ :=
  Classical.choose (Classical.choose_spec prime_tail_harmonic_bound).2

theorem primeTailConstant_pos : 0 < primeTailConstant :=
  (Classical.choose_spec (Classical.choose_spec prime_tail_harmonic_bound).2).1

theorem prime_tail_bound (R Q : Finset ℕ)
    (hR : ∀ r ∈ R, r.Prime ∧ 2 < r) (hQ : ∀ p ∈ Q, p.Prime)
    (hP : PropertyP (Q : Set ℕ)) (horder : ∀ r ∈ R, ∀ p ∈ Q, r < p)
    (hopposite : ∀ r ∈ R, ∀ p ∈ Q, ∀ q ∈ Q, r ∣ p + q → p = q)
    (Y : ℝ) (hY : 2 ≤ Y) (hsize : (primeModulus R : ℝ) ^ primeTailExponent ≤ Y)
    (hQY : ∀ p ∈ Q, Y ≤ (p : ℝ)) :
    harmonic Q ≤ primeTailConstant * (1 / 2 : ℝ) ^ R.card * (1 + R.card) / Real.log (2 * Y) :=
  (Classical.choose_spec (Classical.choose_spec prime_tail_harmonic_bound).2).2
    R Q hR hQ hP horder hopposite Y hY hsize hQY

theorem finitePrimeFibre_max_le (A : Finset ℕ) {g p : ℕ} (hg : 0 < g)
    (hp : p ∈ finitePrimeFibre A g) : g.maxPrimeFac ≤ p := by
  classical
  have hp' := (Finset.mem_filter.mp hp).2
  by_cases hg1 : g = 1
  · simpa only [hg1, Nat.maxPrimeFac_one] using hp'.1.one_lt.le
  · exact (Nat.maxPrimeFac_le_iff (by omega)).mpr hp'.2.1

theorem finite_fibre_guarded_tail (A : Finset ℕ) (hA : PropertyP (A : Set ℕ))
    {g : ℕ} (hg : 0 < g) (hne : (finitePrimeFibre A g).Nonempty) (R : Finset ℕ)
    (hR : ∀ r ∈ R, r.Prime ∧ 2 < r)
    (horder : ∀ r ∈ R, ∀ p ∈ finitePrimeFibre A g, r < p)
    (hopposite : ∀ r ∈ R, ∀ p ∈ finitePrimeFibre A g, ∀ q ∈ finitePrimeFibre A g,
      r ∣ p + q → p = q)
    (hsize : (primeModulus R : ℝ) ^ primeTailExponent ≤ terminalPrime A g) :
    harmonic (finitePrimeFibre A g) ≤ primeTailConstant * (1 / 2 : ℝ) ^ R.card * (1 + R.card) /
      Real.log (2 * (terminalPrime A g : ℝ)) := by
  exact prime_tail_bound R (finitePrimeFibre A g) hR (fun _ hp => finitePrimeFibre_prime A g hp)
    (finitePrimeFibre_propertyP A hA hg) horder hopposite (terminalPrime A g : ℝ)
    (by exact_mod_cast (terminalPrime_prime A g hne).two_le) hsize
    (fun _ hp => by exact_mod_cast terminalPrime_le A g hne hp)

theorem prefixScore_uniform (A : Finset ℕ) (hA : PropertyP (A : Set ℕ))
    {g : ℕ} (hg : 1 < g) : prefixScore A g ≤ primeTailConstant := by
  classical
  by_cases hne : (finitePrimeFibre A g).Nonempty
  · have hp := terminalPrime_prime A g hne
    have hp2 : (2 : ℝ) ≤ terminalPrime A g := by exact_mod_cast hp.two_le
    have hr := Nat.prime_maxPrimeFac_of_one_lt hg
    have hr0 : (0 : ℝ) < g.maxPrimeFac := by exact_mod_cast hr.pos
    have hmax := finitePrimeFibre_max_le A (by omega : 0 < g) (terminalPrime_mem A g hne)
    have hlog : Real.log (2 * (g.maxPrimeFac : ℝ)) ≤ Real.log (2 * (terminalPrime A g : ℝ)) :=
      Real.log_le_log (by positivity) (by exact_mod_cast Nat.mul_le_mul_left 2 hmax)
    have hden : 0 < Real.log (2 * (terminalPrime A g : ℝ)) := Real.log_pos (by linarith)
    have htail := finite_fibre_guarded_tail A hA (by omega : 0 < g) hne ∅ (by simp)
      (by simp) (by simp) (by simpa only [primeModulus, Finset.prod_empty, Nat.cast_one, one_pow] using hp2.trans' (by norm_num : (1 : ℝ) ≤ 2))
    simp only [Finset.card_empty, pow_zero, Nat.cast_zero, add_zero, mul_one] at htail
    have hmass := (le_div_iff₀ hden).mp htail
    unfold prefixScore
    nlinarith [mul_le_mul_of_nonneg_right hlog (harmonic_nonneg (finitePrimeFibre A g))]
  · have he : finitePrimeFibre A g = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [prefixScore, he, harmonic, Finset.sum_empty, mul_zero]
    exact primeTailConstant_pos.le

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/PrefixChain.lean -/
section
/- # Divisibility and distinct terminals along one finite prefix path -/

namespace Erdos12Proof

theorem prefix_dvd_of_indices {N g h : ℕ} {ω : PrimeSample N}
    (hg0 : g ≠ 0) (hh0 : h ≠ 0) (hgN : g ≤ N)
    (hg : primePrefixCondition N g ω) (hh : primePrefixCondition N h ω)
    (hmax : g.maxPrimeFac ≤ h.maxPrimeFac)
    (hmult : g.maxPrimeFac = h.maxPrimeFac →
      g.factorization g.maxPrimeFac ≤ h.factorization h.maxPrimeFac) : g ∣ h := by
  apply (Nat.factorization_le_iff_dvd hg0 hh0).mp
  intro p
  by_cases hp : p.Prime
  · by_cases hpN : p ≤ N
    · let pi : primesThrough (N : ℝ) := ⟨p,
        (mem_primesThrough (Nat.cast_nonneg N)).mpr ⟨hp, by exact_mod_cast hpN⟩⟩
      by_cases hlow : p < g.maxPrimeFac
      · have hhigh : p < h.maxPrimeFac := hlow.trans_le hmax
        have hgp := (hg pi).1 hlow
        have hhp := (hh pi).1 hhigh
        change (ω pi).val = g.factorization p at hgp
        change (ω pi).val = h.factorization p at hhp
        omega
      · by_cases hgreater : g.maxPrimeFac < p
        · rw [factorization_zero_above_maxPrimeFac hg0 hp hgreater]
          exact Nat.zero_le _
        · have heq : p = g.maxPrimeFac := by omega
          by_cases hsame : g.maxPrimeFac = h.maxPrimeFac
          · simpa only [heq, hsame] using hmult hsame
          · have hless : p < h.maxPrimeFac := by omega
            have hgp := (hg pi).2 heq
            have hhp := (hh pi).1 hless
            change g.factorization p ≤ (ω pi).val at hgp
            change (ω pi).val = h.factorization p at hhp
            omega
    · rw [Nat.factorization_eq_zero_of_lt (by omega : g < p)]
      exact Nat.zero_le _
  · rw [Nat.factorization_eq_zero_of_not_prime g hp]
    exact Nat.zero_le _

theorem prefix_divisibility_total {N g h : ℕ} {ω : PrimeSample N}
    (hg0 : g ≠ 0) (hh0 : h ≠ 0) (hgN : g ≤ N) (hhN : h ≤ N)
    (hg : primePrefixCondition N g ω) (hh : primePrefixCondition N h ω) : g ∣ h ∨ h ∣ g := by
  rcases lt_trichotomy g.maxPrimeFac h.maxPrimeFac with hlt | heq | hgt
  · exact Or.inl (prefix_dvd_of_indices hg0 hh0 hgN hg hh hlt.le (fun h => (hlt.ne h).elim))
  · rcases le_total (g.factorization g.maxPrimeFac) (h.factorization h.maxPrimeFac) with hle | hle
    · exact Or.inl (prefix_dvd_of_indices hg0 hh0 hgN hg hh heq.le (fun _ => hle))
    · exact Or.inr (prefix_dvd_of_indices hh0 hg0 hhN hh hg heq.ge (fun _ => hle))
  · exact Or.inr (prefix_dvd_of_indices hh0 hg0 hhN hh hg hgt.le (fun h => (hgt.ne h).elim))

theorem prefix_same_indices_eq {N g h : ℕ} {ω : PrimeSample N}
    (hg0 : g ≠ 0) (hh0 : h ≠ 0) (hgN : g ≤ N) (hhN : h ≤ N)
    (hg : primePrefixCondition N g ω) (hh : primePrefixCondition N h ω)
    (hmax : g.maxPrimeFac = h.maxPrimeFac)
    (hmult : g.factorization g.maxPrimeFac = h.factorization h.maxPrimeFac) : g = h := by
  apply Nat.dvd_antisymm
  · exact prefix_dvd_of_indices hg0 hh0 hgN hg hh hmax.le (fun _ => hmult.le)
  · exact prefix_dvd_of_indices hh0 hg0 hhN hh hg hmax.ge (fun _ => hmult.ge)

theorem prefix_terminals_distinct (A : Finset ℕ) (hA : Primitive (A : Set ℕ))
    {N g h : ℕ} {ω : PrimeSample N} (hg0 : g ≠ 0) (hh0 : h ≠ 0)
    (hgN : g ≤ N) (hhN : h ≤ N) (hg : primePrefixCondition N g ω) (hh : primePrefixCondition N h ω)
    (hne : g ≠ h) (hgF : (finitePrimeFibre A g).Nonempty) (hhF : (finitePrimeFibre A h).Nonempty) :
    terminalPrime A g ≠ terminalPrime A h := by
  intro heq
  have hp : 0 < terminalPrime A g := (terminalPrime_prime A g hgF).pos
  have hgp := finitePrimeFibre_product_mem A g (terminalPrime_mem A g hgF)
  have hhp := finitePrimeFibre_product_mem A h (terminalPrime_mem A h hhF)
  rw [← heq] at hhp
  rcases prefix_divisibility_total hg0 hh0 hgN hhN hg hh with hdiv | hdiv
  · exact nested_terminal_distinct hA hp hdiv hne hgp hhp
  · exact nested_terminal_distinct hA hp hdiv hne.symm hhp hgp

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/FirstPrefixCandidate.lean -/
section
/- # Predictable first-copy prefixes in the finite sample model -/

namespace Erdos12Proof

theorem prefix_condition_congr {N g : ℕ} {ω η : PrimeSample N}
    (hEq : ∀ p : primesThrough (N : ℝ), p.val ≤ g.maxPrimeFac → ω p = η p) :
    primePrefixCondition N g ω ↔ primePrefixCondition N g η := by
  constructor
  · intro h p
    constructor
    · intro hp
      rw [← hEq p hp.le]
      exact (h p).1 hp
    · intro hp
      rw [← hEq p hp.le]
      exact (h p).2 hp
  · intro h p
    constructor
    · intro hp
      rw [hEq p hp.le]
      exact (h p).1 hp
    · intro hp
      rw [hEq p hp.le]
      exact (h p).2 hp

theorem prefix_condition_update_after {N g : ℕ} (ω : PrimeSample N)
    (p : primesThrough (N : ℝ)) (x : Fin (N + 2)) (hgp : g.maxPrimeFac < p.val) :
    primePrefixCondition N g (Function.update ω p x) ↔ primePrefixCondition N g ω := by
  apply prefix_condition_congr
  intro q hq
  have hqp : q ≠ p := by
    intro h
    subst q
    omega
  exact Function.update_of_ne hqp x ω

theorem prefix_condition_update_last {N g : ℕ} {ω : PrimeSample N}
    (h : primePrefixCondition N g ω) (p : primesThrough (N : ℝ)) (x : Fin (N + 2))
    (hp : g.maxPrimeFac = p.val) (hx : g.factorization p.val ≤ x.val) :
    primePrefixCondition N g (Function.update ω p x) := by
  intro q
  by_cases hqp : q = p
  · subst q
    constructor
    · intro hlt
      omega
    · intro _
      simpa only [Function.update_self] using hx
  · simpa only [Function.update_of_ne hqp] using h q

def firstCopyValue (N : ℕ) : Fin (N + 2) := ⟨1, by omega⟩

def FirstPrefixSpec (N : ℕ) (ω : PrimeSample N) (p : primesThrough (N : ℝ)) (g : ℕ) : Prop :=
  2 ≤ g ∧ g ≤ N ∧ g.maxPrimeFac = p.val ∧ g.factorization p.val = 1 ∧
    primePrefixCondition N g (Function.update ω p (firstCopyValue N))

theorem firstPrefixSpec_unique {N g h : ℕ} {ω : PrimeSample N} {p : primesThrough (N : ℝ)}
    (hg : FirstPrefixSpec N ω p g) (hh : FirstPrefixSpec N ω p h) : g = h := by
  obtain ⟨hg2, hgN, hgp, hgf, hgPre⟩ := hg
  obtain ⟨hh2, hhN, hhp, hhf, hhPre⟩ := hh
  apply prefix_same_indices_eq (by omega) (by omega) hgN hhN hgPre hhPre (hgp.trans hhp.symm)
  rw [hgp, hhp, hgf, hhf]

noncomputable def firstPrefixCandidate (N : ℕ) (ω : PrimeSample N) (p : primesThrough (N : ℝ)) : ℕ := by
  classical
  exact if h : ∃ g, FirstPrefixSpec N ω p g then Nat.find h else 0

theorem firstPrefixCandidate_spec {N : ℕ} {ω : PrimeSample N} {p : primesThrough (N : ℝ)}
    (h : ∃ g, FirstPrefixSpec N ω p g) : FirstPrefixSpec N ω p (firstPrefixCandidate N ω p) := by
  classical
  rw [firstPrefixCandidate, dite_eq_left h]
  exact Nat.find_spec h

theorem firstPrefixCandidate_eq {N g : ℕ} {ω : PrimeSample N} {p : primesThrough (N : ℝ)}
    (hg : FirstPrefixSpec N ω p g) : firstPrefixCandidate N ω p = g :=
  firstPrefixSpec_unique (firstPrefixCandidate_spec ⟨g, hg⟩) hg

theorem firstPrefixCandidate_zero {N : ℕ} {ω : PrimeSample N} {p : primesThrough (N : ℝ)}
    (h : ¬∃ g, FirstPrefixSpec N ω p g) : firstPrefixCandidate N ω p = 0 := by
  classical
  rw [firstPrefixCandidate, dite_eq_right h]

theorem firstPrefixCandidate_congr {N : ℕ} {ω η : PrimeSample N} {p : primesThrough (N : ℝ)}
    (h : ∀ g, FirstPrefixSpec N ω p g ↔ FirstPrefixSpec N η p g) :
    firstPrefixCandidate N ω p = firstPrefixCandidate N η p := by
  classical
  by_cases hex : ∃ g, FirstPrefixSpec N ω p g
  · have hs := firstPrefixCandidate_spec hex
    exact (firstPrefixCandidate_eq ((h _).mp hs)).symm
  · have hη : ¬∃ g, FirstPrefixSpec N η p g := by
      rintro ⟨g, hg⟩
      exact hex ⟨g, (h g).mpr hg⟩
    rw [firstPrefixCandidate_zero hex, firstPrefixCandidate_zero hη]

theorem firstPrefixCandidate_update_self (N : ℕ) (ω : PrimeSample N)
    (p : primesThrough (N : ℝ)) (x : Fin (N + 2)) :
    firstPrefixCandidate N (Function.update ω p x) p = firstPrefixCandidate N ω p := by
  apply firstPrefixCandidate_congr
  intro g
  unfold FirstPrefixSpec
  rw [Function.update_idem]

theorem firstPrefixCandidate_is_prefix {N : ℕ} {ω : PrimeSample N} {p : primesThrough (N : ℝ)}
    (h : ∃ g, FirstPrefixSpec N ω p g) (hp : 1 ≤ (ω p).val) :
    primePrefixCondition N (firstPrefixCandidate N ω p) ω := by
  obtain ⟨_, _, hmax, hfactor, hpre⟩ := firstPrefixCandidate_spec h
  have hx : (firstPrefixCandidate N ω p).factorization p.val ≤ (ω p).val := by rwa [hfactor]
  have h := prefix_condition_update_last hpre p (ω p) hmax hx
  simpa only [Function.update_idem, Function.update_eq_self] using h

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/FirstPrefixPredictability.lean -/
section
/- # Future coordinates do not affect a first-copy candidate -/

namespace Erdos12Proof

theorem firstPrefixSpec_update_after {N g : ℕ} (ω : PrimeSample N)
    (p q : primesThrough (N : ℝ)) (x : Fin (N + 2)) (hpq : p.val < q.val) :
    FirstPrefixSpec N (Function.update ω q x) p g ↔ FirstPrefixSpec N ω p g := by
  have hpne : p ≠ q := by intro h; subst q; exact (Nat.lt_irrefl p.val) hpq
  have hcomm : Function.update (Function.update ω q x) p (firstCopyValue N) =
      Function.update (Function.update ω p (firstCopyValue N)) q x :=
    Function.update_comm hpne.symm x (firstCopyValue N) ω
  constructor
  · rintro ⟨hg2, hgN, hmax, hfactor, hpre⟩
    refine ⟨hg2, hgN, hmax, hfactor, ?_⟩
    rw [hcomm] at hpre
    exact (prefix_condition_update_after _ q x (by omega)).mp hpre
  · rintro ⟨hg2, hgN, hmax, hfactor, hpre⟩
    refine ⟨hg2, hgN, hmax, hfactor, ?_⟩
    rw [hcomm]
    exact (prefix_condition_update_after _ q x (by omega)).mpr hpre

theorem firstPrefixCandidate_update_after {N : ℕ} (ω : PrimeSample N)
    (p q : primesThrough (N : ℝ)) (x : Fin (N + 2)) (hpq : p.val < q.val) :
    firstPrefixCandidate N (Function.update ω q x) p = firstPrefixCandidate N ω p := by
  apply firstPrefixCandidate_congr
  intro g
  exact firstPrefixSpec_update_after ω p q x hpq

theorem prefix_first_candidate_eq {N g : ℕ} {ω : PrimeSample N} (hg : 2 ≤ g) (hgN : g ≤ N)
    (hpre : primePrefixCondition N g ω) (p : primesThrough (N : ℝ))
    (hmax : g.maxPrimeFac = p.val) (hfactor : g.factorization p.val = 1) :
    firstPrefixCandidate N ω p = g := by
  apply firstPrefixCandidate_eq
  refine ⟨hg, hgN, hmax, hfactor, ?_⟩
  apply prefix_condition_update_last hpre p (firstCopyValue N) hmax
  simp only [firstCopyValue, hfactor, le_refl]

theorem firstPrefixCandidate_spec_of_ne_zero {N : ℕ} {ω : PrimeSample N}
    {p : primesThrough (N : ℝ)} (h : firstPrefixCandidate N ω p ≠ 0) :
    FirstPrefixSpec N ω p (firstPrefixCandidate N ω p) := by
  classical
  by_cases hex : ∃ g, FirstPrefixSpec N ω p g
  · exact firstPrefixCandidate_spec hex
  · exact (h (firstPrefixCandidate_zero hex)).elim

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/FirstCopyScores.lean -/
section
/- # First-copy scores and their predictable-coordinate expectations -/

namespace Erdos12Proof

theorem prefixScore_zero (A : Finset ℕ) : prefixScore A 0 = 0 := by
  simp only [prefixScore, Nat.maxPrimeFac_zero, Nat.cast_zero, mul_zero, Real.log_zero, zero_mul]

theorem prefixScore_nonneg (A : Finset ℕ) (g : ℕ) : 0 ≤ prefixScore A g := by
  by_cases hg0 : g = 0
  · subst g
    rw [prefixScore_zero]
  · have hmax : 1 ≤ g.maxPrimeFac := by
      by_cases hg1 : g = 1
      · simp only [hg1, Nat.maxPrimeFac_one, le_refl]
      · exact (Nat.prime_maxPrimeFac_of_one_lt (by omega)).one_lt.le
    have hreal : (1 : ℝ) ≤ 2 * (g.maxPrimeFac : ℝ) := by exact_mod_cast (show 1 ≤ 2 * g.maxPrimeFac by omega)
    exact mul_nonneg (Real.log_nonneg hreal) (harmonic_nonneg _)

theorem first_candidate_score_bound (A : Finset ℕ) (hA : PropertyP (A : Set ℕ)) (N : ℕ)
    (ω : PrimeSample N) (p : primesThrough (N : ℝ)) :
    prefixScore A (firstPrefixCandidate N ω p) ≤ primeTailConstant := by
  by_cases hzero : firstPrefixCandidate N ω p = 0
  · rw [hzero, prefixScore_zero]
    exact primeTailConstant_pos.le
  · have hspec := firstPrefixCandidate_spec_of_ne_zero hzero
    exact prefixScore_uniform A hA (by have := hspec.1; omega)

noncomputable def firstCopyScore (N : ℕ) (A : Finset ℕ) (ω : PrimeSample N)
    (p : primesThrough (N : ℝ)) : ℝ :=
  if 1 ≤ (ω p).val then prefixScore A (firstPrefixCandidate N ω p) else 0

noncomputable def firstCopyScoreSum (N : ℕ) (A : Finset ℕ) (ω : PrimeSample N) : ℝ :=
  ∑ p : primesThrough (N : ℝ), firstCopyScore N A ω p

theorem firstCopyScore_nonneg (N : ℕ) (A : Finset ℕ) (ω : PrimeSample N)
    (p : primesThrough (N : ℝ)) : 0 ≤ firstCopyScore N A ω p := by
  unfold firstCopyScore
  split_ifs
  · exact prefixScore_nonneg _ _
  · exact le_refl _

theorem firstCopyScore_bound (N : ℕ) (A : Finset ℕ) (hA : PropertyP (A : Set ℕ))
    (ω : PrimeSample N) (p : primesThrough (N : ℝ)) : firstCopyScore N A ω p ≤ primeTailConstant := by
  unfold firstCopyScore
  split_ifs
  · exact first_candidate_score_bound A hA N ω p
  · exact primeTailConstant_pos.le

theorem expected_first_copy_score (N : ℕ) (A : Finset ℕ) (p : primesThrough (N : ℝ)) :
    weightedSum (primeSampleWeight N) (fun ω => firstCopyScore N A ω p) =
      (1 / (p.val : ℝ)) * weightedSum (primeSampleWeight N)
        (fun ω => prefixScore A (firstPrefixCandidate N ω p)) := by
  have h := finiteGeometric_tail_pairing (fun p : primesThrough (N : ℝ) => (p.val : ℝ))
    (N + 1) p 1 (by omega) (fun ω => prefixScore A (firstPrefixCandidate N ω p)) (by
      intro ω x
      rw [firstPrefixCandidate_update_self])
  simpa only [pow_one, firstCopyScore, weightedSum, primeSampleWeight, finiteGeometricProductWeight] using h

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/RepeatedCopyExpectation.lean -/
section
/- # Expected cost of second and later copies of a prime coordinate -/

namespace Erdos12Proof

theorem truncated_repeated_copy_identity (p : ℝ) (cap : ℕ) :
    (∑ x : Fin (cap + 1), truncatedGeometricWeight p cap x * ((x.val - 1 : ℕ) : ℝ)) =
      ∑ a ∈ Finset.Icc 2 cap, (1 / p) ^ a := by
  have hcount (x : Fin (cap + 1)) : ((x.val - 1 : ℕ) : ℝ) =
      ∑ a ∈ Finset.Icc 2 cap, if a ≤ x.val then (1 : ℝ) else 0 := by
    have hx : x.val ≤ cap := by omega
    have hf : (Finset.Icc 2 cap).filter (fun a => a ≤ x.val) = Finset.Icc 2 x.val := by
      apply Finset.ext
      intro a
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [Finset.sum_boole, hf, Nat.card_Icc]
    congr 1
  simp only [hcount, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [mul_ite, mul_one, mul_zero]
  exact truncatedGeometricWeight_tail p cap a (Finset.mem_Icc.mp ha).2

theorem truncated_repeated_copy_bound {p : ℝ} (hp : 1 < p) (cap : ℕ) :
    (∑ x : Fin (cap + 1), truncatedGeometricWeight p cap x * ((x.val - 1 : ℕ) : ℝ)) ≤
      1 / (p * (p - 1)) := by
  rw [truncated_repeated_copy_identity]
  obtain ⟨hq0, hq1⟩ := geometric_ratio_bounds hp
  have hden : 0 < 1 - 1 / p := sub_pos.mpr hq1
  have hp0 : p ≠ 0 := (by linarith : 0 < p).ne'
  have hp1 : p - 1 ≠ 0 := (sub_pos.mpr hp).ne'
  by_cases hcap : 0 < cap
  · have hs := hasSum_geometric_of_lt_one hq0 hq1
    have hbound := hs.summable.sum_le_tsum (Finset.range (cap + 1)) (fun a _ => pow_nonneg hq0 a)
    rw [hs.tsum_eq] at hbound
    have hsplit := Finset.sum_range_add_sum_Ico (fun a => (1 / p) ^ a) (show 2 ≤ cap + 1 by omega)
    have hIco : Finset.Ico 2 (cap + 1) = Finset.Icc 2 cap := by
      apply Finset.ext
      intro a
      simp only [Finset.mem_Ico, Finset.mem_Icc]
      omega
    rw [hIco] at hsplit
    have htwo : (∑ a ∈ Finset.range 2, (1 / p) ^ a) = 1 + 1 / p := by
      norm_num [Finset.sum_range_succ]
    rw [htwo] at hsplit
    have hid : (1 - 1 / p)⁻¹ - 1 - 1 / p = 1 / (p * (p - 1)) := by
      field_simp
      ring
    linarith
  · have hc0 : cap = 0 := by omega
    subst cap
    simp only [Finset.Icc_eq_empty_of_lt (by decide : (0 : ℕ) < 2), Finset.sum_empty]
    exact (one_div_pos.mpr (mul_pos (by linarith) (sub_pos.mpr hp))).le

theorem finite_prime_repeated_cost_bound (R : Finset ℕ) (hR : ∀ p ∈ R, p.Prime) :
    (∑ p ∈ R, (1 / ((p : ℝ) * ((p : ℝ) - 1)))) ≤ 2 := by
  have hterm (p : ℕ) (hp : p ∈ R) : 1 / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 2 / (p : ℝ) ^ 2 := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hR p hp).two_le
    have hpos : 0 < (p : ℝ) := by linarith
    apply (div_le_div_iff₀ (mul_pos hpos (by linarith)) (sq_pos_of_pos hpos)).mpr
    nlinarith
  calc
    _ ≤ ∑ p ∈ R, 2 / (p : ℝ) ^ 2 := Finset.sum_le_sum (fun p hp => hterm p hp)
    _ = 2 * ∑ p ∈ R, 1 / (p : ℝ) ^ 2 := by rw [Finset.mul_sum]; simp only [mul_one_div]
    _ ≤ 2 * (2 / (2 : ℝ)) := mul_le_mul_of_nonneg_left
      (finite_reciprocal_square_tail R (by decide : 0 < (2 : ℕ)) (fun p hp => (hR p hp).two_le)) (by norm_num)
    _ = _ := by norm_num

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/RepeatedPrimeCopies.lean -/
section
/- # A uniform expected budget for repeated prime copies -/

namespace Erdos12Proof

noncomputable def repeatedPrimeCopies (N : ℕ) (ω : PrimeSample N) : ℝ :=
  ∑ p : primesThrough (N : ℝ), ((ω p).val - 1 : ℕ)

theorem repeated_prime_coordinate_mean (N : ℕ) (p : primesThrough (N : ℝ)) :
    weightedSum (primeSampleWeight N) (fun ω => (((ω p).val - 1 : ℕ) : ℝ)) =
      ∑ x : Fin (N + 2), truncatedGeometricWeight (p.val : ℝ) (N + 1) x * ((x.val - 1 : ℕ) : ℝ) := by
  let w := fun p : primesThrough (N : ℝ) => truncatedGeometricWeight (p.val : ℝ) (N + 1)
  have hone : weightedSum (productWeight w) (fun _ => 1) = 1 := by
    simp only [weightedSum, mul_one]
    exact productWeight_mass w (fun p => truncatedGeometricWeight_sum (p.val : ℝ) (N + 1))
  have h := weightedSum_coordinate_pairing w p (truncatedGeometricWeight_sum (p.val : ℝ) (N + 1))
    (fun x => ((x.val - 1 : ℕ) : ℝ)) (fun _ => 1) (by intro ω x; rfl)
  rw [hone, mul_one] at h
  simpa only [weightedSum, primeSampleWeight, finiteGeometricProductWeight, mul_one, w] using h

theorem expected_repeated_prime_copies (N : ℕ) :
    weightedSum (primeSampleWeight N) (repeatedPrimeCopies N) ≤ 2 := by
  have hprime (p : primesThrough (N : ℝ)) : p.val.Prime :=
    ((mem_primesThrough (Nat.cast_nonneg N)).mp p.property).1
  have hterm (p : primesThrough (N : ℝ)) :
      weightedSum (primeSampleWeight N) (fun ω => (((ω p).val - 1 : ℕ) : ℝ)) ≤
        1 / ((p.val : ℝ) * ((p.val : ℝ) - 1)) := by
    rw [repeated_prime_coordinate_mean]
    exact truncated_repeated_copy_bound (by exact_mod_cast (hprime p).one_lt) (N + 1)
  unfold repeatedPrimeCopies
  rw [weightedSum_finite_sum]
  calc
    _ ≤ ∑ p : primesThrough (N : ℝ), 1 / ((p.val : ℝ) * ((p.val : ℝ) - 1)) :=
      Finset.sum_le_sum (fun p _ => hterm p)
    _ = ∑ p ∈ primesThrough (N : ℝ), 1 / ((p : ℝ) * ((p : ℝ) - 1)) :=
      Finset.sum_coe_sort (primesThrough (N : ℝ)) (fun p : ℕ => 1 / ((p : ℝ) * ((p : ℝ) - 1)))
    _ ≤ 2 := finite_prime_repeated_cost_bound _
      (fun p hp => ((mem_primesThrough (Nat.cast_nonneg N)).mp hp).1)

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/PrefixCopyDecomposition.lean -/
section
/- # Separating first-copy and repeated-copy prefix scores -/

namespace Erdos12Proof

theorem real_card_eq_subtype_fibres {α β : Type*} [DecidableEq β]
    (S : Finset α) (T : Finset β) (f : α → β) (hmap : ∀ a ∈ S, f a ∈ T) :
    (S.card : ℝ) = ∑ b : T, ((S.filter (fun a => f a = b.val)).card : ℝ) := by
  classical
  rw [Finset.sum_coe_sort T (fun b : β => ((S.filter (fun a => f a = b)).card : ℝ))]
  exact_mod_cast Finset.card_eq_sum_card_fiberwise hmap

noncomputable def activePrefixIndices (N : ℕ) (ω : PrimeSample N) : Finset ℕ :=
  (Finset.Icc 2 N).filter (fun g => primePrefixCondition N g ω)

theorem activePrefixIndices_bounds {N g : ℕ} {ω : PrimeSample N} (hg : g ∈ activePrefixIndices N ω) :
    2 ≤ g ∧ g ≤ N ∧ primePrefixCondition N g ω := by
  have h := Finset.mem_filter.mp hg
  exact ⟨(Finset.mem_Icc.mp h.1).1, (Finset.mem_Icc.mp h.1).2, h.2⟩

theorem activePrefixIndices_prime {N g : ℕ} {ω : PrimeSample N} (hg : g ∈ activePrefixIndices N ω) :
    g.maxPrimeFac ∈ primesThrough (N : ℝ) := by
  obtain ⟨hg2, hgN, _⟩ := activePrefixIndices_bounds hg
  exact (mem_primesThrough (Nat.cast_nonneg N)).mpr
    ⟨Nat.prime_maxPrimeFac_of_one_lt (by omega), by exact_mod_cast Nat.maxPrimeFac_le.trans hgN⟩

theorem activePrefixIndices_multiplicity_pos {N g : ℕ} {ω : PrimeSample N}
    (hg : g ∈ activePrefixIndices N ω) : 0 < g.factorization g.maxPrimeFac := by
  have hg2 := (activePrefixIndices_bounds hg).1
  exact (Nat.prime_maxPrimeFac_of_one_lt (by omega)).factorization_pos_of_dvd (by omega) Nat.maxPrimeFac_dvd

noncomputable def firstCopyScoreAt (N : ℕ) (A : Finset ℕ) (ω : PrimeSample N) (p : ℕ) : ℝ :=
  if hp : p ∈ primesThrough (N : ℝ) then firstCopyScore N A ω ⟨p, hp⟩ else 0

theorem firstCopyScoreSum_eq (N : ℕ) (A : Finset ℕ) (ω : PrimeSample N) :
    firstCopyScoreSum N A ω = ∑ p ∈ primesThrough (N : ℝ), firstCopyScoreAt N A ω p := by
  classical
  rw [← Finset.sum_coe_sort (primesThrough (N : ℝ)) (firstCopyScoreAt N A ω)]
  apply Finset.sum_congr rfl
  intro p _
  simp only [firstCopyScoreAt, dite_eq_left p.property]

theorem first_prefix_score_sum (N : ℕ) (A : Finset ℕ) (ω : PrimeSample N) :
    (∑ g ∈ (activePrefixIndices N ω).filter (fun g => g.factorization g.maxPrimeFac = 1), prefixScore A g) ≤
      firstCopyScoreSum N A ω := by
  classical
  let G := (activePrefixIndices N ω).filter (fun g => g.factorization g.maxPrimeFac = 1)
  have hmap : ∀ g ∈ G, g.maxPrimeFac ∈ primesThrough (N : ℝ) := fun g hg =>
    activePrefixIndices_prime (Finset.mem_filter.mp hg).1
  have hfibre (p : ℕ) (hp : p ∈ primesThrough (N : ℝ)) :
      (∑ g ∈ G.filter (fun g => g.maxPrimeFac = p), prefixScore A g) ≤ firstCopyScoreAt N A ω p := by
    let pi : primesThrough (N : ℝ) := ⟨p, hp⟩
    by_cases hhit : 1 ≤ (ω pi).val
    · have hsub : G.filter (fun g => g.maxPrimeFac = p) ⊆ {firstPrefixCandidate N ω pi} := by
        intro g hg
        obtain ⟨hgG, hmax⟩ := Finset.mem_filter.mp hg
        obtain ⟨hgActive, hmult⟩ := Finset.mem_filter.mp hgG
        obtain ⟨hg2, hgN, hpre⟩ := activePrefixIndices_bounds hgActive
        have hfactor : g.factorization p = 1 := by simpa only [hmax] using hmult
        have heq := prefix_first_candidate_eq hg2 hgN hpre pi hmax hfactor
        exact Finset.mem_singleton.mpr heq.symm
      have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun g _ _ => prefixScore_nonneg A g)
      dsimp only [pi] at hhit hle
      simpa only [Finset.sum_singleton, firstCopyScoreAt, dite_eq_left hp, firstCopyScore, ite_eq_left hhit] using hle
    · have hempty : G.filter (fun g => g.maxPrimeFac = p) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro g hg
        obtain ⟨hgG, hmax⟩ := Finset.mem_filter.mp hg
        obtain ⟨hgActive, hmult⟩ := Finset.mem_filter.mp hgG
        have hpre := (activePrefixIndices_bounds hgActive).2.2
        have hbound := (hpre pi).2 hmax.symm
        change g.factorization p ≤ (ω pi).val at hbound
        have hfactor : g.factorization p = 1 := by simpa only [hmax] using hmult
        exact hhit (hfactor ▸ hbound)
      dsimp only [pi] at hhit
      simp only [hempty, Finset.sum_empty, firstCopyScoreAt, dite_eq_left hp, firstCopyScore, ite_eq_right hhit, le_refl]
  rw [firstCopyScoreSum_eq]
  calc
    _ = ∑ p ∈ primesThrough (N : ℝ), ∑ g ∈ G.filter (fun g => g.maxPrimeFac = p), prefixScore A g :=
      (Finset.sum_fiberwise_of_maps_to hmap (prefixScore A)).symm
    _ ≤ _ := Finset.sum_le_sum (fun p hp => hfibre p hp)

theorem repeated_prefix_cardinality (N : ℕ) (ω : PrimeSample N) :
    (((activePrefixIndices N ω).filter (fun g => g.factorization g.maxPrimeFac ≠ 1)).card : ℝ) ≤
      repeatedPrimeCopies N ω := by
  classical
  let G := (activePrefixIndices N ω).filter (fun g => g.factorization g.maxPrimeFac ≠ 1)
  have hmap : ∀ g ∈ G, g.maxPrimeFac ∈ primesThrough (N : ℝ) := fun g hg =>
    activePrefixIndices_prime (Finset.mem_filter.mp hg).1
  have hfibre (p : ℕ) (hp : p ∈ primesThrough (N : ℝ)) :
      (G.filter (fun g => g.maxPrimeFac = p)).card ≤ (ω ⟨p, hp⟩).val - 1 := by
    let S := G.filter (fun g => g.maxPrimeFac = p)
    let pi : primesThrough (N : ℝ) := ⟨p, hp⟩
    have hinj : Set.InjOn (fun g : ℕ => g.factorization p) S := by
      intro g hg h hh heq
      obtain ⟨hgG, hgmax⟩ := Finset.mem_filter.mp hg
      obtain ⟨hhG, hhmax⟩ := Finset.mem_filter.mp hh
      obtain ⟨hg2, hgN, hgpre⟩ := activePrefixIndices_bounds (Finset.mem_filter.mp hgG).1
      obtain ⟨hh2, hhN, hhpre⟩ := activePrefixIndices_bounds (Finset.mem_filter.mp hhG).1
      apply prefix_same_indices_eq (by omega) (by omega) hgN hhN hgpre hhpre (hgmax.trans hhmax.symm)
      simpa only [hgmax, hhmax] using heq
    have hsub : S.image (fun g : ℕ => g.factorization p) ⊆ Finset.Icc 2 (ω pi).val := by
      intro a ha
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨hgG, hmax⟩ := Finset.mem_filter.mp hg
      obtain ⟨hgActive, hnot⟩ := Finset.mem_filter.mp hgG
      have hpos := activePrefixIndices_multiplicity_pos hgActive
      have hpre := (activePrefixIndices_bounds hgActive).2.2
      have hbound := (hpre pi).2 hmax.symm
      change g.factorization p ≤ (ω pi).val at hbound
      rw [hmax] at hpos hnot
      exact Finset.mem_Icc.mpr ⟨by omega, hbound⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_of_injOn hinj, Nat.card_Icc] at hcard
    change S.card ≤ (ω pi).val - 1
    omega
  have hcardR : (G.card : ℝ) = ∑ p : primesThrough (N : ℝ),
      ((G.filter (fun g => g.maxPrimeFac = p.val)).card : ℝ) := by
    exact real_card_eq_subtype_fibres G (primesThrough (N : ℝ)) Nat.maxPrimeFac hmap
  change (G.card : ℝ) ≤ _
  rw [hcardR]
  calc
    _ ≤ ∑ p : primesThrough (N : ℝ), (((ω p).val - 1 : ℕ) : ℝ) := by
      exact Finset.sum_le_sum (fun p _ => by exact_mod_cast hfibre p.val p.property)
    _ = _ := rfl

theorem prefix_score_copy_decomposition (N : ℕ) (A : Finset ℕ) (hA : PropertyP (A : Set ℕ)) (ω : PrimeSample N) :
    (∑ g ∈ Finset.Icc 2 N, if primePrefixCondition N g ω then prefixScore A g else 0) ≤
      firstCopyScoreSum N A ω + primeTailConstant * repeatedPrimeCopies N ω := by
  classical
  let G := activePrefixIndices N ω
  have hsplit := Finset.sum_filter_add_sum_filter_not G (fun g => g.factorization g.maxPrimeFac = 1) (prefixScore A)
  have hfirst := first_prefix_score_sum N A ω
  have hlater : (∑ g ∈ G.filter (fun g => g.factorization g.maxPrimeFac ≠ 1), prefixScore A g) ≤
      primeTailConstant * repeatedPrimeCopies N ω := by
    calc
      _ ≤ ∑ _g ∈ G.filter (fun g => g.factorization g.maxPrimeFac ≠ 1), primeTailConstant := by
        apply Finset.sum_le_sum
        intro g hg
        have hg2 := (activePrefixIndices_bounds (Finset.mem_filter.mp hg).1).1
        exact prefixScore_uniform A hA (by omega)
      _ = primeTailConstant * ((G.filter (fun g => g.factorization g.maxPrimeFac ≠ 1)).card : ℝ) := by
        simp only [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (repeated_prefix_cardinality N ω) primeTailConstant_pos.le
  have hsum : (∑ g ∈ Finset.Icc 2 N, if primePrefixCondition N g ω then prefixScore A g else 0) =
      ∑ g ∈ G, prefixScore A g := by
    dsimp only [G, activePrefixIndices]
    rw [Finset.sum_filter]
  rw [hsum]
  linarith

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/FirstCopyReduction.lean -/
section
/- # Removing the uniformly bounded repeated-copy contribution -/

namespace Erdos12Proof

theorem expectedPrefixScore_le_first (N : ℕ) (A : Finset ℕ) (hA : PropertyP (A : Set ℕ)) :
    expectedPrefixScore N A ≤ weightedSum (primeSampleWeight N) (firstCopyScoreSum N A) +
      2 * primeTailConstant := by
  have h := weightedSum_mono (primeSampleWeight N) (primeSampleWeight_nonneg N)
    (fun ω => prefix_score_copy_decomposition N A hA ω)
  change expectedPrefixScore N A ≤ _ at h
  have hsplit : weightedSum (primeSampleWeight N)
      (fun ω => firstCopyScoreSum N A ω + primeTailConstant * repeatedPrimeCopies N ω) =
      weightedSum (primeSampleWeight N) (firstCopyScoreSum N A) +
        primeTailConstant * weightedSum (primeSampleWeight N) (repeatedPrimeCopies N) := by
    simp only [weightedSum, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro ω _
    ring
  rw [hsplit] at h
  have hcopies := mul_le_mul_of_nonneg_left (expected_repeated_prime_copies N) primeTailConstant_pos.le
  linarith

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/SchedulingBudgets.lean -/
section
/- # Deterministic budgets used by the adaptive prefix schedule -/

namespace Erdos12Proof

theorem doubling_ratio_budget (S : Finset ℕ) (a : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (ha : ∀ i ∈ S, 0 ≤ a i ∧ a i ≤ B)
    (hdouble : ∀ i ∈ S, ∀ j ∈ S, i < j → 2 * a i ≤ a j) :
    (∑ i ∈ S, a i) ≤ 2 * B := by
  classical
  induction S using Finset.strongInductionOn generalizing B with
  | _ S ih =>
      by_cases hne : S.Nonempty
      · let m := S.max' hne
        have hm : m ∈ S := Finset.max'_mem S hne
        have hsmall : (∑ i ∈ S.erase m, a i) ≤ 2 * (B / 2) := by
          apply ih (S.erase m) (Finset.erase_ssubset hm) (B / 2) (by positivity)
          · intro i hi
            obtain ⟨him, hiS⟩ := Finset.mem_erase.mp hi
            have him' : i < m := lt_of_le_of_ne (Finset.le_max' S i hiS) him
            have hd := hdouble i hiS m hm him'
            exact ⟨(ha i hiS).1, by linarith [(ha m hm).2]⟩
          · intro i hi j hj hij
            exact hdouble i (Finset.mem_erase.mp hi).2 j (Finset.mem_erase.mp hj).2 hij
        have hs := Finset.sum_erase_add S a hm
        linarith [(ha m hm).2]
      · have hzero : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        simp only [hzero, Finset.sum_empty]
        linarith

theorem finite_stage_budget (S : Finset ℕ) :
    (∑ k ∈ S, (1 / 2 : ℝ) ^ k * (1 + (k : ℝ))) ≤ 4 := by
  have h := hasSum_stage_budget.summable.sum_le_tsum S (fun k _ => by positivity)
  simpa only [hasSum_stage_budget.tsum_eq] using h

theorem prime_log_sum_le (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime) (P : ℝ)
    (hP : 0 ≤ P) (hupper : ∀ r ∈ S, (r : ℝ) ≤ P) :
    (∑ r ∈ S, Real.log (r : ℝ) / r) ≤ primeLogReciprocalSum P := by
  have hsub : S ⊆ primesThrough P := fun r hr => (mem_primesThrough hP).mpr ⟨hS r hr, hupper r hr⟩
  apply Finset.sum_le_sum_of_subset_of_nonneg hsub
  intro r hr _
  have hrPrime := ((mem_primesThrough hP).mp hr).1
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hrPrime.one_lt.le)) (Nat.cast_nonneg r)

theorem predictable_prime_budget (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime)
    (P : ℝ) (hP : 2 ≤ P) (pending : ℕ → ℝ)
    (hupper : ∀ r ∈ S, (r : ℝ) ≤ P) (hlower : ∀ r ∈ S, P ≤ pending r) :
    (∑ r ∈ S, (1 / (r : ℝ)) * (Real.log r / Real.log (pending r))) ≤ primeLogWeightConstant := by
  have hP0 : 0 < P := by linarith
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hterm (r : ℕ) (hr : r ∈ S) :
      (1 / (r : ℝ)) * (Real.log r / Real.log (pending r)) ≤
        (Real.log r / r) / Real.log P := by
    have hlogr : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg (by exact_mod_cast (hS r hr).one_lt.le)
    have hlogPending := Real.log_le_log hP0 (hlower r hr)
    calc
      _ = (Real.log r / r) / Real.log (pending r) := by ring
      _ ≤ _ := div_le_div_of_nonneg_left (div_nonneg hlogr (Nat.cast_nonneg r)) hlogP hlogPending
  calc
    _ ≤ ∑ r ∈ S, (Real.log r / r) / Real.log P := Finset.sum_le_sum (fun r hr => hterm r hr)
    _ = (∑ r ∈ S, Real.log r / r) / Real.log P := (Finset.sum_div _ _ _).symm
    _ ≤ primeLogReciprocalSum P / Real.log P :=
      div_le_div_of_nonneg_right (prime_log_sum_le S hS P hP0.le hupper) hlogP.le
    _ ≤ (primeLogWeightConstant * Real.log P) / Real.log P :=
      div_le_div_of_nonneg_right (primeLogWeightConstant_bound hP) hlogP.le
    _ = _ := mul_div_cancel_right₀ _ hlogP.ne'

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/DelayBudget.lean -/
section
/- # A uniform reciprocal-prime budget during a delayed stage -/

namespace Erdos12Proof

noncomputable def primeWindowConstant : ℝ := Classical.choose prime_reciprocal_window_bound

theorem primeWindowConstant_pos : 0 < primeWindowConstant :=
  (Classical.choose_spec prime_reciprocal_window_bound).1

theorem prime_window_bound (x y : ℝ) (hx : 2 ≤ x) (hy : 2 ≤ y) :
    primeReciprocalSum y - primeReciprocalSum x ≤ primeWindowConstant +
      Real.log (Real.log y) - Real.log (Real.log x) :=
  (Classical.choose_spec prime_reciprocal_window_bound).2 x y hx hy

theorem prime_power_window_budget (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (P : ℝ) (hP : 4 ≤ P) (m : ℕ) (hm : 1 ≤ m)
    (hinterval : ∀ p ∈ S, P ≤ (p : ℝ) ∧ (p : ℝ) ≤ P ^ m) :
    harmonic S ≤ primeWindowConstant + Real.log (2 * (m : ℝ)) := by
  have hP0 : 0 < P := by linarith
  have hP1 : 1 ≤ P := by linarith
  have hPm : P ≤ P ^ m := by
    simpa only [pow_one] using pow_le_pow_right₀ hP1 hm
  have hx2 : 2 ≤ P / 2 := by linarith
  have hy2 : 2 ≤ P ^ m := by linarith
  have hxy : P / 2 ≤ P ^ m := by linarith
  have hsub : S ⊆ primesThrough (P ^ m) \ primesThrough (P / 2) := by
    intro p hp
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · exact (mem_primesThrough (by linarith : 0 ≤ P ^ m)).mpr ⟨hS p hp, (hinterval p hp).2⟩
    · intro hpx
      have hpx' := ((mem_primesThrough (by linarith : 0 ≤ P / 2)).mp hpx).2
      linarith [(hinterval p hp).1]
  have hmass : harmonic S ≤ primeReciprocalSum (P ^ m) - primeReciprocalSum (P / 2) := by
    calc
      _ ≤ harmonic (primesThrough (P ^ m) \ primesThrough (P / 2)) := harmonic_mono hsub
      _ = _ := by
        exact eq_sub_iff_add_eq.mpr
          (Finset.sum_sdiff (f := fun p : ℕ => (1 / p : ℝ)) (primesThrough_mono hxy))
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hlogX : 0 < Real.log (P / 2) := Real.log_pos (by linarith)
  have hlogY : 0 < Real.log (P ^ m) := Real.log_pos (by linarith)
  have hlogFour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hlogP4 := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hP
  rw [hlogFour] at hlogP4
  have hlogXeq : Real.log (P / 2) = Real.log P - Real.log 2 :=
    Real.log_div hP0.ne' (by norm_num)
  have hloghalf : Real.log P ≤ 2 * Real.log (P / 2) := by linarith
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlogmul : Real.log (P ^ m) ≤ (2 * (m : ℝ)) * Real.log (P / 2) := by
    rw [Real.log_pow]
    nlinarith [mul_le_mul_of_nonneg_left hloghalf (by linarith : (0 : ℝ) ≤ m)]
  have hlogs := Real.log_le_log hlogY hlogmul
  rw [Real.log_mul (by positivity) hlogX.ne'] at hlogs
  have hwindow := prime_window_bound (P / 2) (P ^ m) hx2 hy2
  linarith

noncomputable def primeDelayBudgetConstant : ℝ :=
  primeWindowConstant + Real.log (2 * ((primeTailExponent + 1 : ℕ) : ℝ))

theorem primeDelayBudgetConstant_pos : 0 < primeDelayBudgetConstant := by
  have hm : 1 < 2 * ((primeTailExponent + 1 : ℕ) : ℝ) := by
    have h := primeTailExponent_ge_three
    exact_mod_cast (show 1 < 2 * (primeTailExponent + 1) by omega)
  exact add_pos primeWindowConstant_pos (Real.log_pos hm)

theorem delay_prime_budget (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (P : ℝ) (hP : 4 ≤ P)
    (hinterval : ∀ p ∈ S, P ≤ (p : ℝ) ∧ (p : ℝ) ≤ P ^ (primeTailExponent + 1)) :
    harmonic S ≤ primeDelayBudgetConstant :=
  prime_power_window_budget S hS P hP (primeTailExponent + 1) (by omega) hinterval

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/PrefixSchedule.lean -/
section
/- # The finite adaptive schedule for first-copy prefix scores -/

namespace Erdos12Proof

structure PrefixGuard where
  prime : ℕ
  sourcePrefix : ℕ

structure PrefixScheduleState where
  guards : Finset ℕ
  sources : ℕ → ℕ
  pending : Option PrefixGuard
  readyAt : ℕ
  delayGuards : Finset ℕ
  delayStart : ℕ

def initialPrefixSchedule : PrefixScheduleState where
  guards := ∅
  sources := fun _ => 0
  pending := none
  readyAt := 4
  delayGuards := ∅
  delayStart := 0

def primeHit (N : ℕ) (ω : PrimeSample N) (r : ℕ) : Prop :=
  ∃ p : primesThrough (N : ℝ), p.val = r ∧ 1 ≤ (ω p).val

noncomputable def proposedPrefixGuard (N : ℕ) (A : Finset ℕ) (ω : PrimeSample N) (r : ℕ) :
    Option PrefixGuard := by
  classical
  exact if hr : r ∈ primesThrough (N : ℝ) then
    let g := firstPrefixCandidate N ω ⟨r, hr⟩
    if 2 ≤ g ∧ (finitePrimeFibre A g).Nonempty then some ⟨terminalPrime A g, g⟩ else none
  else none

def choosePendingGuard (old : Option PrefixGuard) (new : PrefixGuard) : PrefixGuard :=
  match old with
  | none => new
  | some g => if g.prime ≤ new.prime then g else new

noncomputable def activatePrefixGuard (s : PrefixScheduleState) (g : PrefixGuard) : PrefixScheduleState where
  guards := insert g.prime s.guards
  sources := Function.update s.sources g.prime g.sourcePrefix
  pending := none
  readyAt := primeModulus (insert g.prime s.guards) ^ primeTailExponent
  delayGuards := s.guards
  delayStart := g.prime

noncomputable def recordPrefixGuard (s : PrefixScheduleState) (r : ℕ) (g : PrefixGuard) : PrefixScheduleState :=
  let chosen := choosePendingGuard s.pending g
  if chosen.prime ≤ r then activatePrefixGuard s chosen
  else { s with pending := some chosen }

noncomputable def processReadyPrefix (N : ℕ) (A : Finset ℕ) (ω : PrimeSample N)
    (r : ℕ) (s : PrefixScheduleState) : PrefixScheduleState := by
  classical
  exact if primeHit N ω r then
    match proposedPrefixGuard N A ω r with
    | none => s
    | some g => recordPrefixGuard s r g
  else s

noncomputable def prefixScheduleStep (N : ℕ) (A : Finset ℕ) (ω : PrimeSample N)
    (r : ℕ) (s : PrefixScheduleState) : PrefixScheduleState :=
  if r < s.readyAt then s else
    match s.pending with
    | none => processReadyPrefix N A ω r s
    | some g => if g.prime ≤ r then activatePrefixGuard s g else processReadyPrefix N A ω r s

noncomputable def prefixSchedule (N : ℕ) (A : Finset ℕ) (ω : PrimeSample N) : ℕ → PrefixScheduleState
  | 0 => initialPrefixSchedule
  | r + 1 => prefixScheduleStep N A ω r (prefixSchedule N A ω r)

theorem primeHit_update_after {N r : ℕ} (ω : PrimeSample N) (q : primesThrough (N : ℝ))
    (x : Fin (N + 2)) (hrq : r < q.val) :
    primeHit N (Function.update ω q x) r ↔ primeHit N ω r := by
  constructor
  · rintro ⟨p, hpr, hp⟩
    have hpq : p ≠ q := by intro h; subst p; omega
    exact ⟨p, hpr, by simpa only [Function.update_of_ne hpq] using hp⟩
  · rintro ⟨p, hpr, hp⟩
    have hpq : p ≠ q := by intro h; subst p; omega
    exact ⟨p, hpr, by simpa only [Function.update_of_ne hpq] using hp⟩

theorem proposedPrefixGuard_update_after {N r : ℕ} (A : Finset ℕ) (ω : PrimeSample N)
    (q : primesThrough (N : ℝ)) (x : Fin (N + 2)) (hrq : r ≤ q.val) :
    proposedPrefixGuard N A (Function.update ω q x) r = proposedPrefixGuard N A ω r := by
  classical
  by_cases hr : r ∈ primesThrough (N : ℝ)
  · let p : primesThrough (N : ℝ) := ⟨r, hr⟩
    have hc : firstPrefixCandidate N (Function.update ω q x) p = firstPrefixCandidate N ω p := by
      by_cases hpq : p = q
      · subst q
        exact firstPrefixCandidate_update_self N ω p x
      · have hlt : p.val < q.val := by
          have hne : p.val ≠ q.val := fun h => hpq (Subtype.ext h)
          change r ≠ q.val at hne
          change r < q.val
          omega
        exact firstPrefixCandidate_update_after ω p q x hlt
    unfold proposedPrefixGuard
    rw [dite_eq_left hr, dite_eq_left hr]
    change (if 2 ≤ firstPrefixCandidate N (Function.update ω q x) p ∧
      (finitePrimeFibre A (firstPrefixCandidate N (Function.update ω q x) p)).Nonempty then _ else _) = _
    rw [hc]
  · simp only [proposedPrefixGuard, dite_eq_right hr]

theorem processReadyPrefix_update_after {N r : ℕ} (A : Finset ℕ) (ω : PrimeSample N)
    (q : primesThrough (N : ℝ)) (x : Fin (N + 2)) (hrq : r < q.val) (s : PrefixScheduleState) :
    processReadyPrefix N A (Function.update ω q x) r s = processReadyPrefix N A ω r s := by
  classical
  unfold processReadyPrefix
  rw [primeHit_update_after ω q x hrq, proposedPrefixGuard_update_after A ω q x hrq.le]

theorem prefixScheduleStep_update_after {N r : ℕ} (A : Finset ℕ) (ω : PrimeSample N)
    (q : primesThrough (N : ℝ)) (x : Fin (N + 2)) (hrq : r < q.val) (s : PrefixScheduleState) :
    prefixScheduleStep N A (Function.update ω q x) r s = prefixScheduleStep N A ω r s := by
  unfold prefixScheduleStep
  rw [processReadyPrefix_update_after A ω q x hrq s]

theorem prefixSchedule_update_unrevealed {N : ℕ} (A : Finset ℕ) (ω : PrimeSample N)
    (q : primesThrough (N : ℝ)) (x : Fin (N + 2)) (r : ℕ) (hrq : r ≤ q.val) :
    prefixSchedule N A (Function.update ω q x) r = prefixSchedule N A ω r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [prefixSchedule, prefixSchedule, ih (by omega)]
      exact prefixScheduleStep_update_after A ω q x (by omega) _

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/ScheduleGuardValidity.lean -/
section
/- # Valid source prefixes for proposed and retained guards -/

namespace Erdos12Proof

def PrefixGuardValid (N : ℕ) (A : Finset ℕ) (ω : PrimeSample N) (g : PrefixGuard) : Prop :=
  2 ≤ g.sourcePrefix ∧ g.sourcePrefix ≤ N ∧ primePrefixCondition N g.sourcePrefix ω ∧
    (finitePrimeFibre A g.sourcePrefix).Nonempty ∧ g.prime = terminalPrime A g.sourcePrefix

theorem PrefixGuardValid.prime {N : ℕ} {A : Finset ℕ} {ω : PrimeSample N} {g : PrefixGuard}
    (h : PrefixGuardValid N A ω g) : g.prime.Prime := by
  rw [h.2.2.2.2]
  exact terminalPrime_prime A g.sourcePrefix h.2.2.2.1

theorem PrefixGuardValid.source_max_le {N : ℕ} {A : Finset ℕ} {ω : PrimeSample N} {g : PrefixGuard}
    (h : PrefixGuardValid N A ω g) : g.sourcePrefix.maxPrimeFac ≤ g.prime := by
  rw [h.2.2.2.2]
  exact finitePrimeFibre_max_le A (by have := h.1; omega) (terminalPrime_mem A g.sourcePrefix h.2.2.2.1)

theorem PrefixGuardValid.prime_le {N : ℕ} {A : Finset ℕ} {ω : PrimeSample N} {g : PrefixGuard}
    (h : PrefixGuardValid N A ω g) (hA : ∀ a ∈ A, a ≤ N) : g.prime ≤ N := by
  rw [h.2.2.2.2]
  exact finitePrimeFibre_bounded A N hA (by have := h.1; omega)
    (terminalPrime_mem A g.sourcePrefix h.2.2.2.1)

theorem proposedPrefixGuard_spec {N r : ℕ} {A : Finset ℕ} {ω : PrimeSample N} {g : PrefixGuard}
    (h : proposedPrefixGuard N A ω r = some g) :
    ∃ p : primesThrough (N : ℝ), p.val = r ∧ FirstPrefixSpec N ω p g.sourcePrefix ∧
      (finitePrimeFibre A g.sourcePrefix).Nonempty ∧ g.prime = terminalPrime A g.sourcePrefix := by
  classical
  by_cases hr : r ∈ primesThrough (N : ℝ)
  · unfold proposedPrefixGuard at h
    rw [dite_eq_left hr] at h
    dsimp only at h
    by_cases hc : 2 ≤ firstPrefixCandidate N ω ⟨r, hr⟩ ∧
        (finitePrimeFibre A (firstPrefixCandidate N ω ⟨r, hr⟩)).Nonempty
    · rw [ite_eq_left hc] at h
      have heq := Option.some.inj h
      rw [← heq]
      refine ⟨⟨r, hr⟩, rfl, ?_, hc.2, rfl⟩
      exact firstPrefixCandidate_spec_of_ne_zero (by have := hc.1; omega)
    · simp only [ite_eq_right hc] at h
      cases h
  · simp only [proposedPrefixGuard, dite_eq_right hr] at h
    cases h

theorem proposedPrefixGuard_valid {N r : ℕ} {A : Finset ℕ} {ω : PrimeSample N} {g : PrefixGuard}
    (h : proposedPrefixGuard N A ω r = some g) (hhit : primeHit N ω r) :
    PrefixGuardValid N A ω g ∧ g.sourcePrefix.maxPrimeFac = r ∧ r ≤ g.prime := by
  obtain ⟨p, hpr, hspec, hne, hprime⟩ := proposedPrefixGuard_spec h
  obtain ⟨q, hqr, hq⟩ := hhit
  have hqp : q = p := Subtype.ext (hqr.trans hpr.symm)
  subst q
  have hcan := firstPrefixCandidate_eq hspec
  have hpre := firstPrefixCandidate_is_prefix ⟨g.sourcePrefix, hspec⟩ hq
  rw [hcan] at hpre
  have hv : PrefixGuardValid N A ω g := ⟨hspec.1, hspec.2.1, hpre, hne, hprime⟩
  have hmax : g.sourcePrefix.maxPrimeFac = r := hspec.2.2.1.trans hpr
  exact ⟨hv, hmax, hmax ▸ hv.source_max_le⟩

theorem choosePendingGuard_valid {N : ℕ} {A : Finset ℕ} {ω : PrimeSample N}
    (old : Option PrefixGuard) (new : PrefixGuard)
    (hold : ∀ g, old = some g → PrefixGuardValid N A ω g)
    (hnew : PrefixGuardValid N A ω new) : PrefixGuardValid N A ω (choosePendingGuard old new) := by
  cases old with
  | none => exact hnew
  | some g =>
      change PrefixGuardValid N A ω (if g.prime ≤ new.prime then g else new)
      split_ifs
      · exact hold g rfl
      · exact hnew

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/GuardedScoreBounds.lean -/
section
/- # Inherited guard restrictions and their bounds for prefix scores -/

namespace Erdos12Proof

theorem guard_fibre_opposite (N : ℕ) (A : Finset ℕ) (hA : PropertyP (A : Set ℕ))
    (ω : PrimeSample N) (R : Finset ℕ) (sources : ℕ → ℕ) (g : ℕ)
    (hg : 2 ≤ g) (hpre : primePrefixCondition N g ω)
    (hsource : ∀ r ∈ R, PrefixGuardValid N A ω ⟨r, sources r⟩)
    (hbefore : ∀ r ∈ R, r < g.maxPrimeFac) :
    ∀ r ∈ R, ∀ p ∈ finitePrimeFibre A g, ∀ q ∈ finitePrimeFibre A g, r ∣ p + q → p = q := by
  intro r hr p hp q hq hdiv
  have hs := hsource r hr
  have hs0 : 0 < sources r := by
    have hs2 : 2 ≤ sources r := hs.1
    omega
  have hg0 : 0 < g := by omega
  have hsmax : (sources r).maxPrimeFac < g.maxPrimeFac := hs.source_max_le.trans_lt (hbefore r hr)
  have hsdiv : sources r ∣ g := prefix_dvd_of_indices hs0.ne' hg0.ne' hs.2.1 hs.2.2.1 hpre
    hsmax.le (fun h => (hsmax.ne h).elim)
  have hsA := finitePrimeFibre_product_mem A (sources r)
    (terminalPrime_mem A (sources r) hs.2.2.2.1)
  change sources r * terminalPrime A (sources r) ∈ A at hsA
  have hrEq : r = terminalPrime A (sources r) := hs.2.2.2.2
  rw [← hrEq] at hsA
  exact inherited_opposite_restriction hA hs0 hsdiv hg0 hsA
    (finitePrimeFibre_product_mem A g hp) (finitePrimeFibre_product_mem A g hq)
    ((hbefore r hr).trans_le (finitePrimeFibre_max_le A hg0 hp))
    ((hbefore r hr).trans_le (finitePrimeFibre_max_le A hg0 hq)) hdiv

theorem guarded_prefix_score_ratio (N : ℕ) (A : Finset ℕ) (hA : PropertyP (A : Set ℕ))
    (ω : PrimeSample N) (R : Finset ℕ) (sources : ℕ → ℕ) (g : ℕ)
    (hg : 2 ≤ g) (hpre : primePrefixCondition N g ω)
    (hne : (finitePrimeFibre A g).Nonempty)
    (hsource : ∀ r ∈ R, PrefixGuardValid N A ω ⟨r, sources r⟩)
    (hodd : ∀ r ∈ R, 2 < r) (hbefore : ∀ r ∈ R, r < g.maxPrimeFac)
    (hthreshold : (primeModulus R : ℝ) ^ primeTailExponent ≤ g.maxPrimeFac) :
    prefixScore A g ≤ primeTailConstant * (1 / 2 : ℝ) ^ R.card * (1 + R.card) *
      (Real.log (2 * (g.maxPrimeFac : ℝ)) / Real.log (2 * (terminalPrime A g : ℝ))) := by
  have hg0 : 0 < g := by omega
  have hmax : g.maxPrimeFac ≤ terminalPrime A g :=
    finitePrimeFibre_max_le A hg0 (terminalPrime_mem A g hne)
  have hsize : (primeModulus R : ℝ) ^ primeTailExponent ≤ terminalPrime A g :=
    hthreshold.trans (by exact_mod_cast hmax)
  have htail := finite_fibre_guarded_tail A hA hg0 hne R
    (fun r hr => ⟨(hsource r hr).prime, hodd r hr⟩)
    (fun r hr p hp => (hbefore r hr).trans_le (finitePrimeFibre_max_le A hg0 hp))
    (guard_fibre_opposite N A hA ω R sources g hg hpre hsource hbefore) hsize
  have hlog : 0 ≤ Real.log (2 * (g.maxPrimeFac : ℝ)) := by
    have hp := Nat.prime_maxPrimeFac_of_one_lt (by omega : 1 < g)
    apply Real.log_nonneg
    have hpr : (2 : ℝ) ≤ g.maxPrimeFac := by exact_mod_cast hp.two_le
    linarith
  have h := mul_le_mul_of_nonneg_left htail hlog
  unfold prefixScore
  convert h using 1; ring

theorem guarded_prefix_score_bound (N : ℕ) (A : Finset ℕ) (hA : PropertyP (A : Set ℕ))
    (ω : PrimeSample N) (R : Finset ℕ) (sources : ℕ → ℕ) (g : ℕ)
    (hg : 2 ≤ g) (hpre : primePrefixCondition N g ω)
    (hsource : ∀ r ∈ R, PrefixGuardValid N A ω ⟨r, sources r⟩)
    (hodd : ∀ r ∈ R, 2 < r) (hbefore : ∀ r ∈ R, r < g.maxPrimeFac)
    (hthreshold : (primeModulus R : ℝ) ^ primeTailExponent ≤ g.maxPrimeFac) :
    prefixScore A g ≤ primeTailConstant * (1 / 2 : ℝ) ^ R.card * (1 + R.card) := by
  classical
  by_cases hne : (finitePrimeFibre A g).Nonempty
  · have h := guarded_prefix_score_ratio N A hA ω R sources g hg hpre hne hsource hodd hbefore hthreshold
    have hmax := finitePrimeFibre_max_le A (by omega : 0 < g) (terminalPrime_mem A g hne)
    have hp := terminalPrime_prime A g hne
    have hp2 : (2 : ℝ) ≤ terminalPrime A g := by exact_mod_cast hp.two_le
    have hden : 0 < Real.log (2 * (terminalPrime A g : ℝ)) := Real.log_pos (by linarith)
    have hlogle : Real.log (2 * (g.maxPrimeFac : ℝ)) ≤ Real.log (2 * (terminalPrime A g : ℝ)) := by
      have hr := (Nat.prime_maxPrimeFac_of_one_lt (by omega : 1 < g)).pos
      exact Real.log_le_log (by exact_mod_cast Nat.mul_pos (by decide : 0 < (2 : ℕ)) hr)
        (by exact_mod_cast Nat.mul_le_mul_left 2 hmax)
    apply h.trans
    apply mul_le_of_le_one_right
    · exact mul_nonneg (mul_nonneg primeTailConstant_pos.le (by positivity)) (by positivity)
    · exact (div_le_one hden).mpr hlogle
  · have he : finitePrimeFibre A g = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [prefixScore, he, harmonic, Finset.sum_empty, mul_zero]
    have hC := primeTailConstant_pos
    positivity

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/ScheduleHistory.lean -/
section
/- # Source-history invariants of the adaptive prefix schedule -/

namespace Erdos12Proof

def ScheduleHistoryValid (N : ℕ) (A : Finset ℕ) (ω : PrimeSample N) (s : PrefixScheduleState) : Prop :=
  (∀ p ∈ s.guards, PrefixGuardValid N A ω ⟨p, s.sources p⟩) ∧
    ∀ g, s.pending = some g → PrefixGuardValid N A ω g

theorem activatePrefixGuard_history {N : ℕ} {A : Finset ℕ} {ω : PrimeSample N}
    (s : PrefixScheduleState) (g : PrefixGuard) (hs : ScheduleHistoryValid N A ω s)
    (hg : PrefixGuardValid N A ω g) : ScheduleHistoryValid N A ω (activatePrefixGuard s g) := by
  constructor
  · intro p hp
    change p ∈ insert g.prime s.guards at hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · simpa only [activatePrefixGuard, Function.update_self] using hg
    · by_cases hpg : p = g.prime
      · subst p
        simpa only [activatePrefixGuard, Function.update_self] using hg
      · simpa only [activatePrefixGuard, Function.update_of_ne hpg] using hs.1 p hp
  · intro q hq
    change none = some q at hq
    cases hq

theorem recordPrefixGuard_history {N : ℕ} {A : Finset ℕ} {ω : PrimeSample N}
    (s : PrefixScheduleState) (r : ℕ) (g : PrefixGuard) (hs : ScheduleHistoryValid N A ω s)
    (hg : PrefixGuardValid N A ω g) : ScheduleHistoryValid N A ω (recordPrefixGuard s r g) := by
  have hchosen := choosePendingGuard_valid s.pending g hs.2 hg
  unfold recordPrefixGuard
  dsimp only
  split_ifs
  · exact activatePrefixGuard_history s _ hs hchosen
  · constructor
    · exact hs.1
    · intro q hq
      have heq : choosePendingGuard s.pending g = q := Option.some.inj hq
      rwa [← heq]

theorem processReadyPrefix_history {N : ℕ} {A : Finset ℕ} {ω : PrimeSample N}
    (r : ℕ) (s : PrefixScheduleState) (hs : ScheduleHistoryValid N A ω s) :
    ScheduleHistoryValid N A ω (processReadyPrefix N A ω r s) := by
  classical
  unfold processReadyPrefix
  split_ifs with hhit
  · cases hprop : proposedPrefixGuard N A ω r with
    | none => exact hs
    | some g => exact recordPrefixGuard_history s r g hs (proposedPrefixGuard_valid hprop hhit).1
  · exact hs

theorem prefixScheduleStep_history {N : ℕ} {A : Finset ℕ} {ω : PrimeSample N}
    (r : ℕ) (s : PrefixScheduleState) (hs : ScheduleHistoryValid N A ω s) :
    ScheduleHistoryValid N A ω (prefixScheduleStep N A ω r s) := by
  unfold prefixScheduleStep
  split_ifs
  · exact hs
  · cases hpend : s.pending with
    | none => exact processReadyPrefix_history r s hs
    | some g =>
        change ScheduleHistoryValid N A ω
          (if g.prime ≤ r then activatePrefixGuard s g else processReadyPrefix N A ω r s)
        split_ifs
        · exact activatePrefixGuard_history s g hs (hs.2 g hpend)
        · exact processReadyPrefix_history r s hs

theorem prefixSchedule_history (N : ℕ) (A : Finset ℕ) (ω : PrimeSample N) (r : ℕ) :
    ScheduleHistoryValid N A ω (prefixSchedule N A ω r) := by
  induction r with
  | zero => simp [ScheduleHistoryValid, prefixSchedule, initialPrefixSchedule]
  | succ r ih => exact prefixScheduleStep_history r _ ih

theorem prefixSchedule_guard_prime_le (N : ℕ) (A : Finset ℕ) (hA : ∀ a ∈ A, a ≤ N)
    (ω : PrimeSample N) (r p : ℕ) (hp : p ∈ (prefixSchedule N A ω r).guards) : p ≤ N :=
  ((prefixSchedule_history N A ω r).1 p hp).prime_le hA

theorem prefixSchedule_pending_prime_le (N : ℕ) (A : Finset ℕ) (hA : ∀ a ∈ A, a ≤ N)
    (ω : PrimeSample N) (r : ℕ) (g : PrefixGuard) (hg : (prefixSchedule N A ω r).pending = some g) :
    g.prime ≤ N := ((prefixSchedule_history N A ω r).2 g hg).prime_le hA

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/ScheduleTimingBasic.lean -/
section
/- # Elementary timing invariants of the adaptive schedule -/

namespace Erdos12Proof

structure ScheduleTimingValid (r : ℕ) (s : PrefixScheduleState) : Prop where
  ready_floor : 4 ≤ s.readyAt
  guards_past : ∀ p ∈ s.guards, p < r
  guards_odd : ∀ p ∈ s.guards, 2 < p
  pending_next : ∀ g, s.pending = some g → r ≤ g.prime ∧ 2 < g.prime
  pending_clear : r < s.readyAt → s.pending = none

theorem choosePendingGuard_cases (old : Option PrefixGuard) (new : PrefixGuard) :
    choosePendingGuard old new = new ∨ ∃ g, old = some g ∧ choosePendingGuard old new = g := by
  cases old with
  | none => exact Or.inl rfl
  | some g =>
      by_cases h : g.prime ≤ new.prime
      · exact Or.inr ⟨g, rfl, by simp only [choosePendingGuard, ite_eq_left h]⟩
      · exact Or.inl (by simp only [choosePendingGuard, ite_eq_right h])

theorem timing_delay_succ {r : ℕ} {s : PrefixScheduleState} (hs : ScheduleTimingValid r s)
    (hdelay : r < s.readyAt) : ScheduleTimingValid (r + 1) s := by
  refine ⟨hs.ready_floor, ?_, hs.guards_odd, ?_, ?_⟩
  · intro p hp
    exact (hs.guards_past p hp).trans (Nat.lt_succ_self r)
  · intro g hg
    rw [hs.pending_clear hdelay] at hg
    cases hg
  · intro _
    exact hs.pending_clear hdelay

theorem timing_replace_pending {r : ℕ} {s : PrefixScheduleState} (hs : ScheduleTimingValid r s)
    (hready : s.readyAt ≤ r) (pending : Option PrefixGuard)
    (hnext : ∀ g, pending = some g → r < g.prime ∧ 2 < g.prime) :
    ScheduleTimingValid (r + 1) {s with pending := pending} := by
  refine ⟨hs.ready_floor, ?_, hs.guards_odd, ?_, ?_⟩
  · intro p hp
    exact (hs.guards_past p hp).trans (Nat.lt_succ_self r)
  · intro g hg
    have h := hnext g hg
    exact ⟨Nat.succ_le_of_lt h.1, h.2⟩
  · intro h
    have : r + 1 < s.readyAt := h
    omega

theorem timing_activate {N r : ℕ} {A : Finset ℕ} {ω : PrimeSample N}
    (s : PrefixScheduleState) (g : PrefixGuard) (hs : ScheduleTimingValid r s)
    (hh : ScheduleHistoryValid N A ω s) (hg : PrefixGuardValid N A ω g)
    (hgr : g.prime = r) (hr : 4 ≤ r) : ScheduleTimingValid (r + 1) (activatePrefixGuard s g) := by
  have hprime : ∀ p ∈ insert g.prime s.guards, p.Prime := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hg.prime
    · exact (hh.1 p hp).prime
  have hM : 4 ≤ primeModulus (insert g.prime s.guards) :=
    hr.trans (hgr ▸ primeModulus_mem_le _ hprime (Finset.mem_insert_self _ _))
  have hpow : primeModulus (insert g.prime s.guards) ≤
      primeModulus (insert g.prime s.guards) ^ primeTailExponent := by
    have h := Nat.pow_le_pow_right (show 1 ≤ primeModulus (insert g.prime s.guards) by omega)
      (show 1 ≤ primeTailExponent by have := primeTailExponent_ge_three; omega)
    simpa only [pow_one] using h
  refine ⟨hM.trans hpow, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · omega
    · exact (hs.guards_past p hp).trans (Nat.lt_succ_self r)
  · intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · omega
    · exact hs.guards_odd p hp
  · intro p hp
    change none = some p at hp
    cases hp
  · intro _
    rfl

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/ScheduleTiming.lean -/
section
/- # Preservation of the scheduling clock and pending-guard bounds -/

namespace Erdos12Proof

theorem timing_ready_succ {r : ℕ} {s : PrefixScheduleState} (hs : ScheduleTimingValid r s)
    (hready : s.readyAt ≤ r) (hdue : ∀ g, s.pending = some g → r < g.prime) :
    ScheduleTimingValid (r + 1) s := by
  apply timing_replace_pending hs hready s.pending
  intro g hg
  exact ⟨hdue g hg, (hs.pending_next g hg).2⟩

theorem recordPrefixGuard_timing {N r : ℕ} {A : Finset ℕ} {ω : PrimeSample N}
    (s : PrefixScheduleState) (g : PrefixGuard) (hs : ScheduleTimingValid r s)
    (hh : ScheduleHistoryValid N A ω s) (hready : s.readyAt ≤ r)
    (hdue : ∀ q, s.pending = some q → r < q.prime)
    (hg : PrefixGuardValid N A ω g) (hgr : r ≤ g.prime) :
    ScheduleTimingValid (r + 1) (recordPrefixGuard s r g) := by
  let chosen := choosePendingGuard s.pending g
  have hr4 : 4 ≤ r := hs.ready_floor.trans hready
  have hcValid : PrefixGuardValid N A ω chosen := choosePendingGuard_valid s.pending g hh.2 hg
  have hcBound : r ≤ chosen.prime ∧ 2 < chosen.prime := by
    rcases choosePendingGuard_cases s.pending g with heq | ⟨q, hq, heq⟩
    · change r ≤ (choosePendingGuard s.pending g).prime ∧ 2 < (choosePendingGuard s.pending g).prime
      rw [heq]
      omega
    · change r ≤ (choosePendingGuard s.pending g).prime ∧ 2 < (choosePendingGuard s.pending g).prime
      rw [heq]
      exact ⟨(hdue q hq).le, (hs.pending_next q hq).2⟩
  change ScheduleTimingValid (r + 1)
    (if chosen.prime ≤ r then activatePrefixGuard s chosen else {s with pending := some chosen})
  split_ifs with htime
  · exact timing_activate s chosen hs hh hcValid (by omega) hr4
  · apply timing_replace_pending hs hready (some chosen)
    intro q hq
    have heq : chosen = q := Option.some.inj hq
    rw [← heq]
    exact ⟨lt_of_not_ge htime, hcBound.2⟩

theorem processReadyPrefix_timing {N r : ℕ} {A : Finset ℕ} {ω : PrimeSample N}
    (s : PrefixScheduleState) (hs : ScheduleTimingValid r s) (hh : ScheduleHistoryValid N A ω s)
    (hready : s.readyAt ≤ r) (hdue : ∀ g, s.pending = some g → r < g.prime) :
    ScheduleTimingValid (r + 1) (processReadyPrefix N A ω r s) := by
  classical
  unfold processReadyPrefix
  split_ifs with hhit
  · cases hprop : proposedPrefixGuard N A ω r with
    | none => exact timing_ready_succ hs hready hdue
    | some g =>
        obtain ⟨hg, _, hgr⟩ := proposedPrefixGuard_valid hprop hhit
        exact recordPrefixGuard_timing s g hs hh hready hdue hg hgr
  · exact timing_ready_succ hs hready hdue

theorem prefixScheduleStep_timing {N r : ℕ} {A : Finset ℕ} {ω : PrimeSample N}
    (s : PrefixScheduleState) (hs : ScheduleTimingValid r s) (hh : ScheduleHistoryValid N A ω s) :
    ScheduleTimingValid (r + 1) (prefixScheduleStep N A ω r s) := by
  unfold prefixScheduleStep
  split_ifs with hdelay
  · exact timing_delay_succ hs hdelay
  · have hready : s.readyAt ≤ r := Nat.le_of_not_gt hdelay
    cases hpend : s.pending with
    | none =>
        apply processReadyPrefix_timing s hs hh hready
        intro g hg
        rw [hpend] at hg
        cases hg
    | some g =>
        change ScheduleTimingValid (r + 1)
          (if g.prime ≤ r then activatePrefixGuard s g else processReadyPrefix N A ω r s)
        split_ifs with htime
        · have hnext := (hs.pending_next g hpend).1
          exact timing_activate s g hs hh (hh.2 g hpend) (by omega) (hs.ready_floor.trans hready)
        · apply processReadyPrefix_timing s hs hh hready
          intro q hq
          have heq : g = q := Option.some.inj (hpend.symm.trans hq)
          rw [← heq]
          exact lt_of_not_ge htime

theorem prefixSchedule_timing (N : ℕ) (A : Finset ℕ) (ω : PrimeSample N) (r : ℕ) :
    ScheduleTimingValid r (prefixSchedule N A ω r) := by
  induction r with
  | zero =>
      constructor
      · exact le_refl _
      · simp [prefixSchedule, initialPrefixSchedule]
      · simp [prefixSchedule, initialPrefixSchedule]
      · simp [prefixSchedule, initialPrefixSchedule]
      · simp [prefixSchedule, initialPrefixSchedule]
  | succ r ih => exact prefixScheduleStep_timing _ ih (prefixSchedule_history N A ω r)

theorem prefixSchedule_final_pending (N : ℕ) (A : Finset ℕ) (hA : ∀ a ∈ A, a ≤ N)
    (ω : PrimeSample N) : (prefixSchedule N A ω (N + 1)).pending = none := by
  cases hpend : (prefixSchedule N A ω (N + 1)).pending with
  | none => rfl
  | some g =>
      have hlow := ((prefixSchedule_timing N A ω (N + 1)).pending_next g hpend).1
      have hhigh := prefixSchedule_pending_prime_le N A hA ω (N + 1) g hpend
      omega

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/StageWeights.lean -/
section
/- # A telescoping reserve for the successive guard stages -/

namespace Erdos12Proof

noncomputable def stageWeight (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ k * (1 + k)
noncomputable def stageReserve (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ k * (2 * k + 4)

theorem stageWeight_nonneg (k : ℕ) : 0 ≤ stageWeight k := by unfold stageWeight; positivity
theorem stageReserve_nonneg (k : ℕ) : 0 ≤ stageReserve k := by unfold stageReserve; positivity
theorem stageReserve_zero : stageReserve 0 = 4 := by norm_num [stageReserve]

theorem stageReserve_step (k : ℕ) : stageReserve k - stageReserve (k + 1) = stageWeight k := by
  simp only [stageReserve, stageWeight, pow_succ, Nat.cast_add, Nat.cast_one]
  ring

theorem stageWeight_le_reserve (k : ℕ) : stageWeight k ≤ stageReserve k := by
  have h := stageReserve_nonneg (k + 1)
  linarith [stageReserve_step k]

theorem sum_range_differences (f : ℕ → ℝ) (n : ℕ) :
    (∑ r ∈ Finset.range n, (f (r + 1) - f r)) = f n - f 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/ScheduleTransitions.lean -/
section
/- # The three possible state changes in the adaptive schedule -/

namespace Erdos12Proof

inductive PrefixTransition (r : ℕ) (s : PrefixScheduleState) : PrefixScheduleState → Prop
  | idle : PrefixTransition r s s
  | pending (g : PrefixGuard) (hready : s.readyAt ≤ r) (hfuture : r < g.prime)
      (hmin : ∀ q, s.pending = some q → g.prime ≤ q.prime) :
      PrefixTransition r s {s with pending := some g}
  | activate (g : PrefixGuard) (hready : s.readyAt ≤ r) (heq : g.prime = r) :
      PrefixTransition r s (activatePrefixGuard s g)

theorem choosePendingGuard_le_old (old : Option PrefixGuard) (g q : PrefixGuard)
    (hq : old = some q) : (choosePendingGuard old g).prime ≤ q.prime := by
  subst old
  change (if q.prime ≤ g.prime then q else g).prime ≤ q.prime
  split_ifs with h
  · exact le_refl _
  · exact (lt_of_not_ge h).le

theorem recordPrefixGuard_transition {r : ℕ} {s : PrefixScheduleState}
    (hs : ScheduleTimingValid r s) (hready : s.readyAt ≤ r) (g : PrefixGuard)
    (hgr : r ≤ g.prime) : PrefixTransition r s (recordPrefixGuard s r g) := by
  let q := choosePendingGuard s.pending g
  have hq : r ≤ q.prime := by
    rcases choosePendingGuard_cases s.pending g with heq | ⟨p, hp, heq⟩
    · change r ≤ (choosePendingGuard s.pending g).prime
      rw [heq]
      exact hgr
    · change r ≤ (choosePendingGuard s.pending g).prime
      rw [heq]
      exact (hs.pending_next p hp).1
  change PrefixTransition r s (if q.prime ≤ r then activatePrefixGuard s q else {s with pending := some q})
  split_ifs with htime
  · exact PrefixTransition.activate q hready (by omega)
  · exact PrefixTransition.pending q hready (lt_of_not_ge htime) (choosePendingGuard_le_old _ _)

theorem processReadyPrefix_transition {N r : ℕ} {A : Finset ℕ} {ω : PrimeSample N}
    (s : PrefixScheduleState) (hs : ScheduleTimingValid r s) (hready : s.readyAt ≤ r) :
    PrefixTransition r s (processReadyPrefix N A ω r s) := by
  classical
  unfold processReadyPrefix
  split_ifs with hhit
  · cases hprop : proposedPrefixGuard N A ω r with
    | none => exact PrefixTransition.idle
    | some g =>
        exact recordPrefixGuard_transition hs hready g (proposedPrefixGuard_valid hprop hhit).2.2
  · exact PrefixTransition.idle

theorem prefixScheduleStep_transition {N r : ℕ} {A : Finset ℕ} {ω : PrimeSample N}
    (s : PrefixScheduleState) (hs : ScheduleTimingValid r s) :
    PrefixTransition r s (prefixScheduleStep N A ω r s) := by
  unfold prefixScheduleStep
  split_ifs with hdelay
  · exact PrefixTransition.idle
  · have hready : s.readyAt ≤ r := Nat.le_of_not_gt hdelay
    cases hp : s.pending with
    | none => exact processReadyPrefix_transition s hs hready
    | some g =>
        change PrefixTransition r s
          (if g.prime ≤ r then activatePrefixGuard s g else processReadyPrefix N A ω r s)
        split_ifs with htime
        · exact PrefixTransition.activate g hready (by have := (hs.pending_next g hp).1; omega)
        · exact processReadyPrefix_transition s hs hready

theorem prefixSchedule_transition (N : ℕ) (A : Finset ℕ) (ω : PrimeSample N) (r : ℕ) :
    PrefixTransition r (prefixSchedule N A ω r) (prefixSchedule N A ω (r + 1)) :=
  prefixScheduleStep_transition _ (prefixSchedule_timing N A ω r)

theorem PrefixTransition.card {r : ℕ} {s t : PrefixScheduleState} (h : PrefixTransition r s t)
    (hs : ScheduleTimingValid r s) : t.guards.card = s.guards.card ∨ t.guards.card = s.guards.card + 1 := by
  cases h with
  | idle => exact Or.inl rfl
  | pending => exact Or.inl rfl
  | activate g _ heq =>
      right
      have hnot : g.prime ∉ s.guards := by intro hp; have := hs.guards_past _ hp; omega
      exact Finset.card_insert_of_notMem hnot

noncomputable def activationWeight (s t : PrefixScheduleState) : ℝ :=
  stageReserve s.guards.card - stageReserve t.guards.card

theorem activationWeight_nonneg {r : ℕ} {s t : PrefixScheduleState}
    (h : PrefixTransition r s t) (hs : ScheduleTimingValid r s) : 0 ≤ activationWeight s t := by
  rcases h.card hs with hc | hc
  · simp only [activationWeight, hc, sub_self, le_refl]
  · rw [activationWeight, hc, stageReserve_step]
    exact stageWeight_nonneg _

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/ScheduleGeometry.lean -/
section
/- # The inherited threshold and the length of every delayed stage -/

namespace Erdos12Proof

structure ScheduleGeometryValid (r : ℕ) (s : PrefixScheduleState) : Prop where
  threshold : primeModulus s.guards ^ primeTailExponent ≤ s.readyAt
  start_past : s.delayStart ≤ r
  empty_start : s.delayStart = 0 ↔ s.guards = ∅
  empty_ready : s.delayStart = 0 → s.readyAt = 4
  delay_data : s.delayStart ≠ 0 →
    4 ≤ s.delayStart ∧ s.guards = insert s.delayStart s.delayGuards ∧
    s.delayStart ∉ s.delayGuards ∧
    (∀ p ∈ s.delayGuards, p < s.delayStart) ∧
    primeModulus s.delayGuards ^ primeTailExponent ≤ s.delayStart ∧
    s.readyAt = primeModulus s.guards ^ primeTailExponent

theorem geometry_activate {r : ℕ} {s : PrefixScheduleState} (hs : ScheduleTimingValid r s)
    (hg : ScheduleGeometryValid r s) (g : PrefixGuard) (hr : s.readyAt ≤ r)
    (heq : g.prime = r) : ScheduleGeometryValid (r + 1) (activatePrefixGuard s g) := by
  have hr4 : 4 ≤ r := hs.ready_floor.trans hr
  have hnot : g.prime ∉ s.guards := by intro hp; have := hs.guards_past _ hp; omega
  refine ⟨le_refl _, ?_, ?_, ?_, ?_⟩
  · change g.prime ≤ r + 1
    omega
  · change g.prime = 0 ↔ insert g.prime s.guards = ∅
    constructor
    · intro h
      omega
    · intro h
      have hm : g.prime ∈ insert g.prime s.guards := Finset.mem_insert_self _ _
      rw [h] at hm
      exact (Finset.notMem_empty _ hm).elim
  · intro h
    change g.prime = 0 at h
    omega
  · intro _
    exact ⟨by change 4 ≤ g.prime; omega, rfl, hnot,
      by intro p hp; change p < g.prime; rw [heq]; exact hs.guards_past p hp,
      by change primeModulus s.guards ^ primeTailExponent ≤ g.prime; rw [heq]; exact hg.threshold.trans hr, rfl⟩

theorem PrefixTransition.geometry {r : ℕ} {s t : PrefixScheduleState} (h : PrefixTransition r s t)
    (hs : ScheduleTimingValid r s) (hg : ScheduleGeometryValid r s) : ScheduleGeometryValid (r + 1) t := by
  cases h with
  | idle => exact ⟨hg.threshold, hg.start_past.trans (Nat.le_succ r), hg.empty_start, hg.empty_ready, hg.delay_data⟩
  | pending g _ _ _ =>
      exact ⟨hg.threshold, hg.start_past.trans (Nat.le_succ r), hg.empty_start, hg.empty_ready, hg.delay_data⟩
  | activate g hr heq => exact geometry_activate hs hg g hr heq

theorem prefixSchedule_geometry (N : ℕ) (A : Finset ℕ) (ω : PrimeSample N) (r : ℕ) :
    ScheduleGeometryValid r (prefixSchedule N A ω r) := by
  induction r with
  | zero =>
      constructor
      · norm_num [prefixSchedule, initialPrefixSchedule, primeModulus]
      · exact le_refl _
      · simp [prefixSchedule, initialPrefixSchedule]
      · simp [prefixSchedule, initialPrefixSchedule]
      · simp [prefixSchedule, initialPrefixSchedule]
  | succ r ih => exact (prefixSchedule_transition N A ω r).geometry (prefixSchedule_timing N A ω r) ih

theorem ScheduleGeometryValid.delay_window {r : ℕ} {s : PrefixScheduleState}
    (hg : ScheduleGeometryValid r s) (hne : s.delayStart ≠ 0) :
    s.readyAt ≤ s.delayStart ^ (primeTailExponent + 1) := by
  obtain ⟨_, hguards, hnot, _, hbase, htime⟩ := hg.delay_data hne
  rw [htime, hguards]
  have hprod : primeModulus (insert s.delayStart s.delayGuards) =
      s.delayStart * primeModulus s.delayGuards := Finset.prod_insert hnot
  rw [hprod, mul_pow, pow_succ]
  exact Nat.mul_le_mul_left _ hbase

theorem ScheduleGeometryValid.delay_card {r : ℕ} {s : PrefixScheduleState}
    (hg : ScheduleGeometryValid r s) (hne : s.delayStart ≠ 0) :
    s.guards.card = s.delayGuards.card + 1 := by
  obtain ⟨_, hguards, hnot, _⟩ := hg.delay_data hne
  rw [hguards, Finset.card_insert_of_notMem hnot]

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/PrimePrefixSums.lean -/
section
/- # Prime sums immediately before each natural-number time -/

namespace Erdos12Proof

noncomputable def primeLogPrefix (r : ℕ) : ℝ :=
  ∑ p ∈ Finset.range r, if p.Prime then Real.log (p : ℝ) / p else 0

theorem primeLogPrefix_zero : primeLogPrefix 0 = 0 := by simp [primeLogPrefix]

theorem primeLogPrefix_step (r : ℕ) :
    primeLogPrefix (r + 1) = primeLogPrefix r + (if r.Prime then Real.log (r : ℝ) / r else 0) := by
  exact Finset.sum_range_succ _ _

theorem primeLogPrefix_nonneg (r : ℕ) : 0 ≤ primeLogPrefix r := by
  apply Finset.sum_nonneg
  intro p _
  split_ifs
  · exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  · exact le_refl _

theorem primeLogPrefix_mono {r t : ℕ} (hrt : r ≤ t) : primeLogPrefix r ≤ primeLogPrefix t := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hrt)
  intro p _ _
  split_ifs
  · exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  · exact le_refl _

theorem primeLogPrefix_bound {r : ℕ} {P : ℝ} (hP : 2 ≤ P) (hrP : (r : ℝ) ≤ P + 1) :
    primeLogPrefix r ≤ primeLogWeightConstant * Real.log P := by
  classical
  have hsub : (Finset.range r).filter Nat.Prime ⊆ primesThrough P := by
    intro p hp
    obtain ⟨hpr, hpPrime⟩ := Finset.mem_filter.mp hp
    have hpr' : (p : ℝ) + 1 ≤ r := by exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hpr)
    exact (mem_primesThrough (by linarith)).mpr ⟨hpPrime, by linarith⟩
  calc
    primeLogPrefix r = ∑ p ∈ (Finset.range r).filter Nat.Prime, Real.log (p : ℝ) / p := by
      rw [Finset.sum_filter]
      rfl
    _ ≤ primeLogReciprocalSum P := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p _ _
      exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
    _ ≤ _ := primeLogWeightConstant_bound hP

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/PendingPotentials.lean -/
section
/- # Potentials for a pending guard and the predictable prime intensity -/

namespace Erdos12Proof

noncomputable def pendingProgress (f : ℕ → ℝ) (r : ℕ) (s : PrefixScheduleState) : ℝ :=
  match s.pending with
  | none => 0
  | some g => stageWeight s.guards.card * f r / Real.log (g.prime : ℝ)

noncomputable def pendingLogProgress := pendingProgress (fun r => Real.log (r : ℝ))
noncomputable def pendingPrimeProgress := pendingProgress primeLogPrefix

noncomputable def pendingPrimeIntensity (r : ℕ) (s : PrefixScheduleState) : ℝ :=
  if r.Prime then pendingLogProgress r s / r else 0

theorem pendingProgress_nonneg {r : ℕ} {s : PrefixScheduleState} (hs : ScheduleTimingValid r s)
    (f : ℕ → ℝ) (hf : 0 ≤ f r) : 0 ≤ pendingProgress f r s := by
  cases hp : s.pending with
  | none => simp only [pendingProgress, hp, le_refl]
  | some g =>
      simp only [pendingProgress, hp]
      have hg := (hs.pending_next g hp).2
      have hlog : 0 < Real.log (g.prime : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < g.prime by omega))
      exact div_nonneg (mul_nonneg (stageWeight_nonneg _) hf) hlog.le

theorem pendingProgress_replace {r : ℕ} {s : PrefixScheduleState}
    (f : ℕ → ℝ) (hf : 0 ≤ f (r + 1)) (g : PrefixGuard) (hg : 2 < g.prime)
    (hmin : ∀ q, s.pending = some q → g.prime ≤ q.prime) :
    pendingProgress f (r + 1) s ≤ pendingProgress f (r + 1) {s with pending := some g} := by
  have hlog : 0 < Real.log (g.prime : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < g.prime by omega))
  cases hp : s.pending with
  | none =>
      simp only [pendingProgress, hp]
      change 0 ≤ stageWeight s.guards.card * f (r + 1) / Real.log (g.prime : ℝ)
      exact div_nonneg (mul_nonneg (stageWeight_nonneg _) hf) hlog.le
  | some q =>
      simp only [pendingProgress, hp]
      change stageWeight s.guards.card * f (r + 1) / Real.log (q.prime : ℝ) ≤
        stageWeight s.guards.card * f (r + 1) / Real.log (g.prime : ℝ)
      apply div_le_div_of_nonneg_left (mul_nonneg (stageWeight_nonneg _) hf) hlog
      exact Real.log_le_log (by exact_mod_cast (show 0 < g.prime by omega)) (by exact_mod_cast hmin q hp)

theorem pendingLogProgress_nonneg {r : ℕ} {s : PrefixScheduleState} (hs : ScheduleTimingValid r s) :
    0 ≤ pendingLogProgress r s := pendingProgress_nonneg hs _ (Real.log_natCast_nonneg r)

theorem pendingLogProgress_le_weight {r : ℕ} {s : PrefixScheduleState}
    (hs : ScheduleTimingValid r s) (hr : 1 ≤ r) :
    pendingLogProgress r s ≤ stageWeight s.guards.card := by
  cases hp : s.pending with
  | none => simpa only [pendingLogProgress, pendingProgress, hp] using stageWeight_nonneg s.guards.card
  | some g =>
      simp only [pendingLogProgress, pendingProgress, hp]
      have hbound := hs.pending_next g hp
      have hlog : 0 < Real.log (g.prime : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < g.prime by omega))
      have hlogle : Real.log (r : ℝ) ≤ Real.log (g.prime : ℝ) :=
        Real.log_le_log (by exact_mod_cast (show 0 < r by omega)) (by exact_mod_cast hbound.1)
      change stageWeight s.guards.card * Real.log (r : ℝ) / Real.log (g.prime : ℝ) ≤ _
      exact (div_le_iff₀ hlog).mpr (mul_le_mul_of_nonneg_left hlogle (stageWeight_nonneg _))

theorem pendingLogProgress_transition {r : ℕ} {s t : PrefixScheduleState}
    (hs : ScheduleTimingValid r s) (ht : PrefixTransition r s t) (hr : 1 ≤ r) :
    0 ≤ pendingLogProgress (r + 1) t - pendingLogProgress r s + activationWeight s t := by
  have hmono : pendingLogProgress r s ≤ pendingLogProgress (r + 1) s := by
    cases hp : s.pending with
    | none => simp only [pendingLogProgress, pendingProgress, hp, le_refl]
    | some g =>
        simp only [pendingLogProgress, pendingProgress, hp]
        have hlog : 0 ≤ Real.log (g.prime : ℝ) := Real.log_natCast_nonneg _
        change stageWeight s.guards.card * Real.log (r : ℝ) / Real.log (g.prime : ℝ) ≤
          stageWeight s.guards.card * Real.log ((r + 1 : ℕ) : ℝ) / Real.log (g.prime : ℝ)
        apply div_le_div_of_nonneg_right _ hlog
        apply mul_le_mul_of_nonneg_left _ (stageWeight_nonneg _)
        exact Real.log_le_log (by exact_mod_cast (show 0 < r by omega)) (by exact_mod_cast Nat.le_succ r)
  cases ht with
  | idle => simpa only [activationWeight, sub_self, add_zero] using sub_nonneg.mpr hmono
  | pending g hready hfuture hmin =>
      have hg : 2 < g.prime := by have := hs.ready_floor; omega
      have hnext := pendingProgress_replace (r := r) (s := s) (fun n => Real.log (n : ℝ))
        (Real.log_natCast_nonneg (r + 1)) g hg hmin
      change pendingLogProgress (r + 1) s ≤ pendingLogProgress (r + 1) {s with pending := some g} at hnext
      simp only [activationWeight, sub_self, add_zero]
      exact sub_nonneg.mpr (hmono.trans hnext)
  | activate g hready heq =>
      have hn : g.prime ∉ s.guards := by intro hp; have := hs.guards_past _ hp; omega
      have haw : activationWeight s (activatePrefixGuard s g) = stageWeight s.guards.card := by
        change stageReserve s.guards.card - stageReserve (insert g.prime s.guards).card = _
        rw [Finset.card_insert_of_notMem hn, stageReserve_step]
      have hQ := pendingLogProgress_le_weight hs hr
      rw [haw]
      change 0 ≤ 0 - pendingLogProgress r s + stageWeight s.guards.card
      linarith

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/PredictableScheduleBudget.lean -/
section
/- # The expected cost of ready coordinates, bounded by telescoping -/

namespace Erdos12Proof

theorem pendingPrimeProgress_step (r : ℕ) (s : PrefixScheduleState) :
    pendingPrimeProgress (r + 1) s - pendingPrimeProgress r s = pendingPrimeIntensity r s := by
  cases hp : s.pending with
  | none => simp [pendingPrimeProgress, pendingPrimeIntensity, pendingLogProgress, pendingProgress, hp]
  | some g =>
      simp only [pendingPrimeProgress, pendingProgress, hp, primeLogPrefix_step,
        pendingPrimeIntensity, pendingLogProgress]
      split_ifs <;> ring

theorem pendingPrimeProgress_bound {r : ℕ} {s : PrefixScheduleState}
    (hs : ScheduleTimingValid r s) :
    pendingPrimeProgress (r + 1) s ≤ primeLogWeightConstant * stageWeight s.guards.card := by
  cases hp : s.pending with
  | none =>
      simp only [pendingPrimeProgress, pendingProgress, hp]
      exact mul_nonneg primeLogWeightConstant_pos.le (stageWeight_nonneg _)
  | some g =>
      simp only [pendingPrimeProgress, pendingProgress, hp]
      have hg := hs.pending_next g hp
      have hP : (2 : ℝ) ≤ g.prime := by exact_mod_cast (show 2 ≤ g.prime by omega)
      have hlog : 0 < Real.log (g.prime : ℝ) := Real.log_pos (by linarith)
      have hbound := primeLogPrefix_bound (r := r + 1) hP (by exact_mod_cast Nat.add_le_add_right hg.1 1)
      change stageWeight s.guards.card * primeLogPrefix (r + 1) / Real.log (g.prime : ℝ) ≤ _
      apply (div_le_iff₀ hlog).mpr
      have hmul := mul_le_mul_of_nonneg_left hbound (stageWeight_nonneg s.guards.card)
      nlinarith

theorem pendingPrimeIntensity_transition {r : ℕ} {s t : PrefixScheduleState}
    (hs : ScheduleTimingValid r s) (ht : PrefixTransition r s t) :
    pendingPrimeIntensity r s ≤ pendingPrimeProgress (r + 1) t - pendingPrimeProgress r s +
      primeLogWeightConstant * activationWeight s t := by
  have hid := pendingPrimeProgress_step r s
  cases ht with
  | idle => simpa only [activationWeight, sub_self, mul_zero, add_zero] using le_of_eq hid.symm
  | pending g hready hfuture hmin =>
      have hg : 2 < g.prime := by have := hs.ready_floor; omega
      have hnext := pendingProgress_replace (r := r) (s := s) primeLogPrefix (primeLogPrefix_nonneg (r + 1)) g hg hmin
      change pendingPrimeProgress (r + 1) s ≤ pendingPrimeProgress (r + 1) {s with pending := some g} at hnext
      simp only [activationWeight, sub_self, mul_zero, add_zero]
      linarith
  | activate g hready heq =>
      have hn : g.prime ∉ s.guards := by intro hp; have := hs.guards_past _ hp; omega
      have haw : activationWeight s (activatePrefixGuard s g) = stageWeight s.guards.card := by
        change stageReserve s.guards.card - stageReserve (insert g.prime s.guards).card = _
        rw [Finset.card_insert_of_notMem hn, stageReserve_step]
      have hb := pendingPrimeProgress_bound hs
      rw [haw]
      change pendingPrimeIntensity r s ≤ 0 - pendingPrimeProgress r s + _
      linarith

theorem activationWeight_sum (N : ℕ) (A : Finset ℕ) (ω : PrimeSample N) (n : ℕ) :
    (∑ r ∈ Finset.range n, activationWeight (prefixSchedule N A ω r) (prefixSchedule N A ω (r + 1))) ≤ 4 := by
  have h := sum_range_differences (fun r => stageReserve (prefixSchedule N A ω r).guards.card) n
  have hi : stageReserve (prefixSchedule N A ω 0).guards.card = 4 := by
    simpa only [prefixSchedule, initialPrefixSchedule, Finset.card_empty] using stageReserve_zero
  have hn := stageReserve_nonneg (prefixSchedule N A ω n).guards.card
  have heq : (∑ r ∈ Finset.range n, activationWeight (prefixSchedule N A ω r) (prefixSchedule N A ω (r + 1))) =
      - ∑ r ∈ Finset.range n, (stageReserve (prefixSchedule N A ω (r + 1)).guards.card -
        stageReserve (prefixSchedule N A ω r).guards.card) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro r _
    unfold activationWeight
    ring
  rw [heq, h, hi]
  linarith

theorem pendingPrimeIntensity_sum (N : ℕ) (A : Finset ℕ) (hA : ∀ a ∈ A, a ≤ N)
    (ω : PrimeSample N) :
    (∑ r ∈ Finset.range (N + 1), pendingPrimeIntensity r (prefixSchedule N A ω r)) ≤ 4 * primeLogWeightConstant := by
  have hsum := Finset.sum_le_sum (fun r (_ : r ∈ Finset.range (N + 1)) =>
    pendingPrimeIntensity_transition (prefixSchedule_timing N A ω r) (prefixSchedule_transition N A ω r))
  have hv := sum_range_differences (fun r => pendingPrimeProgress r (prefixSchedule N A ω r)) (N + 1)
  have hv0 : pendingPrimeProgress 0 (prefixSchedule N A ω 0) = 0 := rfl
  have hvN : pendingPrimeProgress (N + 1) (prefixSchedule N A ω (N + 1)) = 0 := by
    simp only [pendingPrimeProgress, pendingProgress, prefixSchedule_final_pending N A hA ω]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hv, hv0, hvN, sub_self, zero_add] at hsum
  exact hsum.trans (by nlinarith [activationWeight_sum N A ω (N + 1), primeLogWeightConstant_pos])

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/DelayPotential.lean -/
section
/- # A finite prime-mass potential for delayed stages -/

namespace Erdos12Proof

noncomputable def delayPrimeMass (r : ℕ) (s : PrefixScheduleState) : ℝ :=
  ∑ p ∈ Finset.range r, if p.Prime ∧ s.delayStart ≤ p ∧ p < s.readyAt then (1 / p : ℝ) else 0

noncomputable def delayProgress (r : ℕ) (s : PrefixScheduleState) : ℝ :=
  if s.delayStart = 0 then 0 else stageWeight s.delayGuards.card * delayPrimeMass r s

noncomputable def delayCoefficient (r : ℕ) (s : PrefixScheduleState) : ℝ :=
  if 4 ≤ r ∧ r < s.readyAt then stageWeight s.delayGuards.card else 0

noncomputable def delayIntensity (r : ℕ) (s : PrefixScheduleState) : ℝ :=
  if r.Prime then delayCoefficient r s / r else 0

noncomputable def delayRemainder (r : ℕ) (s : PrefixScheduleState) : ℝ :=
  if s.delayStart = 0 then 0 else
    primeDelayBudgetConstant * stageWeight s.delayGuards.card - delayProgress r s

noncomputable def delayBalance (r : ℕ) (s : PrefixScheduleState) : ℝ :=
  primeDelayBudgetConstant * stageReserve s.guards.card + delayRemainder r s

theorem delayPrimeMass_nonneg (r : ℕ) (s : PrefixScheduleState) : 0 ≤ delayPrimeMass r s := by
  apply Finset.sum_nonneg
  intro p _
  split_ifs <;> positivity

theorem delayProgress_nonneg (r : ℕ) (s : PrefixScheduleState) : 0 ≤ delayProgress r s := by
  unfold delayProgress
  split_ifs
  · exact le_refl _
  · exact mul_nonneg (stageWeight_nonneg _) (delayPrimeMass_nonneg _ _)

theorem delayPrimeMass_bound {r : ℕ} {s : PrefixScheduleState}
    (hg : ScheduleGeometryValid r s) (hne : s.delayStart ≠ 0) :
    delayPrimeMass r s ≤ primeDelayBudgetConstant := by
  classical
  let S := (Finset.range r).filter (fun p => p.Prime ∧ s.delayStart ≤ p ∧ p < s.readyAt)
  have hS : ∀ p ∈ S, p.Prime := by intro p hp; exact (Finset.mem_filter.mp hp).2.1
  have hP : (4 : ℝ) ≤ s.delayStart := by exact_mod_cast (hg.delay_data hne).1
  have hinterval : ∀ p ∈ S, (s.delayStart : ℝ) ≤ p ∧
      (p : ℝ) ≤ (s.delayStart : ℝ) ^ (primeTailExponent + 1) := by
    intro p hp
    have hi := (Finset.mem_filter.mp hp).2.2
    constructor
    · exact_mod_cast hi.1
    · exact_mod_cast hi.2.le.trans (hg.delay_window hne)
  have hb := delay_prime_budget S hS (s.delayStart : ℝ) hP hinterval
  simpa only [S, harmonic, Finset.sum_filter, delayPrimeMass] using hb

theorem delayRemainder_nonneg {r : ℕ} {s : PrefixScheduleState}
    (hg : ScheduleGeometryValid r s) : 0 ≤ delayRemainder r s := by
  unfold delayRemainder
  split_ifs with hzero
  · exact le_refl _
  · rw [delayProgress, ite_eq_right hzero]
    have h := mul_le_mul_of_nonneg_left (delayPrimeMass_bound hg hzero) (stageWeight_nonneg s.delayGuards.card)
    nlinarith

theorem delayBalance_nonneg {r : ℕ} {s : PrefixScheduleState}
    (hg : ScheduleGeometryValid r s) : 0 ≤ delayBalance r s :=
  add_nonneg (mul_nonneg primeDelayBudgetConstant_pos.le (stageReserve_nonneg _)) (delayRemainder_nonneg hg)

theorem delayProgress_step {r : ℕ} {s : PrefixScheduleState} (hg : ScheduleGeometryValid r s) :
    delayProgress (r + 1) s - delayProgress r s = delayIntensity r s := by
  by_cases hzero : s.delayStart = 0
  · have hready := hg.empty_ready hzero
    have hcond : ¬ (4 ≤ r ∧ r < s.readyAt) := by omega
    simp only [delayProgress, ite_eq_left hzero, sub_self, delayIntensity,
      delayCoefficient, ite_eq_right hcond, zero_div, ite_self]
  · have hstart := (hg.delay_data hzero).1
    have hr4 : 4 ≤ r := hstart.trans hg.start_past
    have hstep : delayPrimeMass (r + 1) s = delayPrimeMass r s +
        (if r.Prime ∧ s.delayStart ≤ r ∧ r < s.readyAt then (1 / r : ℝ) else 0) :=
      Finset.sum_range_succ _ _
    rw [delayProgress, delayProgress, ite_eq_right hzero, ite_eq_right hzero, hstep]
    simp only [delayIntensity, delayCoefficient]
    by_cases hp : r.Prime <;> by_cases hr : r < s.readyAt <;>
      simp only [hp, hr, hr4, hg.start_past, and_self, and_true, and_false, ite_true, ite_false] <;> ring

theorem delayBalance_same_state {r : ℕ} {s : PrefixScheduleState} (hg : ScheduleGeometryValid r s) :
    delayIntensity r s = delayBalance r s - delayBalance (r + 1) s := by
  have hstep := delayProgress_step hg
  by_cases hzero : s.delayStart = 0
  · have hp0 : delayProgress r s = 0 := by simp only [delayProgress, ite_eq_left hzero]
    have hp1 : delayProgress (r + 1) s = 0 := by simp only [delayProgress, ite_eq_left hzero]
    simp only [delayBalance, delayRemainder, ite_eq_left hzero, add_zero, sub_self]
    linarith
  · simp only [delayBalance, delayRemainder, ite_eq_right hzero]
    linarith

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/DelayScheduleBudget.lean -/
section
/- # The uniform total predictable cost of delayed coordinates -/

namespace Erdos12Proof

theorem delayIntensity_transition {r : ℕ} {s t : PrefixScheduleState}
    (hs : ScheduleTimingValid r s) (hg : ScheduleGeometryValid r s) (ht : PrefixTransition r s t) :
    delayIntensity r s ≤ delayBalance r s - delayBalance (r + 1) t := by
  cases ht with
  | idle => exact le_of_eq (delayBalance_same_state hg)
  | pending g hready hfuture hmin =>
      change delayIntensity r s ≤ delayBalance r s - delayBalance (r + 1) s
      exact le_of_eq (delayBalance_same_state hg)
  | activate g hready heq =>
      have hr4 : 4 ≤ r := hs.ready_floor.trans hready
      have hgn : g.prime ≠ 0 := by omega
      have hn : g.prime ∉ s.guards := by intro hp; have := hs.guards_past _ hp; omega
      have hc : (insert g.prime s.guards).card = s.guards.card + 1 := Finset.card_insert_of_notMem hn
      have hnew : delayBalance (r + 1) (activatePrefixGuard s g) =
          primeDelayBudgetConstant * stageReserve (s.guards.card + 1) +
          primeDelayBudgetConstant * stageWeight s.guards.card - delayProgress (r + 1) (activatePrefixGuard s g) := by
        change primeDelayBudgetConstant * stageReserve (insert g.prime s.guards).card +
          (if g.prime = 0 then 0 else primeDelayBudgetConstant * stageWeight s.guards.card -
            delayProgress (r + 1) (activatePrefixGuard s g)) = _
        rw [hc, ite_eq_right hgn]
        ring
      have hlow := delayRemainder_nonneg hg
      have hprogress := delayProgress_nonneg (r + 1) (activatePrefixGuard s g)
      have hstep := stageReserve_step s.guards.card
      have hscaled := congrArg (fun x => primeDelayBudgetConstant * x) hstep
      have hnewle : delayBalance (r + 1) (activatePrefixGuard s g) ≤
          primeDelayBudgetConstant * stageReserve s.guards.card := by
        rw [hnew]
        nlinarith [hscaled]
      have hold : primeDelayBudgetConstant * stageReserve s.guards.card ≤ delayBalance r s := by
        unfold delayBalance
        linarith
      have hcost : delayIntensity r s = 0 := by
        have hcond : ¬ (4 ≤ r ∧ r < s.readyAt) := by omega
        simp only [delayIntensity, delayCoefficient, ite_eq_right hcond, zero_div, ite_self]
      rw [hcost]
      linarith

theorem delayIntensity_sum (N : ℕ) (A : Finset ℕ) (ω : PrimeSample N) (n : ℕ) :
    (∑ r ∈ Finset.range n, delayIntensity r (prefixSchedule N A ω r)) ≤ 4 * primeDelayBudgetConstant := by
  have hsum := Finset.sum_le_sum (fun r (_ : r ∈ Finset.range n) =>
    delayIntensity_transition (prefixSchedule_timing N A ω r) (prefixSchedule_geometry N A ω r)
      (prefixSchedule_transition N A ω r))
  have ht := sum_range_differences (fun r => delayBalance r (prefixSchedule N A ω r)) n
  have hz : delayBalance 0 (prefixSchedule N A ω 0) = 4 * primeDelayBudgetConstant := by
    simp only [delayBalance, delayRemainder, prefixSchedule, initialPrefixSchedule,
      Finset.card_empty, ite_true, stageReserve_zero, add_zero]
    ring
  have heq : (∑ r ∈ Finset.range n, (delayBalance r (prefixSchedule N A ω r) -
      delayBalance (r + 1) (prefixSchedule N A ω (r + 1)))) =
      -(∑ r ∈ Finset.range n, (delayBalance (r + 1) (prefixSchedule N A ω (r + 1)) -
        delayBalance r (prefixSchedule N A ω r))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [heq, ht, hz] at hsum
  exact hsum.trans (by linarith [delayBalance_nonneg (prefixSchedule_geometry N A ω n)])

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/ScheduleScorePreparations.lean -/
section
/- # Prefix-score bounds at one step of the adaptive schedule -/

namespace Erdos12Proof

theorem firstCopyScore_guarded (N : ℕ) (A : Finset ℕ) (hA : PropertyP (A : Set ℕ))
    (ω : PrimeSample N) (p : primesThrough (N : ℝ)) (R : Finset ℕ) (sources : ℕ → ℕ)
    (hsource : ∀ q ∈ R, PrefixGuardValid N A ω ⟨q, sources q⟩)
    (hodd : ∀ q ∈ R, 2 < q) (hbefore : ∀ q ∈ R, q < p.val)
    (hthreshold : (primeModulus R : ℝ) ^ primeTailExponent ≤ p.val) :
    firstCopyScore N A ω p ≤ primeTailConstant * stageWeight R.card := by
  unfold firstCopyScore
  split_ifs with hhit
  · by_cases hzero : firstPrefixCandidate N ω p = 0
    · rw [hzero, prefixScore_zero]
      exact mul_nonneg primeTailConstant_pos.le (stageWeight_nonneg _)
    · have hspec := firstPrefixCandidate_spec_of_ne_zero hzero
      have hpre := firstPrefixCandidate_is_prefix ⟨_, hspec⟩ hhit
      have hb := guarded_prefix_score_bound N A hA ω R sources _ hspec.1 hpre hsource hodd
        (by simpa only [hspec.2.2.1] using hbefore) (by simpa only [hspec.2.2.1] using hthreshold)
      simpa only [stageWeight, mul_assoc] using hb
  · exact mul_nonneg primeTailConstant_pos.le (stageWeight_nonneg _)

theorem proposed_none_score {N : ℕ} (A : Finset ℕ) (ω : PrimeSample N)
    (p : primesThrough (N : ℝ)) (h : proposedPrefixGuard N A ω p.val = none) :
    prefixScore A (firstPrefixCandidate N ω p) = 0 := by
  classical
  by_cases hz : firstPrefixCandidate N ω p = 0
  · rw [hz, prefixScore_zero]
  · have hs := firstPrefixCandidate_spec_of_ne_zero hz
    have he : ¬ (finitePrimeFibre A (firstPrefixCandidate N ω p)).Nonempty := by
      intro hne
      have hh : 2 ≤ firstPrefixCandidate N ω p ∧ (finitePrimeFibre A (firstPrefixCandidate N ω p)).Nonempty := ⟨hs.1, hne⟩
      unfold proposedPrefixGuard at h
      rw [dite_eq_left p.property] at h
      change (if 2 ≤ firstPrefixCandidate N ω p ∧ (finitePrimeFibre A (firstPrefixCandidate N ω p)).Nonempty
        then some _ else none) = none at h
      rw [ite_eq_left hh] at h
      cases h
    have hf : finitePrimeFibre A (firstPrefixCandidate N ω p) = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    simp only [prefixScore, hf, harmonic, Finset.sum_empty, mul_zero]

theorem proposed_some_score {N : ℕ} {A : Finset ℕ} {ω : PrimeSample N}
    (p : primesThrough (N : ℝ)) {g : PrefixGuard} (h : proposedPrefixGuard N A ω p.val = some g) :
    prefixScore A (firstPrefixCandidate N ω p) = prefixScore A g.sourcePrefix := by
  obtain ⟨q, hq, hs, _⟩ := proposedPrefixGuard_spec h
  have hqp : q = p := Subtype.ext hq
  subst q
  rw [firstPrefixCandidate_eq hs]

theorem log_double_ratio {r P : ℕ} (hr : 2 ≤ r) (hrP : r ≤ P) :
    Real.log (2 * (r : ℝ)) / Real.log (2 * (P : ℝ)) ≤
      2 * (Real.log (r : ℝ) / Real.log (P : ℝ)) := by
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hPR : (2 : ℝ) ≤ P := by exact_mod_cast hr.trans hrP
  have hlr : 0 < Real.log (r : ℝ) := Real.log_pos (by linarith)
  have hlP : 0 < Real.log (P : ℝ) := Real.log_pos (by linarith)
  have hl2P : 0 < Real.log (2 * (P : ℝ)) := Real.log_pos (by linarith)
  have hl2r : Real.log (2 * (r : ℝ)) ≤ 2 * Real.log (r : ℝ) := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hrR
    linarith
  have hden : Real.log (P : ℝ) ≤ Real.log (2 * (P : ℝ)) :=
    Real.log_le_log (by linarith) (by linarith)
  calc
    _ ≤ (2 * Real.log (r : ℝ)) / Real.log (2 * (P : ℝ)) := div_le_div_of_nonneg_right hl2r hl2P.le
    _ ≤ (2 * Real.log (r : ℝ)) / Real.log (P : ℝ) :=
      div_le_div_of_nonneg_left (by linarith) hlP hden
    _ = _ := by ring

theorem ready_proposal_ratio {N r : ℕ} {A : Finset ℕ} (hA : PropertyP (A : Set ℕ))
    {ω : PrimeSample N} {s : PrefixScheduleState} (hs : ScheduleTimingValid r s)
    (hh : ScheduleHistoryValid N A ω s) (hgeo : ScheduleGeometryValid r s)
    (hready : s.readyAt ≤ r) {g : PrefixGuard}
    (hg : PrefixGuardValid N A ω g) (hmax : g.sourcePrefix.maxPrimeFac = r) :
    prefixScore A g.sourcePrefix ≤ 2 * primeTailConstant * stageWeight s.guards.card *
      (Real.log (r : ℝ) / Real.log (g.prime : ℝ)) := by
  have hthreshold : (primeModulus s.guards : ℝ) ^ primeTailExponent ≤ g.sourcePrefix.maxPrimeFac := by
    rw [hmax]
    exact_mod_cast hgeo.threshold.trans hready
  have hb := guarded_prefix_score_ratio N A hA ω s.guards s.sources g.sourcePrefix hg.1 hg.2.2.1 hg.2.2.2.1
    hh.1 hs.guards_odd (by intro q hq; rw [hmax]; exact hs.guards_past q hq) hthreshold
  rw [hmax, ← hg.2.2.2.2] at hb
  have hweight : 0 ≤ primeTailConstant * stageWeight s.guards.card :=
    mul_nonneg primeTailConstant_pos.le (stageWeight_nonneg _)
  have hlog := log_double_ratio (show 2 ≤ r by have := hs.ready_floor; omega)
    (by simpa only [hmax] using hg.source_max_le)
  have hb' : prefixScore A g.sourcePrefix ≤ primeTailConstant * stageWeight s.guards.card *
      (Real.log (2 * (r : ℝ)) / Real.log (2 * (g.prime : ℝ))) := by
    simpa only [stageWeight, mul_assoc] using hb
  calc
    _ ≤ primeTailConstant * stageWeight s.guards.card *
        (2 * (Real.log (r : ℝ) / Real.log (g.prime : ℝ))) :=
      hb'.trans (mul_le_mul_of_nonneg_left hlog hweight)
    _ = _ := by ring

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/ReadyScorePotential.lean -/
section
/- # Charging a ready prefix to its pending-guard potential -/

namespace Erdos12Proof

theorem choosePendingGuard_le_new (old : Option PrefixGuard) (g : PrefixGuard) :
    (choosePendingGuard old g).prime ≤ g.prime := by
  cases old with
  | none => exact le_refl _
  | some q =>
      change (if q.prime ≤ g.prime then q else g).prime ≤ g.prime
      split_ifs with h
      · exact h
      · exact le_refl _

theorem activationWeight_activate {r : ℕ} {s : PrefixScheduleState}
    (hs : ScheduleTimingValid r s) (g : PrefixGuard) (heq : g.prime = r) :
    activationWeight s (activatePrefixGuard s g) = stageWeight s.guards.card := by
  have hn : g.prime ∉ s.guards := by intro hp; have := hs.guards_past _ hp; omega
  change stageReserve s.guards.card - stageReserve (insert g.prime s.guards).card = _
  rw [Finset.card_insert_of_notMem hn, stageReserve_step]

theorem ready_activated_score {N : ℕ} (A : Finset ℕ) (hA : PropertyP (A : Set ℕ))
    (ω : PrimeSample N) (p : primesThrough (N : ℝ)) (s : PrefixScheduleState)
    (hs : ScheduleTimingValid p.val s) (hh : ScheduleHistoryValid N A ω s)
    (hgeo : ScheduleGeometryValid p.val s) (hready : s.readyAt ≤ p.val)
    (g : PrefixGuard) (heq : g.prime = p.val) :
    firstCopyScore N A ω p ≤ 4 * primeTailConstant *
      ((if 1 ≤ (ω p).val then pendingLogProgress p.val s else 0) +
        pendingLogProgress (p.val + 1) (activatePrefixGuard s g) - pendingLogProgress p.val s +
        2 * activationWeight s (activatePrefixGuard s g)) := by
  have hbound := firstCopyScore_guarded N A hA ω p s.guards s.sources hh.1 hs.guards_odd hs.guards_past
    (by exact_mod_cast hgeo.threshold.trans hready)
  have hQ := pendingLogProgress_le_weight hs (by have := hs.ready_floor; omega)
  have hQ0 := pendingLogProgress_nonneg hs
  have hI : 0 ≤ (if 1 ≤ (ω p).val then pendingLogProgress p.val s else 0) := by split_ifs <;> positivity
  rw [activationWeight_activate hs g heq]
  change firstCopyScore N A ω p ≤ 4 * primeTailConstant *
    ((if 1 ≤ (ω p).val then pendingLogProgress p.val s else 0) + 0 - pendingLogProgress p.val s +
      2 * stageWeight s.guards.card)
  have hw := stageWeight_nonneg s.guards.card
  have hC := primeTailConstant_pos
  nlinarith [mul_nonneg hC.le hI, mul_le_mul_of_nonneg_left hQ hC.le]

theorem record_proposal_score {N r : ℕ} {A : Finset ℕ} (hA : PropertyP (A : Set ℕ))
    {ω : PrimeSample N} (s : PrefixScheduleState) (hs : ScheduleTimingValid r s)
    (hh : ScheduleHistoryValid N A ω s) (hgeo : ScheduleGeometryValid r s)
    (hready : s.readyAt ≤ r) (g : PrefixGuard) (hg : PrefixGuardValid N A ω g)
    (hmax : g.sourcePrefix.maxPrimeFac = r) :
    prefixScore A g.sourcePrefix ≤ 4 * primeTailConstant *
      (pendingLogProgress (r + 1) (recordPrefixGuard s r g) +
        2 * activationWeight s (recordPrefixGuard s r g)) := by
  let q := choosePendingGuard s.pending g
  have hr4 : 4 ≤ r := hs.ready_floor.trans hready
  have hgp : r ≤ g.prime := by simpa only [hmax] using hg.source_max_le
  have hqg : q.prime ≤ g.prime := choosePendingGuard_le_new _ _
  have hqr : r ≤ q.prime := by
    rcases choosePendingGuard_cases s.pending g with he | ⟨v, hv, he⟩
    · change r ≤ (choosePendingGuard s.pending g).prime; rw [he]; exact hgp
    · change r ≤ (choosePendingGuard s.pending g).prime; rw [he]; exact (hs.pending_next v hv).1
  have hb := ready_proposal_ratio hA hs hh hgeo hready hg hmax
  have hweight := stageWeight_nonneg s.guards.card
  have hC := primeTailConstant_pos
  have hlogg : 0 < Real.log (g.prime : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < g.prime by omega))
  have hlogr : 0 ≤ Real.log (r : ℝ) := Real.log_natCast_nonneg r
  change prefixScore A g.sourcePrefix ≤ 4 * primeTailConstant *
    (pendingLogProgress (r + 1) (if q.prime ≤ r then activatePrefixGuard s q else {s with pending := some q}) +
      2 * activationWeight s (if q.prime ≤ r then activatePrefixGuard s q else {s with pending := some q}))
  split_ifs with htime
  · have hqe : q.prime = r := by omega
    rw [activationWeight_activate hs q hqe]
    change prefixScore A g.sourcePrefix ≤ 4 * primeTailConstant * (0 + 2 * stageWeight s.guards.card)
    have hlogle : Real.log (r : ℝ) ≤ Real.log (g.prime : ℝ) :=
      Real.log_le_log (by exact_mod_cast (show 0 < r by omega)) (by exact_mod_cast hgp)
    have hratio : Real.log (r : ℝ) / Real.log (g.prime : ℝ) ≤ 1 := (div_le_one hlogg).mpr hlogle
    have hscale := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 2 * primeTailConstant * stageWeight s.guards.card by positivity)
    nlinarith [hb, hscale]
  · have hql : 0 < Real.log (q.prime : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < q.prime by omega))
    have hden : Real.log (q.prime : ℝ) ≤ Real.log (g.prime : ℝ) :=
      Real.log_le_log (by exact_mod_cast (show 0 < q.prime by omega)) (by exact_mod_cast hqg)
    have hnum : Real.log (r : ℝ) ≤ Real.log ((r + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast (show 0 < r by omega)) (by exact_mod_cast Nat.le_succ r)
    have hratio : Real.log (r : ℝ) / Real.log (g.prime : ℝ) ≤
        Real.log ((r + 1 : ℕ) : ℝ) / Real.log (q.prime : ℝ) :=
      (div_le_div_of_nonneg_left hlogr hql hden).trans (div_le_div_of_nonneg_right hnum hql.le)
    have hscale := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 2 * primeTailConstant * stageWeight s.guards.card by positivity)
    change prefixScore A g.sourcePrefix ≤ 4 * primeTailConstant *
      (stageWeight s.guards.card * Real.log ((r + 1 : ℕ) : ℝ) / Real.log (q.prime : ℝ) +
        2 * (stageReserve s.guards.card - stageReserve s.guards.card))
    have hpos : 0 ≤ stageWeight s.guards.card * Real.log ((r + 1 : ℕ) : ℝ) / Real.log (q.prime : ℝ) :=
      div_nonneg (mul_nonneg hweight (Real.log_natCast_nonneg _)) hql.le
    calc
      _ ≤ 2 * primeTailConstant * stageWeight s.guards.card *
          (Real.log ((r + 1 : ℕ) : ℝ) / Real.log (q.prime : ℝ)) := hb.trans hscale
      _ = 2 * primeTailConstant *
          (stageWeight s.guards.card * Real.log ((r + 1 : ℕ) : ℝ) / Real.log (q.prime : ℝ)) := by ring
      _ ≤ 4 * primeTailConstant *
          (stageWeight s.guards.card * Real.log ((r + 1 : ℕ) : ℝ) / Real.log (q.prime : ℝ)) :=
        mul_le_mul_of_nonneg_right (by linarith) hpos
      _ = _ := by ring

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/ReadyScoreStep.lean -/
section
/- # The complete one-step estimate during a ready stage -/

namespace Erdos12Proof

noncomputable def primeHitDecidable (N : ℕ) (ω : PrimeSample N) (r : ℕ) :
    Decidable (primeHit N ω r) := by
  unfold primeHit
  infer_instance

theorem ready_step_bracket_nonneg {N r : ℕ} (A : Finset ℕ) (ω : PrimeSample N)
    (s : PrefixScheduleState) (hs : ScheduleTimingValid r s) (hready : s.readyAt ≤ r) :
    0 ≤ (if primeHit N ω r then pendingLogProgress r s else 0) +
      pendingLogProgress (r + 1) (prefixScheduleStep N A ω r s) - pendingLogProgress r s +
      2 * activationWeight s (prefixScheduleStep N A ω r s) := by
  have ht := prefixScheduleStep_transition (N := N) (A := A) (ω := ω) s hs
  have hq := pendingLogProgress_transition hs ht (by have := hs.ready_floor; omega)
  have ha := activationWeight_nonneg ht hs
  have hi : 0 ≤ (if primeHit N ω r then pendingLogProgress r s else 0) := by
    split_ifs
    · exact pendingLogProgress_nonneg hs
    · exact le_refl _
  linarith

theorem primeHit_at_prime {N : ℕ} (ω : PrimeSample N) (p : primesThrough (N : ℝ)) :
    primeHit N ω p.val ↔ 1 ≤ (ω p).val := by
  constructor
  · rintro ⟨q, hq, hh⟩
    have he : q = p := Subtype.ext hq
    simpa only [he] using hh
  · intro h
    exact ⟨p, rfl, h⟩

theorem ready_firstCopy_step {N : ℕ} (A : Finset ℕ) (hA : PropertyP (A : Set ℕ))
    (ω : PrimeSample N) (p : primesThrough (N : ℝ)) (s : PrefixScheduleState)
    (hs : ScheduleTimingValid p.val s) (hh : ScheduleHistoryValid N A ω s)
    (hg : ScheduleGeometryValid p.val s) (hready : s.readyAt ≤ p.val) :
    firstCopyScore N A ω p ≤ 4 * primeTailConstant *
      ((if primeHit N ω p.val then pendingLogProgress p.val s else 0) +
        pendingLogProgress (p.val + 1) (prefixScheduleStep N A ω p.val s) - pendingLogProgress p.val s +
        2 * activationWeight s (prefixScheduleStep N A ω p.val s)) := by
  have hnonneg := ready_step_bracket_nonneg A ω s hs hready
  by_cases hhit : 1 ≤ (ω p).val
  · have hhit' : primeHit N ω p.val := (primeHit_at_prime ω p).mpr hhit
    cases hprop : proposedPrefixGuard N A ω p.val with
    | none =>
        have hz : firstCopyScore N A ω p = 0 := by
          rw [firstCopyScore, ite_eq_left hhit, proposed_none_score A ω p hprop]
        rw [hz]
        exact mul_nonneg (mul_nonneg (by norm_num) primeTailConstant_pos.le) hnonneg
    | some g =>
        obtain ⟨hvalid, hmax, _⟩ := proposedPrefixGuard_valid hprop hhit'
        have hrecord : firstCopyScore N A ω p ≤ 4 * primeTailConstant *
            ((if primeHit N ω p.val then pendingLogProgress p.val s else 0) +
              pendingLogProgress (p.val + 1) (recordPrefixGuard s p.val g) - pendingLogProgress p.val s +
              2 * activationWeight s (recordPrefixGuard s p.val g)) := by
          rw [firstCopyScore, ite_eq_left hhit, proposed_some_score p hprop, ite_eq_left hhit']
          have hb := record_proposal_score hA s hs hh hg hready g hvalid hmax
          convert hb using 1; ring
        have hprocess : processReadyPrefix N A ω p.val s = recordPrefixGuard s p.val g := by
          simp only [processReadyPrefix, ite_eq_left hhit', hprop]
        unfold prefixScheduleStep
        rw [ite_eq_right (Nat.not_lt.mpr hready)]
        cases hp : s.pending with
        | none => simpa only [hprocess] using hrecord
        | some q =>
            change firstCopyScore N A ω p ≤ 4 * primeTailConstant *
              ((if primeHit N ω p.val then pendingLogProgress p.val s else 0) +
                pendingLogProgress (p.val + 1) (if q.prime ≤ p.val then activatePrefixGuard s q else processReadyPrefix N A ω p.val s) -
                pendingLogProgress p.val s + 2 * activationWeight s
                  (if q.prime ≤ p.val then activatePrefixGuard s q else processReadyPrefix N A ω p.val s))
            split_ifs with htime
            · have heq : q.prime = p.val := by have := (hs.pending_next q hp).1; omega
              simpa only [ite_eq_left hhit] using ready_activated_score A hA ω p s hs hh hg hready q heq
            · simpa only [hprocess, ite_eq_left hhit'] using hrecord
  · have hz : firstCopyScore N A ω p = 0 := by simp only [firstCopyScore, ite_eq_right hhit]
    rw [hz]
    exact mul_nonneg (mul_nonneg (by norm_num) primeTailConstant_pos.le) hnonneg

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/FullScoreStep.lean -/
section
/- # A score bound covering the initial, delayed, and ready coordinates -/

namespace Erdos12Proof

theorem delayed_firstCopy_score {N : ℕ} (A : Finset ℕ) (hA : PropertyP (A : Set ℕ))
    (ω : PrimeSample N) (p : primesThrough (N : ℝ)) (s : PrefixScheduleState)
    (hs : ScheduleTimingValid p.val s) (hh : ScheduleHistoryValid N A ω s)
    (hg : ScheduleGeometryValid p.val s) (hr4 : 4 ≤ p.val) (hdelay : p.val < s.readyAt) :
    firstCopyScore N A ω p ≤ primeTailConstant * stageWeight s.delayGuards.card := by
  have hne : s.delayStart ≠ 0 := by intro hz; have := hg.empty_ready hz; omega
  obtain ⟨_, hguards, _, hbefore, hbase, _⟩ := hg.delay_data hne
  have hsub : s.delayGuards ⊆ s.guards := by
    rw [hguards]
    exact Finset.subset_insert _ _
  exact firstCopyScore_guarded N A hA ω p s.delayGuards s.sources
    (fun q hq => hh.1 q (hsub hq)) (fun q hq => hs.guards_odd q (hsub hq))
    (fun q hq => (hbefore q hq).trans_le hg.start_past)
    (by exact_mod_cast hbase.trans hg.start_past)

noncomputable def initialCoefficient (r : ℕ) : ℝ := if r < 4 then 1 else 0

noncomputable def hitCharge (N : ℕ) (ω : PrimeSample N) (r : ℕ) (c : ℝ) : ℝ := by
  classical
  exact if primeHit N ω r then c else 0

noncomputable def scheduleScoreBudget (N : ℕ) (A : Finset ℕ) (ω : PrimeSample N) (r : ℕ) : ℝ :=
  let s := prefixSchedule N A ω r
  let t := prefixSchedule N A ω (r + 1)
  primeTailConstant * hitCharge N ω r (initialCoefficient r + delayCoefficient r s) +
    4 * primeTailConstant * (hitCharge N ω r (pendingLogProgress r s) +
      pendingLogProgress (r + 1) t - pendingLogProgress r s + 2 * activationWeight s t)

theorem firstCopy_score_step {N : ℕ} (A : Finset ℕ) (hA : PropertyP (A : Set ℕ))
    (ω : PrimeSample N) (p : primesThrough (N : ℝ)) :
    firstCopyScore N A ω p ≤ scheduleScoreBudget N A ω p.val := by
  classical
  let s := prefixSchedule N A ω p.val
  have hs := prefixSchedule_timing N A ω p.val
  have hh := prefixSchedule_history N A ω p.val
  have hg := prefixSchedule_geometry N A ω p.val
  change ScheduleTimingValid p.val s at hs
  change ScheduleHistoryValid N A ω s at hh
  change ScheduleGeometryValid p.val s at hg
  change firstCopyScore N A ω p ≤
    primeTailConstant * hitCharge N ω p.val (initialCoefficient p.val + delayCoefficient p.val s) +
      4 * primeTailConstant * (hitCharge N ω p.val (pendingLogProgress p.val s) +
        pendingLogProgress (p.val + 1) (prefixScheduleStep N A ω p.val s) - pendingLogProgress p.val s +
        2 * activationWeight s (prefixScheduleStep N A ω p.val s))
  by_cases hdelay : p.val < s.readyAt
  · have hstep : prefixScheduleStep N A ω p.val s = s := by
      rw [prefixScheduleStep, ite_eq_left hdelay]
    have hpending := hs.pending_clear hdelay
    have hq0 : pendingLogProgress p.val s = 0 := by simp only [pendingLogProgress, pendingProgress, hpending]
    have hq1 : pendingLogProgress (p.val + 1) s = 0 := by simp only [pendingLogProgress, pendingProgress, hpending]
    have haw : activationWeight s s = 0 := sub_self _
    rw [hstep, hq0, hq1, haw]
    simp only [hitCharge, ite_self, sub_self, mul_zero, add_zero]
    by_cases hr : p.val < 4
    · have hd : delayCoefficient p.val s = 0 := by
        rw [delayCoefficient, ite_eq_right (by omega)]
      rw [initialCoefficient, ite_eq_left hr, hd, add_zero]
      by_cases hhit : 1 ≤ (ω p).val
      · rw [ite_eq_left ((primeHit_at_prime ω p).mpr hhit)]
        simpa only [mul_one] using firstCopyScore_bound N A hA ω p
      · rw [ite_eq_right (by simpa only [primeHit_at_prime] using hhit), mul_zero]
        simp only [firstCopyScore, ite_eq_right hhit, le_refl]
    · have hr4 : 4 ≤ p.val := Nat.le_of_not_gt hr
      have hd : delayCoefficient p.val s = stageWeight s.delayGuards.card := by
        exact ite_eq_left ⟨hr4, hdelay⟩
      rw [initialCoefficient, ite_eq_right hr, hd, zero_add]
      by_cases hhit : 1 ≤ (ω p).val
      · rw [ite_eq_left ((primeHit_at_prime ω p).mpr hhit)]
        exact delayed_firstCopy_score A hA ω p s hs hh hg hr4 hdelay
      · rw [ite_eq_right (by simpa only [primeHit_at_prime] using hhit), mul_zero]
        simp only [firstCopyScore, ite_eq_right hhit, le_refl]
  · have hready : s.readyAt ≤ p.val := Nat.le_of_not_gt hdelay
    have hr4 : 4 ≤ p.val := hs.ready_floor.trans hready
    have hi : initialCoefficient p.val = 0 := by rw [initialCoefficient, ite_eq_right (by omega)]
    have hd : delayCoefficient p.val s = 0 := by rw [delayCoefficient, ite_eq_right (by omega)]
    rw [hi, hd, add_zero]
    simp only [hitCharge, ite_self, mul_zero, zero_add]
    exact ready_firstCopy_step A hA ω p s hs hh hg hready

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/ScheduleBudgetAggregation.lean -/
section
/- # Summing the pointwise prefix-score estimates -/

namespace Erdos12Proof

theorem initialCoefficient_nonneg (r : ℕ) : 0 ≤ initialCoefficient r := by
  unfold initialCoefficient
  split_ifs <;> norm_num

theorem delayCoefficient_nonneg (r : ℕ) (s : PrefixScheduleState) : 0 ≤ delayCoefficient r s := by
  unfold delayCoefficient
  split_ifs
  · exact stageWeight_nonneg _
  · exact le_refl _

theorem hitCharge_nonneg (N : ℕ) (ω : PrimeSample N) (r : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ hitCharge N ω r c := by
  unfold hitCharge
  split_ifs
  · exact hc
  · exact le_refl _

theorem scheduleScoreBudget_nonneg (N : ℕ) (A : Finset ℕ) (ω : PrimeSample N) (r : ℕ) :
    0 ≤ scheduleScoreBudget N A ω r := by
  have hs := prefixSchedule_timing N A ω r
  have ht := prefixSchedule_transition N A ω r
  have hfirst := hitCharge_nonneg N ω r (add_nonneg (initialCoefficient_nonneg r)
    (delayCoefficient_nonneg r (prefixSchedule N A ω r)))
  have hhit := hitCharge_nonneg N ω r (pendingLogProgress_nonneg hs)
  have ha := activationWeight_nonneg ht hs
  have hdiff : 0 ≤ pendingLogProgress (r + 1) (prefixSchedule N A ω (r + 1)) -
      pendingLogProgress r (prefixSchedule N A ω r) +
      activationWeight (prefixSchedule N A ω r) (prefixSchedule N A ω (r + 1)) := by
    by_cases hz : r = 0
    · subst r
      norm_num [prefixSchedule, initialPrefixSchedule, prefixScheduleStep,
        pendingLogProgress, pendingProgress, activationWeight]
    · exact pendingLogProgress_transition hs ht (by omega)
  unfold scheduleScoreBudget
  dsimp only
  apply add_nonneg (mul_nonneg primeTailConstant_pos.le hfirst)
  apply mul_nonneg (mul_nonneg (by norm_num) primeTailConstant_pos.le)
  linarith

theorem firstCopyScoreSum_le_budget (N : ℕ) (A : Finset ℕ) (hA : PropertyP (A : Set ℕ))
    (ω : PrimeSample N) :
    firstCopyScoreSum N A ω ≤ ∑ r ∈ Finset.range (N + 1), scheduleScoreBudget N A ω r := by
  classical
  have hsub : primesThrough (N : ℝ) ⊆ Finset.range (N + 1) := by
    intro p hp
    have hb := ((mem_primesThrough (Nat.cast_nonneg N)).mp hp).2
    have hn : p ≤ N := by exact_mod_cast hb
    exact Finset.mem_range.mpr (by omega)
  calc
    firstCopyScoreSum N A ω ≤ ∑ p : primesThrough (N : ℝ), scheduleScoreBudget N A ω p.val :=
      Finset.sum_le_sum (fun p _ => firstCopy_score_step A hA ω p)
    _ = ∑ p ∈ primesThrough (N : ℝ), scheduleScoreBudget N A ω p :=
      Finset.sum_coe_sort _ _
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun r _ _ => scheduleScoreBudget_nonneg N A ω r)

theorem pendingLogProgress_total_difference (N : ℕ) (A : Finset ℕ) (hA : ∀ a ∈ A, a ≤ N)
    (ω : PrimeSample N) :
    (∑ r ∈ Finset.range (N + 1), (pendingLogProgress (r + 1) (prefixSchedule N A ω (r + 1)) -
      pendingLogProgress r (prefixSchedule N A ω r))) = 0 := by
  rw [sum_range_differences (fun r => pendingLogProgress r (prefixSchedule N A ω r)) (N + 1)]
  have hn : pendingLogProgress (N + 1) (prefixSchedule N A ω (N + 1)) = 0 := by
    simp only [pendingLogProgress, pendingProgress, prefixSchedule_final_pending N A hA ω]
  have hz : pendingLogProgress 0 (prefixSchedule N A ω 0) = 0 := rfl
  rw [hn, hz, sub_self]

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/FiniteExpectationAlgebra.lean -/
section
/- # Elementary algebra for finite weighted expectations -/

namespace Erdos12Proof

variable {X : Type*} [Fintype X]

theorem weightedSum_add (w f g : X → ℝ) :
    weightedSum w (fun x => f x + g x) = weightedSum w f + weightedSum w g := by
  simp only [weightedSum, mul_add, Finset.sum_add_distrib]

theorem weightedSum_sub (w f g : X → ℝ) :
    weightedSum w (fun x => f x - g x) = weightedSum w f - weightedSum w g := by
  simp only [weightedSum, mul_sub, Finset.sum_sub_distrib]

theorem weightedSum_smul (w f : X → ℝ) (c : ℝ) :
    weightedSum w (fun x => c * f x) = c * weightedSum w f := by
  unfold weightedSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem weightedSum_const (w : X → ℝ) (hw : (∑ x, w x) = 1) (c : ℝ) :
    weightedSum w (fun _ => c) = c := by
  unfold weightedSum
  rw [← Finset.sum_mul, hw, one_mul]

theorem weightedSum_le_const (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (hm : (∑ x, w x) = 1)
    (f : X → ℝ) (c : ℝ) (h : ∀ x, f x ≤ c) : weightedSum w f ≤ c := by
  exact (weightedSum_mono w hw h).trans_eq (weightedSum_const w hm c)

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/ExpectedScheduleCosts.lean -/
section
/- # Conditional expectations of the predictable scheduling costs -/

namespace Erdos12Proof

theorem primeHit_not_prime {N r : ℕ} (ω : PrimeSample N) (hr : ¬ r.Prime) : ¬ primeHit N ω r := by
  rintro ⟨p, hp, _⟩
  have hprime := ((mem_primesThrough (Nat.cast_nonneg N)).mp p.property).1
  exact hr (hp ▸ hprime)

theorem expected_hit_state (N : ℕ) (A : Finset ℕ) (r : ℕ) (hrN : r ≤ N)
    (F : PrefixScheduleState → ℝ) :
    weightedSum (primeSampleWeight N) (fun ω => hitCharge N ω r (F (prefixSchedule N A ω r))) =
      weightedSum (primeSampleWeight N) (fun ω => if r.Prime then F (prefixSchedule N A ω r) / r else 0) := by
  classical
  by_cases hp : r.Prime
  · let p : primesThrough (N : ℝ) := ⟨r, (mem_primesThrough (Nat.cast_nonneg N)).mpr ⟨hp, by exact_mod_cast hrN⟩⟩
    have h := finiteGeometric_tail_pairing (fun q : primesThrough (N : ℝ) => (q.val : ℝ))
      (N + 1) p 1 (by omega) (fun ω => F (prefixSchedule N A ω r)) (by
        intro ω x
        rw [prefixSchedule_update_unrevealed A ω p x r (by rfl)])
    change weightedSum (primeSampleWeight N)
      (fun ω => if 1 ≤ (ω p).val then F (prefixSchedule N A ω r) else 0) =
        (1 / (r : ℝ)) ^ 1 * weightedSum (primeSampleWeight N) (fun ω => F (prefixSchedule N A ω r)) at h
    have hleft : (fun ω => hitCharge N ω r (F (prefixSchedule N A ω r))) =
        (fun ω => if 1 ≤ (ω p).val then F (prefixSchedule N A ω r) else 0) := by
      funext ω
      change (if primeHit N ω p.val then _ else _) = _
      simp only [primeHit_at_prime ω p]
    rw [hleft, h, pow_one]
    simp only [ite_eq_left hp]
    have hs := weightedSum_smul (primeSampleWeight N) (fun ω => F (prefixSchedule N A ω r)) (1 / (r : ℝ))
    convert hs.symm using 1
    congr 1
    funext ω
    ring
  · have hz (ω : PrimeSample N) : hitCharge N ω r (F (prefixSchedule N A ω r)) = 0 := by
      simp only [hitCharge, ite_eq_right (primeHit_not_prime ω hp)]
    simp only [hz, ite_eq_right hp]

noncomputable def initialIntensity (r : ℕ) : ℝ := if r.Prime then initialCoefficient r / r else 0

theorem initialIntensity_nonneg (r : ℕ) : 0 ≤ initialIntensity r := by
  unfold initialIntensity
  split_ifs
  · exact div_nonneg (initialCoefficient_nonneg r) (Nat.cast_nonneg r)
  · exact le_refl _

theorem initialIntensity_sum (n : ℕ) : (∑ r ∈ Finset.range n, initialIntensity r) ≤ 2 := by
  have hfour : (∑ r ∈ Finset.range 4, initialIntensity r) ≤ 2 := by
    norm_num [initialIntensity, initialCoefficient, Finset.sum_range_succ]
  by_cases hn : n ≤ 4
  · exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn)
      (fun r _ _ => initialIntensity_nonneg r)).trans hfour
  · have he : n = 4 + (n - 4) := by omega
    rw [he, Finset.sum_range_add]
    have hz : (∑ x ∈ Finset.range (n - 4), initialIntensity (4 + x)) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      have hge : ¬4 + x < 4 := by omega
      simp only [initialIntensity, initialCoefficient, ite_eq_right hge, zero_div, ite_self]
    rw [hz, add_zero]
    exact hfour

theorem expected_hit_pending (N : ℕ) (A : Finset ℕ) (r : ℕ) (hrN : r ≤ N) :
    weightedSum (primeSampleWeight N)
      (fun ω => hitCharge N ω r (pendingLogProgress r (prefixSchedule N A ω r))) =
    weightedSum (primeSampleWeight N)
      (fun ω => pendingPrimeIntensity r (prefixSchedule N A ω r)) :=
  expected_hit_state N A r hrN (pendingLogProgress r)

theorem expected_hit_initial_delay (N : ℕ) (A : Finset ℕ) (r : ℕ) (hrN : r ≤ N) :
    weightedSum (primeSampleWeight N)
      (fun ω => hitCharge N ω r (initialCoefficient r + delayCoefficient r (prefixSchedule N A ω r))) =
    weightedSum (primeSampleWeight N)
      (fun ω => initialIntensity r + delayIntensity r (prefixSchedule N A ω r)) := by
  rw [expected_hit_state N A r hrN (fun s => initialCoefficient r + delayCoefficient r s)]
  congr 1
  funext ω
  unfold initialIntensity delayIntensity
  split_ifs <;> ring

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/ExpectedPrefixBudget.lean -/
section
/- # A uniform expected bound for all first-copy prefix scores -/

namespace Erdos12Proof

noncomputable def initialDelayHitCost (N : ℕ) (A : Finset ℕ) (ω : PrimeSample N) : ℝ :=
  ∑ r ∈ Finset.range (N + 1), hitCharge N ω r
    (initialCoefficient r + delayCoefficient r (prefixSchedule N A ω r))

noncomputable def pendingHitCost (N : ℕ) (A : Finset ℕ) (ω : PrimeSample N) : ℝ :=
  ∑ r ∈ Finset.range (N + 1), hitCharge N ω r (pendingLogProgress r (prefixSchedule N A ω r))

noncomputable def totalActivationWeight (N : ℕ) (A : Finset ℕ) (ω : PrimeSample N) : ℝ :=
  ∑ r ∈ Finset.range (N + 1), activationWeight (prefixSchedule N A ω r) (prefixSchedule N A ω (r + 1))

theorem expected_initialDelayHitCost (N : ℕ) (A : Finset ℕ) :
    weightedSum (primeSampleWeight N) (initialDelayHitCost N A) ≤ 2 + 4 * primeDelayBudgetConstant := by
  have heq : weightedSum (primeSampleWeight N) (initialDelayHitCost N A) =
      weightedSum (primeSampleWeight N) (fun ω => ∑ r ∈ Finset.range (N + 1),
        (initialIntensity r + delayIntensity r (prefixSchedule N A ω r))) := by
    unfold initialDelayHitCost
    rw [weightedSum_finite_sum, weightedSum_finite_sum]
    apply Finset.sum_congr rfl
    intro r hr
    exact expected_hit_initial_delay N A r (by have := Finset.mem_range.mp hr; omega)
  rw [heq]
  apply weightedSum_le_const _ (primeSampleWeight_nonneg N) (primeSampleWeight_mass N)
  intro ω
  rw [Finset.sum_add_distrib]
  exact add_le_add (initialIntensity_sum (N + 1)) (delayIntensity_sum N A ω (N + 1))

theorem expected_pendingHitCost (N : ℕ) (A : Finset ℕ) (hA : ∀ a ∈ A, a ≤ N) :
    weightedSum (primeSampleWeight N) (pendingHitCost N A) ≤ 4 * primeLogWeightConstant := by
  have heq : weightedSum (primeSampleWeight N) (pendingHitCost N A) =
      weightedSum (primeSampleWeight N) (fun ω => ∑ r ∈ Finset.range (N + 1),
        pendingPrimeIntensity r (prefixSchedule N A ω r)) := by
    unfold pendingHitCost
    rw [weightedSum_finite_sum, weightedSum_finite_sum]
    apply Finset.sum_congr rfl
    intro r hr
    exact expected_hit_pending N A r (by have := Finset.mem_range.mp hr; omega)
  rw [heq]
  exact weightedSum_le_const _ (primeSampleWeight_nonneg N) (primeSampleWeight_mass N) _ _
    (pendingPrimeIntensity_sum N A hA)

theorem expected_totalActivationWeight (N : ℕ) (A : Finset ℕ) :
    weightedSum (primeSampleWeight N) (totalActivationWeight N A) ≤ 4 :=
  weightedSum_le_const _ (primeSampleWeight_nonneg N) (primeSampleWeight_mass N) _ _
    (fun ω => activationWeight_sum N A ω (N + 1))

theorem scheduleScoreBudget_sum (N : ℕ) (A : Finset ℕ) (hA : ∀ a ∈ A, a ≤ N) (ω : PrimeSample N) :
    (∑ r ∈ Finset.range (N + 1), scheduleScoreBudget N A ω r) =
      primeTailConstant * initialDelayHitCost N A ω + 4 * primeTailConstant * pendingHitCost N A ω +
        8 * primeTailConstant * totalActivationWeight N A ω := by
  have hp (r : ℕ) : scheduleScoreBudget N A ω r =
      primeTailConstant * hitCharge N ω r (initialCoefficient r + delayCoefficient r (prefixSchedule N A ω r)) +
      4 * primeTailConstant * hitCharge N ω r (pendingLogProgress r (prefixSchedule N A ω r)) +
      4 * primeTailConstant * (pendingLogProgress (r + 1) (prefixSchedule N A ω (r + 1)) -
        pendingLogProgress r (prefixSchedule N A ω r)) +
      8 * primeTailConstant * activationWeight (prefixSchedule N A ω r) (prefixSchedule N A ω (r + 1)) := by
    unfold scheduleScoreBudget
    ring
  simp only [hp, Finset.sum_add_distrib, ← Finset.mul_sum,
    pendingLogProgress_total_difference N A hA ω, mul_zero, add_zero,
    initialDelayHitCost, pendingHitCost, totalActivationWeight]

theorem expected_firstCopyScoreSum_bound (N : ℕ) (A : Finset ℕ)
    (hP : PropertyP (A : Set ℕ)) (hA : ∀ a ∈ A, a ≤ N) :
    weightedSum (primeSampleWeight N) (firstCopyScoreSum N A) ≤
      primeTailConstant * (34 + 4 * primeDelayBudgetConstant + 16 * primeLogWeightConstant) := by
  have h := weightedSum_mono (primeSampleWeight N) (primeSampleWeight_nonneg N)
    (firstCopyScoreSum_le_budget N A hP)
  have heq : weightedSum (primeSampleWeight N) (fun ω => ∑ r ∈ Finset.range (N + 1), scheduleScoreBudget N A ω r) =
      primeTailConstant * weightedSum (primeSampleWeight N) (initialDelayHitCost N A) +
      4 * primeTailConstant * weightedSum (primeSampleWeight N) (pendingHitCost N A) +
      8 * primeTailConstant * weightedSum (primeSampleWeight N) (totalActivationWeight N A) := by
    simp only [scheduleScoreBudget_sum N A hA, weightedSum_add, weightedSum_smul]
  rw [heq] at h
  have hC := primeTailConstant_pos.le
  have hI := mul_le_mul_of_nonneg_left (expected_initialDelayHitCost N A) hC
  have hQ := mul_le_mul_of_nonneg_left (expected_pendingHitCost N A hA) (show 0 ≤ 4 * primeTailConstant by positivity)
  have hG := mul_le_mul_of_nonneg_left (expected_totalActivationWeight N A) (show 0 ≤ 8 * primeTailConstant by positivity)
  nlinarith

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/OddReduction.lean -/
section
/-
# Reduction of primitive sets to odd primitive sets

A strong induction on a bound for the elements avoids introducing valuations.
It is the finite form of summing the weights of the powers of two.
-/

namespace Erdos12Proof

def evenHalves (B : Finset ℕ) : Finset ℕ :=
  (B.filter Even).image (fun n => n / 2)

theorem mem_evenHalves {B : Finset ℕ} {n : ℕ} :
    n ∈ evenHalves B ↔ 2 * n ∈ B := by
  constructor
  · intro hn
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hbB, hbEven⟩ := Finset.mem_filter.mp hb
    simpa only [Nat.mul_div_cancel' hbEven.two_dvd] using hbB
  · intro hn
    apply Finset.mem_image.mpr
    refine ⟨2 * n, Finset.mem_filter.mpr ⟨hn, ?_⟩, ?_⟩
    · exact even_iff_exists_two_mul.mpr ⟨n, rfl⟩
    · omega

theorem double_evenHalves (B : Finset ℕ) :
    (evenHalves B).image (fun n => 2 * n) = B.filter Even := by
  ext n
  constructor
  · intro hn
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_filter.mpr
      ⟨mem_evenHalves.mp hm, even_iff_exists_two_mul.mpr ⟨m, rfl⟩⟩
  · intro hn
    obtain ⟨hnB, hnEven⟩ := Finset.mem_filter.mp hn
    obtain ⟨m, hm⟩ := even_iff_exists_two_mul.mp hnEven
    apply Finset.mem_image.mpr
    exact ⟨m, mem_evenHalves.mpr (hm ▸ hnB), hm.symm⟩

theorem evenHalves_positive {B : Finset ℕ} (hB : Positive (B : Set ℕ)) :
    Positive (evenHalves B : Set ℕ) := by
  intro n hn
  have := hB (mem_evenHalves.mp hn)
  omega

theorem evenHalves_propertyP {B : Finset ℕ} (hB : PropertyP (B : Set ℕ)) :
    PropertyP (evenHalves B : Set ℕ) := by
  apply PropertyP.of_dilate (by decide : 0 < 2)
  apply hB.mono
  rintro n ⟨m, hm, rfl⟩
  exact mem_evenHalves.mp hm

theorem evenHalves_primitive {B : Finset ℕ} (hB : Primitive (B : Set ℕ)) :
    Primitive (evenHalves B : Set ℕ) := by
  apply Primitive.of_dilate (by decide : 0 < 2)
  apply hB.mono
  rintro n ⟨m, hm, rfl⟩
  exact mem_evenHalves.mp hm

theorem harmonic_evenHalves (B : Finset ℕ) :
    harmonic (B.filter Even) = (1 / 2 : ℝ) * harmonic (evenHalves B) := by
  rw [← double_evenHalves B]
  unfold harmonic
  rw [Finset.sum_image, Finset.mul_sum]
  · apply Finset.sum_congr rfl
    intro n _
    push_cast
    ring
  · intro a _ b _ hab
    change 2 * a = 2 * b at hab
    omega

theorem harmonic_parity_split (B : Finset ℕ) :
    harmonic B = harmonic (B.filter Odd) + (1 / 2 : ℝ) * harmonic (evenHalves B) := by
  rw [← harmonic_evenHalves]
  unfold harmonic
  simpa only [Nat.not_odd_iff_even] using
    (Finset.sum_filter_add_sum_filter_not B Odd (fun n => (1 / n : ℝ))).symm

theorem primitive_bound_of_odd_bound {C : ℝ}
    (hC : ∀ B : Finset ℕ, Positive (B : Set ℕ) → Primitive (B : Set ℕ) →
      PropertyP (B : Set ℕ) → (∀ n ∈ B, Odd n) → harmonic B ≤ C) :
    ∀ B : Finset ℕ, Positive (B : Set ℕ) → Primitive (B : Set ℕ) →
      PropertyP (B : Set ℕ) → harmonic B ≤ 2 * C := by
  have hC0 : 0 ≤ C := by
    apply le_trans (harmonic_nonneg ∅)
    exact hC ∅ (by simp [Positive]) (by simp [Primitive])
      (by simp [PropertyP]) (by simp)
  have aux : ∀ N : ℕ, ∀ B : Finset ℕ, Positive (B : Set ℕ) →
      Primitive (B : Set ℕ) → PropertyP (B : Set ℕ) →
      (∀ n ∈ B, n ≤ N) → harmonic B ≤ 2 * C := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro B hpos hprim hP hN
      by_cases hN0 : N = 0
      · have hB : B = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro n hn
          have := hpos hn
          have := hN n hn
          omega
        rw [hB]
        change 0 ≤ 2 * C
        exact mul_nonneg (by norm_num) hC0
      have hhalf : harmonic (evenHalves B) ≤ 2 * C := by
        apply ih (N / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hN0) (by decide))
          (evenHalves B) (evenHalves_positive hpos)
          (evenHalves_primitive hprim) (evenHalves_propertyP hP)
        intro n hn
        have := hN (2 * n) (mem_evenHalves.mp hn)
        omega
      have hodd : harmonic (B.filter Odd) ≤ C := by
        apply hC
        · intro n hn
          exact hpos (Finset.mem_filter.mp hn).1
        · exact hprim.mono (Finset.filter_subset Odd B)
        · exact hP.mono (Finset.filter_subset Odd B)
        · intro n hn
          exact (Finset.mem_filter.mp hn).2
      rw [harmonic_parity_split]
      linarith
  intro B hpos hprim hP
  apply aux (B.sup id) B hpos hprim hP
  intro n hn
  exact Finset.le_sup (f := id) hn

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/Summability.lean -/
section
/-
# The finite-to-infinite bridge and the exact requested statement

The manuscript proves a stronger uniform statement. The bridge below is fully
proved. Its input, `UniformBoundTarget`, is a named proposition awaiting the
analytic proof. No proof or axiom for that proposition is introduced here.
-/

namespace Erdos12Proof

def SummabilityTarget : Prop :=
  ∀ (A : Set ℕ), IsGood A → Summable (fun (n : A) => (1 / n : ℝ))

def UniformBoundTarget : Prop :=
  ∃ C : ℝ, ∀ (B : Finset ℕ), Positive (B : Set ℕ) →
    PropertyP (B : Set ℕ) → harmonic B ≤ C

theorem harmonic_filter_positive (B : Finset ℕ) :
    harmonic (B.filter (fun n => 0 < n)) = harmonic B := by
  classical
  unfold harmonic
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : 0 < n
  · simp [hn]
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    simp [hn0]

theorem subtype_sum_eq_harmonic {A : Set ℕ} (s : Finset A) :
    (∑ n ∈ s, (1 / n : ℝ)) = harmonic (s.image Subtype.val) := by
  classical
  unfold harmonic
  rw [Finset.sum_image]
  intro a _ b _ hab
  exact Subtype.ext hab

theorem summable_of_finite_bounds {A : Set ℕ} {C : ℝ}
    (hbound : ∀ B : Finset ℕ, (B : Set ℕ) ⊆ A → harmonic B ≤ C) :
    Summable (fun n : A => (1 / n : ℝ)) := by
  classical
  apply summable_of_sum_le (c := C) (fun _ => by positivity)
  intro s
  rw [subtype_sum_eq_harmonic]
  apply hbound
  intro n hn
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hn
  exact a.property

theorem tsum_le_of_finite_bounds {A : Set ℕ} {C : ℝ}
    (hbound : ∀ B : Finset ℕ, (B : Set ℕ) ⊆ A → harmonic B ≤ C) :
    (∑' n : A, (1 / n : ℝ)) ≤ C := by
  classical
  apply Real.tsum_le_of_sum_le (fun _ => by positivity)
  intro s
  rw [subtype_sum_eq_harmonic]
  apply hbound
  intro n hn
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hn
  exact a.property

theorem uniform_bound_implies_strong_statement (h : UniformBoundTarget) :
    ∃ C : ℝ, ∀ A : Set ℕ, PropertyP A →
      Summable (fun n : A => (1 / n : ℝ)) ∧ (∑' n : A, (1 / n : ℝ)) ≤ C := by
  classical
  obtain ⟨C, hC⟩ := h
  refine ⟨C, ?_⟩
  intro A hA
  have hbound : ∀ B : Finset ℕ, (B : Set ℕ) ⊆ A → harmonic B ≤ C := by
    intro B hBA
    rw [← harmonic_filter_positive B]
    apply hC
    · intro n hn
      exact (Finset.mem_filter.mp hn).2
    · apply hA.mono
      intro n hn
      exact hBA (Finset.mem_filter.mp hn).1
  exact ⟨summable_of_finite_bounds hbound, tsum_le_of_finite_bounds hbound⟩

theorem uniform_bound_implies_target (h : UniformBoundTarget) : SummabilityTarget := by
  obtain ⟨_, hC⟩ := uniform_bound_implies_strong_statement h
  intro A hA
  exact (hC A hA.2).1

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/Reduction.lean -/
section
/- # The precise analytic obligation left by the checked reductions -/

namespace Erdos12Proof

def OddPrimitiveBoundTarget : Prop :=
  ∃ C : ℝ, ∀ B : Finset ℕ, Positive (B : Set ℕ) → Primitive (B : Set ℕ) →
    PropertyP (B : Set ℕ) → (∀ n ∈ B, Odd n) → harmonic B ≤ C

theorem odd_primitive_bound_implies_uniform (h : OddPrimitiveBoundTarget) :
    UniformBoundTarget := by
  obtain ⟨C, hC⟩ := h
  refine ⟨3 * C, ?_⟩
  intro B hpos hP
  have hcore : harmonic (minimalCore B) ≤ 2 * C := by
    apply primitive_bound_of_odd_bound hC
    · intro n hn
      exact hpos ((minimalCore_subset B) hn)
    · exact minimalCore_primitive B
    · exact hP.mono (minimalCore_subset B)
  have hbound := harmonic_le_three_halves_core hpos hP
  linarith

theorem uniform_bound_iff_odd_primitive_bound :
    UniformBoundTarget ↔ OddPrimitiveBoundTarget := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, fun B hpos _ hP _ => hC B hpos hP⟩
  · exact odd_primitive_bound_implies_uniform

theorem odd_primitive_bound_implies_target (h : OddPrimitiveBoundTarget) :
    SummabilityTarget :=
  uniform_bound_implies_target (odd_primitive_bound_implies_uniform h)

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/PrefixReduction.lean -/
section
/- # The remaining finite expected-score obligation -/

namespace Erdos12Proof

def PrefixScoreBoundTarget : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ A : Finset ℕ,
    (∀ n ∈ A, 1 < n) → (∀ n ∈ A, n ≤ N) → Primitive (A : Set ℕ) →
    PropertyP (A : Set ℕ) → (∀ n ∈ A, Odd n) → expectedPrefixScore N A ≤ C

theorem prefix_score_bound_implies_odd_primitive_bound (h : PrefixScoreBoundTarget) :
    OddPrimitiveBoundTarget := by
  classical
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨1 + primeHarmonicConstant + C / prefixWeightConstant, ?_⟩
  intro A hpos hprim hP hodd
  by_cases h1 : 1 ∈ A
  · have hA : A = {1} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨h1, ?_⟩
      intro n hn
      exact (hprim h1 hn (one_dvd n)).symm
    rw [hA]
    simp only [harmonic, Finset.sum_singleton, Nat.cast_one, div_one]
    have hquot : 0 ≤ C / prefixWeightConstant := div_nonneg hC0 prefixWeightConstant_pos.le
    linarith [primeHarmonicConstant_pos]
  · have hA : ∀ n ∈ A, 1 < n := by
      intro n hn
      have hn0 := hpos hn
      have hn1 : n ≠ 1 := fun h => h1 (h ▸ hn)
      omega
    let N := max 2 (A.sup id)
    have hN2 : 2 ≤ N := le_max_left _ _
    have hN : ∀ n ∈ A, n ≤ N := by
      intro n hn
      exact (Finset.le_sup (f := id) hn).trans (le_max_right _ _)
    have hscore := hC N hN2 A hA hN hprim hP hodd
    have hbound := harmonic_le_expected_prefix_score A hA hP N hN hN2
    have hquot := div_le_div_of_nonneg_right hscore prefixWeightConstant_pos.le
    linarith

theorem prefix_score_bound_implies_target (h : PrefixScoreBoundTarget) : SummabilityTarget :=
  odd_primitive_bound_implies_target (prefix_score_bound_implies_odd_primitive_bound h)

end Erdos12Proof
end

/- BEGIN SOURCE: Erdos12/SourceStatement.lean -/
section
/-
# Comparison with the public Formal Conjectures statement

The quantifiers below transcribe `Erdos12Proof.IsGood` and `erdos_12.parts.iii`
from Google DeepMind's Formal Conjectures project. The source is
https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/12.lean
and is attributed to the Formal Conjectures Authors under Apache-2.0.
The theorem under development is the positive summability assertion.
-/

namespace Erdos12Proof.Source

abbrev IsGood (A : Set ℕ) : Prop := A.Infinite ∧
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ∣ b + c → a < b → a < c → b = c

def PartIII : Prop :=
  ∀ (A : Set ℕ), IsGood A → Summable (fun (n : A) => (1 / n : ℝ))

theorem isGood_iff (A : Set ℕ) : Source.IsGood A ↔ Erdos12Proof.IsGood A := Iff.rfl

theorem partIII_iff : PartIII ↔ SummabilityTarget := Iff.rfl

theorem partIII_of_odd_primitive_bound (h : OddPrimitiveBoundTarget) : PartIII :=
  partIII_iff.mpr (odd_primitive_bound_implies_target h)

end Erdos12Proof.Source
end

/- BEGIN SOURCE: Erdos12/Main.lean -/
section
/-
# Erdős problem 12(iii)

The finite predictable schedule gives a uniform prefix-score bound.
The checked finite-to-infinite reductions then prove the original statement.
-/

namespace Erdos12Proof

noncomputable def uniformPrefixScoreBound : ℝ :=
  primeTailConstant * (36 + 4 * primeDelayBudgetConstant + 16 * primeLogWeightConstant)

theorem uniformPrefixScoreBound_nonneg : 0 ≤ uniformPrefixScoreBound := by
  unfold uniformPrefixScoreBound
  have hC := primeTailConstant_pos
  have hD := primeDelayBudgetConstant_pos
  have hL := primeLogWeightConstant_pos
  positivity

theorem expectedPrefixScore_uniform (N : ℕ) (A : Finset ℕ)
    (hP : PropertyP (A : Set ℕ)) (hA : ∀ a ∈ A, a ≤ N) :
    expectedPrefixScore N A ≤ uniformPrefixScoreBound := by
  have hfirst := expected_firstCopyScoreSum_bound N A hP hA
  have hsplit := expectedPrefixScore_le_first N A hP
  unfold uniformPrefixScoreBound
  linarith

theorem prefix_score_bound : PrefixScoreBoundTarget := by
  refine ⟨uniformPrefixScoreBound, uniformPrefixScoreBound_nonneg, ?_⟩
  intro N _ A _ hA _ hP _
  exact expectedPrefixScore_uniform N A hP hA

theorem erdos_12_iii : Source.PartIII :=
  Source.partIII_iff.mpr (prefix_score_bound_implies_target prefix_score_bound)

end Erdos12Proof
end

/- BEGIN ADAPTED PRIOR RESULT: PART I -/

section
/-
Copyright 2025 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/










open Classical Filter Set

namespace Erdos12PriorI

/--
A set `A` is "good" if it is infinite and there are no distinct `a,b,c` in `A`
such that `a ∣ (b+c)` and `b > a`, `c > a`.
-/
abbrev IsGood (A : Set ℕ) : Prop := A.Infinite ∧
  ∀ᵉ (a ∈ A) (b ∈ A) (c ∈ A), a ∣ b + c → a < b →
  a < c → b = c

open Erdos12PriorI

open MeasureTheory

open Polynomial

open scoped BigOperators

open scoped Classical

open scoped ENNReal

open scoped EuclideanGeometry

open scoped InnerProductSpace

open scoped intervalIntegral

open scoped List

open scoped Matrix

open scoped Nat

open scoped NNReal

open scoped Pointwise

open scoped ProbabilityTheory

open scoped Real

open scoped symmDiff

open scoped Topology

-- EVOLVE-BLOCK-START
lemma exists_prime_bounded (n : ℕ) : ∃ p, n < p ∧ p ≤ 2 * n + 2 ∧ p.Prime := by
  rcases eq_or_ne n 0 with rfl | hn0
  · exact ⟨2, by decide, by decide, Nat.prime_two⟩
  · rcases Nat.exists_prime_lt_and_le_two_mul n hn0 with ⟨p, hp1, hp2, hp3⟩
    exact ⟨p, hp2, by omega, hp1⟩

noncomputable def q : ℕ → ℕ
| 0 => 5
| m + 1 => Classical.choose (exists_prime_bounded (q m))

lemma q_prime (m : ℕ) : (q m).Prime := by
  cases m with
  | zero => decide
  | succ m =>
    have h := Classical.choose_spec (exists_prime_bounded (q m))
    exact h.2.2

lemma q_gt (m : ℕ) : q m < q (m + 1) := by
  have h := Classical.choose_spec (exists_prime_bounded (q m))
  exact h.1

lemma q_ge_5 (m : ℕ) : 5 ≤ q m := by
  induction m with
  | zero => decide
  | succ m ih =>
    have h_gt := q_gt m
    omega

noncomputable def K : ℕ → ℕ
| 0 => 729
| m + 1 => K m * q m

noncomputable def P (m : ℕ) : ℕ := K m * q m

noncomputable def M (m : ℕ) : ℕ := (P m)^8

def MyGoodSet : Set ℕ :=
  { n | ∃ m, M m ≤ n ∧ n ≤ 2 * M m ∧ n < M m + (P (m + 1)^4 / 2) * P m ∧
        n % K m = 1 ∧ n % q m = 0 }

lemma K_pos (m : ℕ) : 0 < K m := by
  induction m with
  | zero => decide
  | succ m ih =>
    have hq : 0 < q m := by linarith [q_ge_5 m]
    exact Nat.mul_pos ih hq

lemma P_pos (m : ℕ) : 0 < P m := Nat.mul_pos (K_pos m) (by linarith [q_ge_5 m])

lemma M_succ (m : ℕ) : M (m + 1) = M m * (q (m + 1))^8 := by
  calc M (m + 1) = (P (m + 1))^8 := rfl
    _ = (P m * q (m + 1))^8 := rfl
    _ = (P m)^8 * (q (m + 1))^8 := Nat.mul_pow (P m) (q (m + 1)) 8
    _ = M m * (q (m + 1))^8 := rfl

lemma pow_eight_le {a b : ℕ} (h : a ≤ b) : a^8 ≤ b^8 := by
  gcongr

lemma M_increasing (m : ℕ) : 2 * M m < M (m + 1) := by
  have h1 : M (m + 1) = M m * (q (m + 1))^8 := M_succ m
  have h2 : 5 ≤ q (m + 1) := q_ge_5 (m + 1)
  have h3 : 2 < 5^8 := by decide
  have h4 : 5^8 ≤ (q (m + 1))^8 := pow_eight_le h2
  have h5 : 2 < (q (m + 1))^8 := by linarith
  have h_P : 1 ≤ P m := P_pos m
  have h_M_pos : 1 ≤ M m := pow_eight_le h_P
  have h_M_pos2 : 0 < M m := by linarith
  rw [h1]
  nlinarith

lemma M_monotone {m1 m2 : ℕ} (h : m1 ≤ m2) : M m1 ≤ M m2 := by
  induction m2 with
  | zero =>
    have h_m1 : m1 = 0 := by omega
    rw [h_m1]
  | succ m2 ih =>
    have h_cases : m1 ≤ m2 ∨ m1 = m2 + 1 := by omega
    rcases h_cases with h_le | rfl
    · have h_ih := ih h_le
      have h_inc := M_increasing m2
      omega
    · rfl

lemma m_le_of_lt {a b ma mb : ℕ} (ha : M ma ≤ a) (_ : a ≤ 2 * M ma)
  (_ : M mb ≤ b) (hb2 : b ≤ 2 * M mb) (hab : a < b) : ma ≤ mb := by
  by_contra h
  push Not at h
  have h1 : mb + 1 ≤ ma := h
  have h2 : 2 * M mb < M (mb + 1) := M_increasing mb
  have h3 : M (mb + 1) ≤ M ma := M_monotone h1
  omega

lemma q_dvd_K {ma mb : ℕ} (hma : ma < mb) : q ma ∣ K mb := by
  induction mb with
  | zero =>
    omega
  | succ mb ih =>
    have h_cases : ma < mb ∨ ma = mb := by omega
    rcases h_cases with h_lt | rfl
    · have h_dvd := ih h_lt
      exact dvd_mul_of_dvd_left h_dvd (q mb)
    · exact ⟨K ma, mul_comm (K ma) (q ma)⟩

lemma mod_q_of_lt {b mb ma : ℕ} (hb : b % K mb = 1) (hma : ma < mb) : b % q ma = 1 := by
  have h_dvd : q ma ∣ K mb := q_dvd_K hma
  rcases h_dvd with ⟨k, hk⟩
  have h_div := Nat.div_add_mod b (K mb)
  rw [hb] at h_div
  have h1 : b = 1 + q ma * (k * (b / K mb)) := by
    calc b = K mb * (b / K mb) + 1 := h_div.symm
    _ = (q ma * k) * (b / K mb) + 1 := by rw [hk]
    _ = 1 + q ma * (k * (b / K mb)) := by ring
  have h_mod : b % q ma = (1 + q ma * (k * (b / K mb))) % q ma := congrArg (fun x => x % q ma) h1
  have h_mod2 : (1 + q ma * (k * (b / K mb))) % q ma = (1 % q ma + (q ma * (k * (b / K mb))) % q ma) % q ma := Nat.add_mod 1 (q ma * (k * (b / K mb))) (q ma)
  rw [h_mod2] at h_mod
  have h_mod3 : (q ma * (k * (b / K mb))) % q ma = 0 := Nat.mul_mod_right (q ma) (k * (b / K mb))
  rw [h_mod3] at h_mod
  have h_1_lt : 1 < q ma := by
    have h_ge : 5 ≤ q ma := q_ge_5 ma
    omega
  have h_mod4 : 1 % q ma = 1 := Nat.mod_eq_of_lt h_1_lt
  have h_mod5 : (1 + 0) % q ma = 1 % q ma := rfl
  rw [h_mod4, h_mod5, h_mod4] at h_mod
  exact h_mod

lemma q_div_a {a ma : ℕ} (ha : a % q ma = 0) : q ma ∣ a := Nat.dvd_of_mod_eq_zero ha

lemma K_mod_3 (m : ℕ) : K m % 3 = 0 := by
  induction m with
  | zero => decide
  | succ m ih =>
    have h : (K m * q m) % 3 = ((K m % 3) * (q m % 3)) % 3 := Nat.mul_mod (K m) (q m) 3
    rw [ih] at h
    have h2 : 0 * (q m % 3) = 0 := Nat.zero_mul _
    rw [h2] at h
    exact h

lemma mod_3_eq_1 {n m : ℕ} (hn : n % K m = 1) : n % 3 = 1 := by
  have h_dvd : 3 ∣ K m := Nat.dvd_of_mod_eq_zero (K_mod_3 m)
  rcases h_dvd with ⟨k, hk⟩
  have h_div := Nat.div_add_mod n (K m)
  rw [hn] at h_div
  have h_n : n = 3 * (k * (n / K m)) + 1 := by
    calc n = K m * (n / K m) + 1 := h_div.symm
    _ = (3 * k) * (n / K m) + 1 := by rw [hk]
    _ = 3 * (k * (n / K m)) + 1 := by ring
  omega

lemma prime_dvd_K {p m : ℕ} (hp : p.Prime) (h : p ∣ K m) : p < q m := by
  induction m with
  | zero =>
    have h_K0 : K 0 = 729 := rfl
    rw [h_K0] at h
    have hp_le_3 : p ≤ 3 := by
      have hdvd : p ∣ 3^6 := by exact h
      have hdvd2 : p ∣ 3 := hp.dvd_of_dvd_pow hdvd
      exact Nat.le_of_dvd (by decide) hdvd2
    have h_q0 : q 0 = 5 := rfl
    linarith
  | succ m ih =>
    have h_K_succ : K (m + 1) = K m * q m := rfl
    rw [h_K_succ] at h
    have h_or : p ∣ K m ∨ p ∣ q m := hp.dvd_mul.mp h
    rcases h_or with hpK | hpq
    · have h_lt := ih hpK
      have h_q_lt := q_gt m
      linarith
    · have h_q_pos : 0 < q m := by linarith [q_ge_5 m]
      have hp_le : p ≤ q m := Nat.le_of_dvd h_q_pos hpq
      have h_q_lt := q_gt m
      linarith

lemma K_q_coprime (m : ℕ) : Nat.Coprime (K m) (q m) := by
  have h_gcd_dvd_q : Nat.gcd (K m) (q m) ∣ q m := Nat.gcd_dvd_right (K m) (q m)
  have hq_prime := q_prime m
  have h_gcd_cases : Nat.gcd (K m) (q m) = 1 ∨ Nat.gcd (K m) (q m) = q m := (Nat.dvd_prime hq_prime).mp h_gcd_dvd_q
  rcases h_gcd_cases with h1 | hq
  · exact h1
  · have h_gcd_dvd_K : Nat.gcd (K m) (q m) ∣ K m := Nat.gcd_dvd_left (K m) (q m)
    rw [hq] at h_gcd_dvd_K
    have h_lt : q m < q m := prime_dvd_K hq_prime h_gcd_dvd_K
    omega

lemma K_ge_3 (m : ℕ) : 3 ≤ K m := by
  induction m with
  | zero => decide
  | succ m ih =>
    have h_K_succ : K (m + 1) = K m * q m := rfl
    have hq : 1 ≤ q m := by linarith [q_ge_5 m]
    have h1 : K m * 1 ≤ K m * q m := Nat.mul_le_mul_left (K m) hq
    rw [← h_K_succ] at h1
    linarith

lemma P_dvd_M (m : ℕ) : P m ∣ M m := by
  have h1 : M m = (P m)^8 := rfl
  have h2 : (P m)^8 = (P m)^7 * P m := rfl
  rw [h1, h2]
  exact dvd_mul_left (P m) ((P m)^7)

lemma K_dvd_P (m : ℕ) : K m ∣ P m := ⟨q m, rfl⟩

lemma q_dvd_P (m : ℕ) : q m ∣ P m := ⟨K m, mul_comm (K m) (q m)⟩

lemma K_dvd_M (m : ℕ) : K m ∣ M m := dvd_trans (K_dvd_P m) (P_dvd_M m)

lemma q_dvd_M (m : ℕ) : q m ∣ M m := dvd_trans (q_dvd_P m) (P_dvd_M m)

lemma pow_four_le {a b : ℕ} (h : a ≤ b) : a^4 ≤ b^4 := by gcongr

noncomputable def r_val (m : ℕ) : ℕ := (Nat.chineseRemainder (K_q_coprime m) 1 0).val

noncomputable def x_val (m : ℕ) : ℕ := (r_val m) % P m

lemma x_val_lt_P (m : ℕ) : x_val m < P m := Nat.mod_lt _ (P_pos m)

lemma x_val_mod_K (m : ℕ) : (x_val m) % K m = 1 := by
  have h_r : r_val m ≡ 1 [MOD K m] := (Nat.chineseRemainder (K_q_coprime m) 1 0).property.1
  have hrK : r_val m % K m = 1 % K m := h_r
  have h_K_ge : 3 ≤ K m := K_ge_3 m
  have hK_mod : 1 % K m = 1 := Nat.mod_eq_of_lt (by linarith)
  rw [hK_mod] at hrK
  have h_x_mod : (r_val m % P m) % K m = r_val m % K m := Nat.mod_mod_of_dvd (r_val m) (K_dvd_P m)
  rw [hrK] at h_x_mod
  exact h_x_mod

lemma x_val_mod_q (m : ℕ) : (x_val m) % q m = 0 := by
  have h_r : r_val m ≡ 0 [MOD q m] := (Nat.chineseRemainder (K_q_coprime m) 1 0).property.2
  have hrq : r_val m % q m = 0 % q m := h_r
  have hq_mod : 0 % q m = 0 := Nat.zero_mod (q m)
  rw [hq_mod] at hrq
  have h_x_mod : (r_val m % P m) % q m = r_val m % q m := Nat.mod_mod_of_dvd (r_val m) (q_dvd_P m)
  rw [hrq] at h_x_mod
  exact h_x_mod

lemma exists_good_in_block (m : ℕ) : ∃ n, M m ≤ n ∧ n ≤ 2 * M m ∧ n < M m + (P (m + 1)^4 / 2) * P m ∧ n % K m = 1 ∧ n % q m = 0 := by
  have h_coprime := K_q_coprime m
  have h_crt := Nat.chineseRemainder h_coprime 1 0
  let r := h_crt.val
  have hrK_mod : r ≡ 1 [MOD K m] := h_crt.property.1
  have hrq_mod : r ≡ 0 [MOD q m] := h_crt.property.2
  have hrK : r % K m = 1 % K m := hrK_mod
  have hrq : r % q m = 0 % q m := hrq_mod
  have h_K_ge : 3 ≤ K m := K_ge_3 m
  have hK_mod : 1 % K m = 1 := Nat.mod_eq_of_lt (by linarith)
  rw [hK_mod] at hrK
  have hq_mod : 0 % q m = 0 := Nat.zero_mod (q m)
  rw [hq_mod] at hrq
  have h_P_pos := P_pos m
  let x := r % P m
  have hx_lt : x < P m := Nat.mod_lt r h_P_pos
  let n := M m + x
  have hn_eq : n = M m + x := rfl
  use n
  have hn1 : M m ≤ n := by linarith
  have h_P_le_M : P m ≤ M m := by
    have h1 : M m = (P m)^7 * P m := rfl
    have hp1 : 1 ≤ P m := P_pos m
    have h2 : 1^7 ≤ (P m)^7 := by gcongr
    have h3 : 1 * P m ≤ (P m)^7 * P m := Nat.mul_le_mul_right (P m) h2
    linarith
  have hn2 : n ≤ 2 * M m := by
    have h1 : x < P m := hx_lt
    have h2 : P m ≤ M m := h_P_le_M
    linarith
  have hn2b : n < M m + (P (m + 1)^4 / 2) * P m := by
    have h1 : x < P m := hx_lt
    have h2 : 1 ≤ P (m + 1)^4 / 2 := by
      have hk : 3 ≤ K (m + 1) := K_ge_3 (m + 1)
      have hq : 5 ≤ q (m + 1) := q_ge_5 (m + 1)
      have hP : 15 ≤ P (m + 1) := Nat.mul_le_mul hk hq
      have hP4 : 2 ≤ P (m + 1)^4 := by
        calc 2 ≤ 15^4 := by decide
          _ ≤ P (m + 1)^4 := by gcongr
      omega
    have h3 : P m ≤ (P (m + 1)^4 / 2) * P m := Nat.le_mul_of_pos_left (P m) h2
    omega
  have hxK : x % K m = r % K m := Nat.mod_mod_of_dvd r (K_dvd_P m)
  have hn3 : n % K m = 1 := by
    have h1 : n % K m = (M m % K m + x % K m) % K m := Nat.add_mod (M m) x (K m)
    have h2 : M m % K m = 0 := Nat.mod_eq_zero_of_dvd (K_dvd_M m)
    rw [h2, hxK, hrK] at h1
    have h3 : (0 + 1) % K m = 1 % K m := rfl
    rw [h3, hK_mod] at h1
    exact h1
  have hxq : x % q m = r % q m := Nat.mod_mod_of_dvd r (q_dvd_P m)
  have hn4 : n % q m = 0 := by
    have h1 : n % q m = (M m % q m + x % q m) % q m := Nat.add_mod (M m) x (q m)
    have h2 : M m % q m = 0 := Nat.mod_eq_zero_of_dvd (q_dvd_M m)
    rw [h2, hxq, hrq] at h1
    have h3 : (0 + 0) % q m = 0 % q m := rfl
    rw [h3, hq_mod] at h1
    exact h1
  exact ⟨hn1, hn2, hn2b, hn3, hn4⟩

lemma M_gt_m (m : ℕ) : m < M m := by
  induction m with
  | zero =>
    have h1 : M 0 = (P 0)^8 := rfl
    have hp1 : 1 ≤ P 0 := P_pos 0
    have h2 : 1^8 ≤ (P 0)^8 := pow_eight_le hp1
    have h3 : 1 ≤ M 0 := by
      calc 1 = 1^8 := rfl
        _ ≤ (P 0)^8 := h2
        _ = M 0 := h1.symm
    linarith
  | succ m ih =>
    have h_inc : 2 * M m < M (m + 1) := M_increasing m
    linarith

lemma my_good_set_infinite : MyGoodSet.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro N
  have h_ex := exists_good_in_block (N + 1)
  rcases h_ex with ⟨n, hn1, hn2, hn2b, hn3, hn4⟩
  use n
  have h_M_gt : N + 1 < M (N + 1) := M_gt_m (N + 1)
  have hn_gt : N < n := by linarith
  have h_in : n ∈ MyGoodSet := ⟨N + 1, hn1, hn2, hn2b, hn3, hn4⟩
  exact ⟨h_in, hn_gt⟩

lemma my_good_set_is_good : IsGood MyGoodSet := by
  constructor
  · exact my_good_set_infinite
  · rintro a ⟨ma, ha1, ha2, _, ha3, ha4⟩ b ⟨mb, hb1, hb2, _, hb3, hb4⟩ c ⟨mc, hc1, hc2, _, hc3, hc4⟩ hdiv hab hac
    have h_a_pos : 0 < a := by
      by_contra h
      have h_a_zero : a = 0 := by omega
      rw [h_a_zero] at hdiv
      have h_bc_zero : b + c = 0 := eq_zero_of_zero_dvd hdiv
      omega
    have h_ma_le_mb : ma ≤ mb := m_le_of_lt ha1 ha2 hb1 hb2 hab
    have h_ma_le_mc : ma ≤ mc := m_le_of_lt ha1 ha2 hc1 hc2 hac
    rcases lt_trichotomy ma mb with h_ma_lt_mb | rfl | h_mb_lt_ma
    · have hq_div_a : q ma ∣ a := q_div_a ha4
      have hq_div_bc : q ma ∣ b + c := dvd_trans hq_div_a hdiv
      have hb_mod : b % q ma = 1 := mod_q_of_lt hb3 h_ma_lt_mb
      rcases lt_trichotomy ma mc with h_ma_lt_mc | rfl | h_mc_lt_ma
      · have hc_mod : c % q ma = 1 := mod_q_of_lt hc3 h_ma_lt_mc
        have hbc_mod : (b + c) % q ma = 2 := by
          have h1 : (b + c) % q ma = (b % q ma + c % q ma) % q ma := Nat.add_mod b c (q ma)
          rw [hb_mod, hc_mod] at h1
          have h2 : (1 + 1) % q ma = 2 % q ma := rfl
          rw [h2] at h1
          have h3 : 2 % q ma = 2 := Nat.mod_eq_of_lt (by linarith [q_ge_5 ma])
          rw [h3] at h1
          exact h1
        have h4 : (b + c) % q ma = 0 := Nat.mod_eq_zero_of_dvd hq_div_bc
        rw [hbc_mod] at h4
        exact absurd h4 (by decide)
      · have hc_mod : c % q ma = 0 := hc4
        have hbc_mod : (b + c) % q ma = 1 := by
          have h1 : (b + c) % q ma = (b % q ma + c % q ma) % q ma := Nat.add_mod b c (q ma)
          rw [hb_mod, hc_mod] at h1
          have h2 : (1 + 0) % q ma = 1 % q ma := rfl
          rw [h2] at h1
          have h3 : 1 % q ma = 1 := Nat.mod_eq_of_lt (by linarith [q_ge_5 ma])
          rw [h3] at h1
          exact h1
        have h4 : (b + c) % q ma = 0 := Nat.mod_eq_zero_of_dvd hq_div_bc
        rw [hbc_mod] at h4
        exact absurd h4 (by decide)
      · exact absurd h_ma_le_mc (by omega)
    · rcases lt_trichotomy ma mc with h_ma_lt_mc | rfl | h_mc_lt_ma
      · have hb_mod : b % q ma = 0 := hb4
        have hc_mod : c % q ma = 1 := mod_q_of_lt hc3 h_ma_lt_mc
        have hq_div_a : q ma ∣ a := q_div_a ha4
        have hq_div_bc : q ma ∣ b + c := dvd_trans hq_div_a hdiv
        have hbc_mod : (b + c) % q ma = 1 := by
          have h1 : (b + c) % q ma = (b % q ma + c % q ma) % q ma := Nat.add_mod b c (q ma)
          rw [hb_mod, hc_mod] at h1
          have h2 : (0 + 1) % q ma = 1 % q ma := rfl
          rw [h2] at h1
          have h3 : 1 % q ma = 1 := Nat.mod_eq_of_lt (by linarith [q_ge_5 ma])
          rw [h3] at h1
          exact h1
        have h4 : (b + c) % q ma = 0 := Nat.mod_eq_zero_of_dvd hq_div_bc
        rw [hbc_mod] at h4
        exact absurd h4 (by decide)
      · rcases hdiv with ⟨k, hk⟩
        have hb_le : b ≤ 2 * a := by
          have h1 : b ≤ 2 * M ma := hb2
          have h2 : M ma ≤ a := ha1
          omega
        have hc_le : c ≤ 2 * a := by
          have h1 : c ≤ 2 * M ma := hc2
          have h2 : M ma ≤ a := ha1
          omega
        have hk_le : k ≤ 4 := by
          by_contra h
          push Not at h
          have h_ak : a * 5 ≤ a * k := Nat.mul_le_mul_left a h
          rw [← hk] at h_ak
          have h_sum : b + c ≤ 4 * a := by omega
          nlinarith
        have h_bc_gt_2a : 2 * a < b + c := by omega
        have hk_ge : 3 ≤ k := by
          by_contra h
          push Not at h
          have h_le_2 : k ≤ 2 := by omega
          have h_ak : a * k ≤ a * 2 := Nat.mul_le_mul_left a h_le_2
          rw [← hk] at h_ak
          have h_sum : 2 * a < b + c := by omega
          nlinarith
        have ha_mod_3 : a % 3 = 1 := mod_3_eq_1 ha3
        have hb_mod_3 : b % 3 = 1 := mod_3_eq_1 hb3
        have hc_mod_3 : c % 3 = 1 := mod_3_eq_1 hc3
        have hbc_mod_3 : (b + c) % 3 = 2 := by
          have h1 : (b + c) % 3 = (b % 3 + c % 3) % 3 := Nat.add_mod b c 3
          rw [hb_mod_3, hc_mod_3] at h1
          have h2 : (1 + 1) % 3 = 2 := rfl
          rw [h2] at h1
          exact h1
        have hk_mod_3 : (a * k) % 3 = 2 := by
          rw [← hk]
          exact hbc_mod_3
        have hk_cases : k = 3 ∨ k = 4 := by omega
        rcases hk_cases with rfl | rfl
        · have h1 : (a * 3) % 3 = 0 := Nat.mod_eq_zero_of_dvd ⟨a, mul_comm a 3⟩
          rw [h1] at hk_mod_3
          exact absurd hk_mod_3 (by decide)
        · have h1 : (a * 4) % 3 = (a % 3 * (4 % 3)) % 3 := Nat.mul_mod a 4 3
          have h2 : 4 % 3 = 1 := rfl
          rw [h2, ha_mod_3] at h1
          have h3 : (1 * 1) % 3 = 1 := rfl
          rw [h3] at h1
          rw [h1] at hk_mod_3
          exact absurd hk_mod_3 (by decide)
      · exact absurd h_ma_le_mc (by omega)
    · exact absurd h_ma_le_mb (by omega)

noncomputable def f_val (m i : ℕ) : ℕ := M m + x_val m + i * P m

lemma P_le_M (m : ℕ) : P m ≤ M m := by
  have h1 : M m = (P m)^7 * P m := rfl
  have hp1 : 1 ≤ P m := P_pos m
  have h2 : 1^7 ≤ (P m)^7 := by gcongr
  have h3 : 1 * P m ≤ (P m)^7 * P m := Nat.mul_le_mul_right (P m) h2
  linarith



lemma q_bound_le (m : ℕ) : q m + 2 ≤ 7 * 2^m := by
  induction m with
  | zero => decide
  | succ m ih =>
    have h1 : q (m + 1) ≤ 2 * q m + 2 := (Classical.choose_spec (exists_prime_bounded (q m))).2.1
    have h2 : q (m + 1) + 2 ≤ 2 * (q m + 2) := by omega
    have h3 : 2 * (q m + 2) ≤ 2 * (7 * 2^m) := Nat.mul_le_mul_left 2 ih
    have h4 : 2 * (7 * 2^m) = 7 * 2^(m + 1) := by ring
    omega

lemma P_lower_bound (m : ℕ) : 3645 * 5^m ≤ P m := by
  induction m with
  | zero =>
    have h1 : P 0 = 3645 := rfl
    omega
  | succ m ih =>
    have h1 : P (m + 1) = P m * q (m + 1) := rfl
    have hq : 5 ≤ q (m + 1) := q_ge_5 (m + 1)
    have h2 : 3645 * 5^m * 5 ≤ P m * q (m + 1) := Nat.mul_le_mul ih hq
    have h3 : 3645 * 5^m * 5 = 3645 * 5^(m + 1) := by ring
    omega

lemma q_pow_four_bound_helper (m : ℕ) : 38416 * 16^m ≤ 48427561125 * 125^m := by
  induction m with
  | zero => decide
  | succ m ih =>
    have h1 : 38416 * 16^(m + 1) = (38416 * 16^m) * 16 := by ring
    have h2 : 48427561125 * 125^(m + 1) = (48427561125 * 125^m) * 125 := by ring
    rw [h1, h2]
    have h3 : (38416 * 16^m) * 16 ≤ (48427561125 * 125^m) * 16 := Nat.mul_le_mul_right 16 ih
    have h4 : (48427561125 * 125^m) * 16 ≤ (48427561125 * 125^m) * 125 := Nat.mul_le_mul_left _ (by decide)
    exact le_trans h3 h4

lemma q_pow_four_bound (m : ℕ) : q (m + 1) ^ 4 ≤ P m ^ 3 := by
  have hq1 : q (m + 1) + 2 ≤ 7 * 2^(m + 1) := q_bound_le (m + 1)
  have hq2 : q (m + 1) ≤ 7 * 2^(m + 1) := by omega
  have hP1 : 3645 * 5^m ≤ P m := P_lower_bound m
  have hq3 : (q (m + 1))^4 ≤ (7 * 2^(m + 1))^4 := by gcongr
  have hP2 : (3645 * 5^m)^3 ≤ P m ^ 3 := by gcongr
  have h_bound : (7 * 2^(m + 1))^4 ≤ (3645 * 5^m)^3 := by
    have h1 : (7 * 2^(m + 1))^4 = 38416 * 16^m := by
      have h_pow : (7 * (2^m * 2))^4 = 7^4 * (2^m)^4 * 2^4 := by ring
      have h2 : 2^(m + 1) = 2^m * 2 := by ring
      rw [h2]
      rw [h_pow]
      have h3 : (2^m)^4 = 16^m := by
        calc (2^m)^4 = 2^(m * 4) := (Nat.pow_mul 2 m 4).symm
          _ = 2^(4 * m) := by rw [Nat.mul_comm]
          _ = (2^4)^m := Nat.pow_mul 2 4 m
          _ = 16^m := rfl
      rw [h3]
      ring
    have h2 : (3645 * 5^m)^3 = 48427561125 * 125^m := by
      have h3 : (5^m)^3 = 125^m := by
        calc (5^m)^3 = 5^(m * 3) := (Nat.pow_mul 5 m 3).symm
          _ = 5^(3 * m) := by rw [Nat.mul_comm]
          _ = (5^3)^m := Nat.pow_mul 5 3 m
          _ = 125^m := rfl
      have h4 : (3645 * 5^m)^3 = 3645^3 * (5^m)^3 := Nat.mul_pow 3645 (5^m) 3
      rw [h4, h3]
      have h5 : 3645^3 = 48427561125 := by decide
      rw [h5]
    rw [h1, h2]
    exact q_pow_four_bound_helper m
  omega

lemma f_val_bound (m i : ℕ) (hi : i ≤ (P (m + 1))^4 / 2) : i * P m ≤ M m / 2 := by
  have h1 : 2 * i ≤ (P (m + 1))^4 := by omega
  have h_P_succ : P (m + 1)^4 = P m^4 * q (m + 1)^4 := by
    have h : P (m + 1) = P m * q (m + 1) := rfl
    rw [h, Nat.mul_pow]
  have h_q : q (m + 1)^4 ≤ P m^3 := q_pow_four_bound m
  have h2 : 2 * i ≤ P m^4 * P m^3 := by
    calc 2 * i ≤ P (m + 1)^4 := h1
      _ = P m^4 * q (m + 1)^4 := h_P_succ
      _ ≤ P m^4 * P m^3 := Nat.mul_le_mul_left _ h_q
  have h3 : P m^4 * P m^3 = P m^7 := by ring
  have h4 : 2 * i * P m ≤ P m^7 * P m := Nat.mul_le_mul_right (P m) (by linarith)
  have h5 : 2 * i * P m = 2 * (i * P m) := by ring
  have h6 : P m^7 * P m = M m := rfl
  rw [h5, h6] at h4
  omega

lemma P_le_M_half (m : ℕ) : P m ≤ M m / 2 := by
  have h1 : M m = (P m)^7 * P m := rfl
  have hp_pos : 0 < P m := P_pos m
  have hp : 15 ≤ P m := by
    have hk : 3 ≤ K m := K_ge_3 m
    have hq : 5 ≤ q m := q_ge_5 m
    have h_mul : 3 * 5 ≤ K m * q m := Nat.mul_le_mul hk hq
    have h_P : P m = K m * q m := rfl
    omega
  have h2 : 2 ≤ (P m)^7 := by
    have h_le : 2 ≤ P m := by omega
    calc 2 ≤ P m := h_le
      _ ≤ P m * (P m)^6 := Nat.le_mul_of_pos_right _ (by positivity)
      _ = (P m)^7 := by ring
  have h3 : 2 * P m ≤ (P m)^7 * P m := Nat.mul_le_mul_right (P m) h2
  rw [← h1] at h3
  omega

lemma f_val_in_good_set (m i : ℕ) (hi : i < (P (m + 1))^4 / 2) : f_val m i ∈ MyGoodSet ∩ Set.Icc (M m) (2 * M m) := by
  constructor
  · use m
    have h_M_ge : M m ≤ f_val m i := by
      dsimp [f_val]
      omega
    have h_P_le_M_half : P m ≤ M m / 2 := P_le_M_half m
    have hi_le : i ≤ (P (m + 1))^4 / 2 := by omega
    have h_i_bound : i * P m ≤ M m / 2 := f_val_bound m i hi_le
    have h_x_lt : x_val m < P m := x_val_lt_P m
    have h_M_le2 : f_val m i ≤ 2 * M m := by
      dsimp [f_val]
      omega
    have h_M_le3 : f_val m i < M m + (P (m + 1)^4 / 2) * P m := by
      dsimp [f_val]
      have h1 : i + 1 ≤ P (m + 1)^4 / 2 := hi
      have h2 : (i + 1) * P m ≤ (P (m + 1)^4 / 2) * P m := Nat.mul_le_mul_right (P m) h1
      have h3 : i * P m + P m = (i + 1) * P m := by ring
      omega
    have hxK : x_val m % K m = 1 := x_val_mod_K m
    have h_n_mod_K : f_val m i % K m = 1 := by
      dsimp [f_val]
      have h_rw : M m + x_val m + i * P m = M m + (x_val m + i * P m) := by ring
      rw [h_rw]
      have h1 : (M m + (x_val m + i * P m)) % K m = (M m % K m + (x_val m + i * P m) % K m) % K m := Nat.add_mod _ _ _
      have hd1 : M m % K m = 0 := Nat.mod_eq_zero_of_dvd (K_dvd_M m)
      rw [hd1] at h1
      have h2 : (0 + (x_val m + i * P m) % K m) % K m = (x_val m + i * P m) % K m := by
        have hz : 0 + (x_val m + i * P m) % K m = (x_val m + i * P m) % K m := zero_add _
        rw [hz]
        exact Nat.mod_mod _ _
      rw [h2] at h1
      rw [h1]
      have h3 : (x_val m + i * P m) % K m = (x_val m % K m + (i * P m) % K m) % K m := Nat.add_mod _ _ _
      have hdvd : K m ∣ i * P m := dvd_mul_of_dvd_right (K_dvd_P m) i
      have hd2 : (i * P m) % K m = 0 := Nat.mod_eq_zero_of_dvd hdvd
      rw [hd2, hxK] at h3
      have h4 : (1 + 0) % K m = 1 % K m := rfl
      rw [h4] at h3
      have hk3 : 3 ≤ K m := K_ge_3 m
      have h5 : 1 % K m = 1 := Nat.mod_eq_of_lt (by omega)
      rw [h5] at h3
      exact h3
    have hxq : x_val m % q m = 0 := x_val_mod_q m
    have h_n_mod_q : f_val m i % q m = 0 := by
      dsimp [f_val]
      have h_rw : M m + x_val m + i * P m = M m + (x_val m + i * P m) := by ring
      rw [h_rw]
      have h1 : (M m + (x_val m + i * P m)) % q m = (M m % q m + (x_val m + i * P m) % q m) % q m := Nat.add_mod _ _ _
      have hd1 : M m % q m = 0 := Nat.mod_eq_zero_of_dvd (q_dvd_M m)
      rw [hd1] at h1
      have h2 : (0 + (x_val m + i * P m) % q m) % q m = (x_val m + i * P m) % q m := by
        have hz : 0 + (x_val m + i * P m) % q m = (x_val m + i * P m) % q m := zero_add _
        rw [hz]
        exact Nat.mod_mod _ _
      rw [h2] at h1
      rw [h1]
      have h3 : (x_val m + i * P m) % q m = (x_val m % q m + (i * P m) % q m) % q m := Nat.add_mod _ _ _
      have hdvd : q m ∣ i * P m := dvd_mul_of_dvd_right (q_dvd_P m) i
      have hd2 : (i * P m) % q m = 0 := Nat.mod_eq_zero_of_dvd hdvd
      rw [hd2, hxq] at h3
      have h4 : (0 + 0) % q m = 0 % q m := rfl
      rw [h4] at h3
      have h5 : 0 % q m = 0 := Nat.zero_mod _
      rw [h5] at h3
      exact h3
    exact ⟨h_M_ge, h_M_le2, h_M_le3, h_n_mod_K, h_n_mod_q⟩
  · constructor
    · dsimp [f_val]
      omega
    · have hi_le : i ≤ (P (m + 1))^4 / 2 := by omega
      have h_i_bound : i * P m ≤ M m / 2 := f_val_bound m i hi_le
      have h_x_lt : x_val m < P m := x_val_lt_P m
      have h_P_le_M_half : P m ≤ M m / 2 := P_le_M_half m
      dsimp [f_val]
      omega

lemma f_val_inj (m : ℕ) : Set.InjOn (f_val m) (Set.Ico 0 ((P (m + 1))^4 / 2)) := by
  intro i hi j hj h_eq
  dsimp [f_val] at h_eq
  have h1 : i * P m = j * P m := by omega
  have hP : 0 < P m := P_pos m
  exact Nat.eq_of_mul_eq_mul_right hP h1

lemma finset_coe_ncard {α : Type*} (s : Finset α) : (s : Set α).ncard = s.card := by
  simp

lemma good_set_inter_finite (m : ℕ) : (MyGoodSet ∩ Set.Icc (M m) (2 * M m)).Finite := by
  have h_sub : MyGoodSet ∩ Set.Icc (M m) (2 * M m) ⊆ Set.Icc (M m) (2 * M m) := fun x hx => hx.2
  have h_fin : (Set.Icc (M m) (2 * M m)).Finite := Set.finite_Icc (M m) (2 * M m)
  exact Set.Finite.subset h_fin h_sub

lemma count_interval (m : ℕ) : P (m + 1) ^ 4 / 2 ≤ (MyGoodSet ∩ Set.Icc (M m) (2 * M m)).ncard := by
  have h_finset : (Finset.Ico 0 ((P (m + 1))^4 / 2)).card = (P (m + 1))^4 / 2 := by
    exact Nat.card_Ico 0 _
  have h_inj : ∀ i ∈ Finset.Ico 0 ((P (m + 1))^4 / 2), ∀ j ∈ Finset.Ico 0 ((P (m + 1))^4 / 2), f_val m i = f_val m j → i = j := by
    intro i hi j hj h_eq
    have hi_set : i ∈ Set.Ico 0 ((P (m + 1))^4 / 2) := by
      have : i < (P (m + 1))^4 / 2 := (Finset.mem_Ico.mp hi).2
      exact ⟨by omega, this⟩
    have hj_set : j ∈ Set.Ico 0 ((P (m + 1))^4 / 2) := by
      have : j < (P (m + 1))^4 / 2 := (Finset.mem_Ico.mp hj).2
      exact ⟨by omega, this⟩
    exact f_val_inj m hi_set hj_set h_eq
  have hs : ∀ i ∈ Finset.Ico 0 ((P (m + 1))^4 / 2), f_val m i ∈ MyGoodSet ∩ Set.Icc (M m) (2 * M m) := by
    intro i hi
    have hi_lt : i < (P (m + 1))^4 / 2 := (Finset.mem_Ico.mp hi).2
    exact f_val_in_good_set m i hi_lt
  let s_img := (Finset.Ico 0 ((P (m + 1))^4 / 2)).image (f_val m)
  have h_card_img : s_img.card = (P (m + 1))^4 / 2 := by
    rw [Finset.card_image_of_injOn]
    exact h_finset
    exact h_inj
  have h_subset : ↑s_img ⊆ MyGoodSet ∩ Set.Icc (M m) (2 * M m) := by
    intro x hx
    have hx_fin : x ∈ s_img := hx
    have h_ex := Finset.mem_image.mp hx_fin
    rcases h_ex with ⟨i, hi, h_eq⟩
    rw [← h_eq]
    exact hs i hi
  have h_fin : (MyGoodSet ∩ Set.Icc (M m) (2 * M m)).Finite := good_set_inter_finite m
  have h_le : s_img.card ≤ (MyGoodSet ∩ Set.Icc (M m) (2 * M m)).ncard := by
    have h_card_eq : s_img.card = (s_img : Set ℕ).ncard := (finset_coe_ncard s_img).symm
    rw [h_card_eq]
    exact Set.ncard_le_ncard h_subset h_fin
  omega







lemma density_ineq_x {x : ℕ} (hx : 10 ≤ x) : 8 * x ≤ 9 * (x / 2)^2 := by
  have h1 : 2 * (x / 2) + x % 2 = x := Nat.div_add_mod x 2
  have h2 : x % 2 ≤ 1 := by omega
  have h3 : x / 2 ≥ 4 := by omega
  nlinarith

lemma density_ineq_x_sq {x : ℕ} (hx : 20 ≤ x) : 2 * x^2 ≤ 9 * (x / 2)^2 := by
  have h1 : 2 * (x / 2) + x % 2 = x := Nat.div_add_mod x 2
  have h2 : x % 2 ≤ 1 := by omega
  have h3 : x / 2 ≥ 10 := by omega
  nlinarith

lemma density_helper_pow (m : ℕ) : 2151296 * 32^(m + 6) ≤ 3375 * 125^(m + 6) := by
  induction m with
  | zero => decide
  | succ m ih =>
    have h1 : 2151296 * 32^(m + 1 + 6) = (2151296 * 32^(m + 6)) * 32 := by
      have : m + 1 + 6 = m + 6 + 1 := by omega
      rw [this, pow_add, pow_one]
      ring
    have h2 : 3375 * 125^(m + 1 + 6) = (3375 * 125^(m + 6)) * 125 := by
      have : m + 1 + 6 = m + 6 + 1 := by omega
      rw [this, pow_add, pow_one]
      ring
    rw [h1, h2]
    have h3 : (2151296 * 32^(m + 6)) * 32 ≤ (3375 * 125^(m + 6)) * 32 := Nat.mul_le_mul_right 32 ih
    have h4 : (3375 * 125^(m + 6)) * 32 ≤ (3375 * 125^(m + 6)) * 125 := Nat.mul_le_mul_left _ (by decide)
    exact le_trans h3 h4

lemma density_ineq_q_helper (m : ℕ) (hm : 6 ≤ m) : 4 * (7 * 2^(m + 1))^5 ≤ (15 * 5^m)^3 := by
  have h_m : ∃ k, m = k + 6 := ⟨m - 6, by omega⟩
  rcases h_m with ⟨k, rfl⟩
  have h1 : 4 * (7 * 2^(k + 6 + 1))^5 = 2151296 * 32^(k + 6) := by
    have : k + 6 + 1 = (k + 6) + 1 := by omega
    rw [this, pow_add, pow_one]
    have h_pow : (7 * (2^(k + 6) * 2))^5 = 7^5 * (2^(k + 6))^5 * 2^5 := by ring
    rw [h_pow]
    have h_2 : (2^(k + 6))^5 = 32^(k + 6) := by
      calc (2^(k + 6))^5 = 2^((k + 6) * 5) := (Nat.pow_mul 2 (k + 6) 5).symm
        _ = 2^(5 * (k + 6)) := by rw [Nat.mul_comm]
        _ = (2^5)^(k + 6) := Nat.pow_mul 2 5 (k + 6)
        _ = 32^(k + 6) := rfl
    rw [h_2]
    ring
  have h2 : (15 * 5^(k + 6))^3 = 3375 * 125^(k + 6) := by
    have h_pow : (15 * 5^(k + 6))^3 = 15^3 * (5^(k + 6))^3 := by ring
    rw [h_pow]
    have h_5 : (5^(k + 6))^3 = 125^(k + 6) := by
      calc (5^(k + 6))^3 = 5^((k + 6) * 3) := (Nat.pow_mul 5 (k + 6) 3).symm
        _ = 5^(3 * (k + 6)) := by rw [Nat.mul_comm]
        _ = (5^3)^(k + 6) := Nat.pow_mul 5 3 (k + 6)
        _ = 125^(k + 6) := rfl
    rw [h_5]
    ring
  rw [h1, h2]
  exact density_helper_pow k

lemma density_ineq_q (m : ℕ) (hm : 6 ≤ m) : 4 * (q (m + 1))^5 ≤ P m ^ 3 := by
  have hq1 : q (m + 1) + 2 ≤ 7 * 2^(m + 1) := q_bound_le (m + 1)
  have hq2 : q (m + 1) ≤ 7 * 2^(m + 1) := by omega
  have hq3 : (q (m + 1))^5 ≤ (7 * 2^(m + 1))^5 := by gcongr
  have hP1 : 3645 * 5^m ≤ P m := P_lower_bound m
  have hp_lower : 15 * 5^m ≤ P m := by linarith
  have hP2 : (15 * 5^m)^3 ≤ P m ^ 3 := by gcongr
  have h1 : 4 * (7 * 2^(m + 1))^5 ≤ (15 * 5^m)^3 := density_ineq_q_helper m hm
  omega

lemma density_ineq (m : ℕ) : 2 * M (m + 1) ≤ 9 * (P (m + 1) ^ 4 / 2) ^ 2 := by
  have h_M : M (m + 1) = P (m + 1) ^ 8 := rfl
  rw [h_M]
  have h_P_ge : 20 ≤ P (m + 1) ^ 4 := by
    have h1 : 15 ≤ P (m + 1) := by
      have hk : 3 ≤ K (m + 1) := K_ge_3 (m + 1)
      have hq : 5 ≤ q (m + 1) := q_ge_5 (m + 1)
      have h_P : P (m + 1) = K (m + 1) * q (m + 1) := rfl
      nlinarith
    have h2 : 15^4 ≤ P (m + 1) ^ 4 := by gcongr
    linarith
  have h_sq : (P (m + 1) ^ 4)^2 = P (m + 1) ^ 8 := by ring
  have h_ineq := density_ineq_x_sq h_P_ge
  rw [h_sq] at h_ineq
  linarith

lemma exists_M_interval (N : ℕ) (hN : M 7 ≤ N) : ∃ m ≥ 7, M m ≤ N ∧ N < M (m + 1) := by
  let P_prop := fun m => N < M m
  have h_ex : ∃ m, P_prop m := ⟨N + 1, by
    have h := M_gt_m (N + 1)
    dsimp [P_prop]
    omega
  ⟩
  let m0 := Nat.find h_ex
  have hm0 : P_prop m0 := Nat.find_spec h_ex
  have hm0_pos : 0 < m0 := by
    by_contra h
    have hm0_zero : m0 = 0 := by omega
    have h_M0_le_M7 : M 0 ≤ M 7 := M_monotone (by decide)
    have : N < M 0 := by
      have h2 := hm0
      rw [hm0_zero] at h2
      exact h2
    omega
  let m := m0 - 1
  use m
  have h_m0_eq : m0 = m + 1 := by omega
  have h2 : ¬ P_prop m := Nat.find_min h_ex (by omega)
  have h3 : M m ≤ N := by
    have h_not : ¬(N < M m) := h2
    omega
  have h4 : N < M (m + 1) := by
    have : m + 1 = m0 := by omega
    rw [this]
    exact hm0
  have hm_ge_7 : 7 ≤ m := by
    by_contra h
    push Not at h
    have h_le : m + 1 ≤ 7 := h
    have h_M_le : M (m + 1) ≤ M 7 := M_monotone h_le
    omega
  exact ⟨hm_ge_7, h3, h4⟩

lemma density_ratio_bound (N C count : ℕ) (h_N_pos : 0 < N) (h_count : C ≤ count) (h_N_bound : N ≤ 9 * C^2) : (1 / 3 : ℝ) ≤ (count : ℝ) / (N : ℝ).sqrt := by
  have h1 : (N : ℝ) ≤ (9 * C^2 : ℕ) := Nat.cast_le.mpr h_N_bound
  have h2 : (9 * C^2 : ℕ) = (3 * C : ℝ)^2 := by
    push_cast
    ring
  rw [h2] at h1
  have h3 : (N : ℝ).sqrt ≤ ((3 * C : ℝ)^2).sqrt := Real.sqrt_le_sqrt h1
  have h4 : ((3 * C : ℝ)^2).sqrt = 3 * C := Real.sqrt_sq (by positivity)
  rw [h4] at h3
  have h_sqrt_pos : 0 < (N : ℝ).sqrt := Real.sqrt_pos.mpr (by exact_mod_cast h_N_pos)
  have h5 : (1 / 3 : ℝ) * (N : ℝ).sqrt ≤ (C : ℝ) := by
    calc (1 / 3 : ℝ) * (N : ℝ).sqrt ≤ (1 / 3 : ℝ) * (3 * C : ℝ) := mul_le_mul_of_nonneg_left h3 (by norm_num)
      _ = (C : ℝ) := by ring
  have h6 : (C : ℝ) ≤ (count : ℝ) := Nat.cast_le.mpr h_count
  have h7 : (1 / 3 : ℝ) * (N : ℝ).sqrt ≤ (count : ℝ) := le_trans h5 h6
  exact (le_div_iff₀ h_sqrt_pos).mpr h7

lemma density_bound_N (N : ℕ) (hN : M 7 ≤ N) : (1 / 3 : ℝ) ≤ (MyGoodSet ∩ Set.Icc 1 N).ncard / (N : ℝ).sqrt := by
  have h_ex := exists_M_interval N hN
  rcases h_ex with ⟨m, hm_ge_7, hM_le, hN_lt⟩
  have h_fin : (MyGoodSet ∩ Set.Icc 1 N).Finite := by
    have h_sub2 : MyGoodSet ∩ Set.Icc 1 N ⊆ Set.Icc 1 N := fun x hx => hx.2
    exact Set.Finite.subset (Set.finite_Icc 1 N) h_sub2
  have h_N_pos : 0 < N := by
    have h_M_pos : 0 < M 7 := by
      have h_M_ge := M_gt_m 7
      omega
    omega
  by_cases h_N_le : N < 2 * M m
  · let m1 := m - 1
    have hm1_eq : m1 + 1 = m := by omega
    have h_M_inc : 2 * M m1 < M m := by
      have h_inc := M_increasing m1
      rw [hm1_eq] at h_inc
      exact h_inc
    have h_sub : MyGoodSet ∩ Set.Icc (M m1) (2 * M m1) ⊆ MyGoodSet ∩ Set.Icc 1 N := by
      intro x hx
      constructor
      · exact hx.1
      · have h_M_pos : 1 ≤ M m1 := by
          have h_M_ge := M_gt_m m1
          omega
        have hx2 : x ∈ Set.Icc (M m1) (2 * M m1) := hx.2
        have h1 : 1 ≤ x := by
          have : M m1 ≤ x := hx2.1
          omega
        have h2 : x ≤ N := by
          have : x ≤ 2 * M m1 := hx2.2
          omega
        exact ⟨h1, h2⟩
    have h_ncard_le : (MyGoodSet ∩ Set.Icc (M m1) (2 * M m1)).ncard ≤ (MyGoodSet ∩ Set.Icc 1 N).ncard :=
      Set.ncard_le_ncard h_sub h_fin
    have h_count := count_interval m1
    have h_P_le_N : P (m1 + 1) ^ 4 / 2 ≤ (MyGoodSet ∩ Set.Icc 1 N).ncard := by omega
    have h_ineq := density_ineq m1
    have h_N_bound : N ≤ 9 * (P (m1 + 1) ^ 4 / 2) ^ 2 := by
      calc N ≤ 2 * M m := by omega
        _ = 2 * M (m1 + 1) := by
          have : m1 + 1 = m := by omega
          rw [this]
        _ ≤ 9 * (P (m1 + 1) ^ 4 / 2) ^ 2 := h_ineq
    exact density_ratio_bound N (P (m1 + 1) ^ 4 / 2) (MyGoodSet ∩ Set.Icc 1 N).ncard h_N_pos h_P_le_N h_N_bound
  · have h_sub : MyGoodSet ∩ Set.Icc (M m) (2 * M m) ⊆ MyGoodSet ∩ Set.Icc 1 N := by
      intro x hx
      constructor
      · exact hx.1
      · have h_M_pos : 1 ≤ M m := by
          have h_M_ge := M_gt_m m
          omega
        have hx2 : x ∈ Set.Icc (M m) (2 * M m) := hx.2
        have h1 : 1 ≤ x := by
          have : M m ≤ x := hx2.1
          omega
        have h2 : x ≤ N := by
          have : x ≤ 2 * M m := hx2.2
          omega
        exact ⟨h1, h2⟩
    have h_ncard_le : (MyGoodSet ∩ Set.Icc (M m) (2 * M m)).ncard ≤ (MyGoodSet ∩ Set.Icc 1 N).ncard :=
      Set.ncard_le_ncard h_sub h_fin
    have h_count := count_interval m
    have h_P_le_N : P (m + 1) ^ 4 / 2 ≤ (MyGoodSet ∩ Set.Icc 1 N).ncard := by omega
    have h_ineq := density_ineq m
    have h_N_bound : N ≤ 9 * (P (m + 1) ^ 4 / 2) ^ 2 := by
      calc N ≤ M (m + 1) := by omega
        _ ≤ 2 * M (m + 1) := by omega
        _ ≤ 9 * (P (m + 1) ^ 4 / 2) ^ 2 := h_ineq
    exact density_ratio_bound N (P (m + 1) ^ 4 / 2) (MyGoodSet ∩ Set.Icc 1 N).ncard h_N_pos h_P_le_N h_N_bound

lemma sum_P_pow_four (m : ℕ) : ∑ k ∈ Finset.range m, P (k + 1)^4 ≤ 2 * P m^4 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have h_ge : 2 * P m ^ 4 ≤ P (m + 1) ^ 4 := by
      have h1 : P (m + 1) = P m * q (m + 1) := rfl
      have h2 : 5 ≤ q (m + 1) := q_ge_5 (m + 1)
      have h3 : P m * 5 ≤ P (m + 1) := by
        rw [h1]
        exact Nat.mul_le_mul_left (P m) h2
      have h4 : (P m * 5)^4 ≤ P (m + 1)^4 := by gcongr
      calc 2 * P m^4 ≤ P m^4 * 625 := by omega
        _ = (P m * 5)^4 := by ring
        _ ≤ P (m + 1)^4 := h4
    linarith

lemma dvd_sub_of_mod_eq {a b c x : ℕ} (ha : a % c = x) (hb : b % c = x) (hle : b ≤ a) : c ∣ a - b := by
  have h_sub : a - b = c * (a / c) - c * (b / c) := by
    have h1 : a = c * (a / c) + x := by
      calc a = c * (a / c) + a % c := (Nat.div_add_mod a c).symm
        _ = c * (a / c) + x := by rw [ha]
    have h2 : b = c * (b / c) + x := by
      calc b = c * (b / c) + b % c := (Nat.div_add_mod b c).symm
        _ = c * (b / c) + x := by rw [hb]
    omega
  have h4 : c * (a / c) - c * (b / c) = c * (a / c - b / c) := (Nat.mul_sub_left_distrib c (a / c) (b / c)).symm
  rw [h_sub, h4]
  exact dvd_mul_right c (a / c - b / c)

lemma div_eq_implies_sub_lt {a b P : ℕ} (h_div : a / P = b / P) (_hle : b ≤ a) (hP : 0 < P) : a - b < P := by
  have h1 := Nat.div_add_mod a P
  have h2 := Nat.div_add_mod b P
  have hm1 : a % P < P := Nat.mod_lt a hP
  have hm2 : b % P < P := Nat.mod_lt b hP
  rw [← h1, ← h2, ← h_div]
  omega

lemma good_set_inj {n1 n2 m : ℕ}
  (hn1_ge : M m ≤ n1) (hn1_modK : n1 % K m = 1) (hn1_modq : n1 % q m = 0)
  (hn2_ge : M m ≤ n2) (hn2_modK : n2 % K m = 1) (hn2_modq : n2 % q m = 0)
  (h_div : (n1 - M m) / P m = (n2 - M m) / P m) : n1 = n2 := by
  have h_coprime : Nat.Coprime (K m) (q m) := K_q_coprime m
  have h_P : P m = K m * q m := rfl
  have hP_pos : 0 < P m := P_pos m
  rcases le_total n1 n2 with hle | hle
  · have hK : K m ∣ n2 - n1 := dvd_sub_of_mod_eq hn2_modK hn1_modK hle
    have hq : q m ∣ n2 - n1 := dvd_sub_of_mod_eq hn2_modq hn1_modq hle
    have hP : P m ∣ n2 - n1 := by
      rw [h_P]
      exact h_coprime.mul_dvd_of_dvd_of_dvd hK hq
    have h_sub_le : n1 - M m ≤ n2 - M m := Nat.sub_le_sub_right hle _
    have h_div_symm : (n2 - M m) / P m = (n1 - M m) / P m := h_div.symm
    have h_lt : (n2 - M m) - (n1 - M m) < P m := div_eq_implies_sub_lt h_div_symm h_sub_le hP_pos
    have h_lt2 : n2 - n1 < P m := by omega
    have h_eq : n2 - n1 = 0 := Nat.eq_zero_of_dvd_of_lt hP h_lt2
    omega
  · have hK : K m ∣ n1 - n2 := dvd_sub_of_mod_eq hn1_modK hn2_modK hle
    have hq : q m ∣ n1 - n2 := dvd_sub_of_mod_eq hn1_modq hn2_modq hle
    have hP : P m ∣ n1 - n2 := by
      rw [h_P]
      exact h_coprime.mul_dvd_of_dvd_of_dvd hK hq
    have h_sub_le : n2 - M m ≤ n1 - M m := Nat.sub_le_sub_right hle _
    have h_lt : (n1 - M m) - (n2 - M m) < P m := div_eq_implies_sub_lt h_div h_sub_le hP_pos
    have h_lt2 : n1 - n2 < P m := by omega
    have h_eq : n1 - n2 = 0 := Nat.eq_zero_of_dvd_of_lt hP h_lt2
    omega

lemma block_unique {n m k : ℕ} (h1 : M m ≤ n) (h2 : n ≤ 2 * M m) (h3 : M k ≤ n) (h4 : n < M (k + 1)) : m = k := by
  rcases lt_trichotomy m k with h_lt | rfl | h_gt
  · have h_M_mono : M (m + 1) ≤ M k := M_monotone h_lt
    have h_inc : 2 * M m < M (m + 1) := M_increasing m
    omega
  · rfl
  · have h_M_mono : M (k + 1) ≤ M m := M_monotone h_gt
    omega

noncomputable def g_block (n : ℕ) : ℕ :=
  if h : ∃ k, M k ≤ n ∧ n < M (k + 1) then Nat.find h else 0

lemma g_block_spec {n : ℕ} (h : ∃ k, M k ≤ n ∧ n < M (k + 1)) :
  M (g_block n) ≤ n ∧ n < M (g_block n + 1) := by
  dsimp [g_block]
  rw [dite_eq_left h]
  exact Nat.find_spec h

lemma my_good_set_has_block {n : ℕ} (hn : n ∈ MyGoodSet) : ∃ k, M k ≤ n ∧ n < M (k + 1) := by
  rcases hn with ⟨k, hk1, hk2, hk3, hk4, hk5⟩
  use k
  refine ⟨hk1, ?_⟩
  have h1 : 2 * M k < M (k + 1) := M_increasing k
  omega

noncomputable def g_val (n : ℕ) : ℕ × ℕ :=
  (g_block n, (n - M (g_block n)) / P (g_block n))

lemma g_val_inj : Set.InjOn g_val MyGoodSet := by
  intro n1 hn1 n2 hn2 h_eq
  dsimp [g_val] at h_eq
  have h_k_eq : g_block n1 = g_block n2 := by
    have h1 : (g_block n1, (n1 - M (g_block n1)) / P (g_block n1)).1 = (g_block n2, (n2 - M (g_block n2)) / P (g_block n2)).1 := by rw [h_eq]
    exact h1
  have h_i_eq : (n1 - M (g_block n1)) / P (g_block n1) = (n2 - M (g_block n2)) / P (g_block n2) := by
    have h1 : (g_block n1, (n1 - M (g_block n1)) / P (g_block n1)).2 = (g_block n2, (n2 - M (g_block n2)) / P (g_block n2)).2 := by rw [h_eq]
    exact h1
  let k := g_block n1
  have hk1 := g_block_spec (my_good_set_has_block hn1)
  have hk2 := g_block_spec (my_good_set_has_block hn2)
  rw [← h_k_eq] at hk2
  rw [← h_k_eq] at h_i_eq
  rcases hn1 with ⟨m1, hm1_1, hm1_2, hm1_3, hm1_4, hm1_5⟩
  rcases hn2 with ⟨m2, hm2_1, hm2_2, hm2_3, hm2_4, hm2_5⟩
  have hm1_eq : m1 = k := block_unique hm1_1 hm1_2 hk1.1 hk1.2
  have hm2_eq : m2 = k := block_unique hm2_1 hm2_2 hk2.1 hk2.2
  rw [hm1_eq] at hm1_1 hm1_2 hm1_3 hm1_4 hm1_5
  rw [hm2_eq] at hm2_1 hm2_2 hm2_3 hm2_4 hm2_5
  exact good_set_inj hm1_1 hm1_4 hm1_5 hm2_1 hm2_4 hm2_5 h_i_eq

noncomputable def target_set (m : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range m).biUnion (fun k => (Finset.Icc 0 (P (k + 1)^4 / 2)).image (fun i => (k, i)))

lemma target_set_card (m : ℕ) : (target_set m).card ≤ 2 * P m^4 := by
  have h1 : (target_set m).card ≤ ∑ k ∈ Finset.range m, ((Finset.Icc 0 (P (k + 1)^4 / 2)).image (fun i => (k, i))).card := Finset.card_biUnion_le
  have h2 : ∑ k ∈ Finset.range m, ((Finset.Icc 0 (P (k + 1)^4 / 2)).image (fun i => (k, i))).card = ∑ k ∈ Finset.range m, (P (k + 1)^4 / 2 + 1) := by
    apply Finset.sum_congr rfl
    intro k _
    have h_inj : Set.InjOn (fun i => (k, i)) (Finset.Icc 0 (P (k + 1)^4 / 2) : Set ℕ) := by
      intro a _ b _ hab
      exact congr_arg Prod.snd hab
    rw [Finset.card_image_of_injOn h_inj]
    exact Nat.card_Icc 0 _
  have h3 : ∑ k ∈ Finset.range m, (P (k + 1)^4 / 2 + 1) ≤ ∑ k ∈ Finset.range m, P (k + 1)^4 := by
    apply Finset.sum_le_sum
    intro k _
    have hp : 15 ≤ P (k + 1) := by
      have hk : 3 ≤ K (k + 1) := K_ge_3 (k + 1)
      have hq : 5 ≤ q (k + 1) := q_ge_5 (k + 1)
      have h_P : P (k + 1) = K (k + 1) * q (k + 1) := rfl
      nlinarith
    have hp4 : 2 ≤ P (k + 1)^4 := by
      calc 2 ≤ 15^4 := by decide
        _ ≤ P (k + 1)^4 := by gcongr
    omega
  have h4 := sum_P_pow_four m
  omega

lemma g_val_maps_to (m : ℕ) {n : ℕ} (hn : n ∈ MyGoodSet ∩ Set.Icc 1 (M m)) :
  g_val n ∈ target_set m := by
  rcases hn with ⟨hn_good, hn_bounds⟩
  have h_n_le : n ≤ M m := hn_bounds.2
  let k := g_block n
  have hk := g_block_spec (my_good_set_has_block hn_good)
  have h_k_lt : k < m := by
    rcases lt_trichotomy k m with h_lt | h_eq | h_gt
    · exact h_lt
    · have h_eq_n : n = M m := by
        have : M m ≤ n := by rw [← h_eq]; exact hk.1
        omega
      have ⟨m1, hm1_1, hm1_2, hm1_3, hm1_4, hm1_5⟩ := hn_good
      have hk1 : M m ≤ n ∧ n < M (m + 1) := by
        rw [← h_eq_n]
        exact ⟨by omega, by have : 2 * M m < M (m + 1) := M_increasing m; omega⟩
      have hm1_eq : m1 = m := block_unique hm1_1 hm1_2 hk1.1 hk1.2
      rw [hm1_eq] at hm1_4
      rw [h_eq_n] at hm1_4
      have h_M_mod : M m % K m = 0 := Nat.mod_eq_zero_of_dvd (K_dvd_M m)
      rw [h_M_mod] at hm1_4
      exact absurd hm1_4 (by decide)
    · have h_M_mono : M (m + 1) ≤ M k := M_monotone h_gt
      have h_inc : M m < M (m + 1) := by
        have : 2 * M m < M (m + 1) := M_increasing m
        omega
      have : M k ≤ n := hk.1
      omega
  have ⟨m1, hm1_1, hm1_2, hm1_3, hm1_4, hm1_5⟩ := hn_good
  have hm1_eq : m1 = k := block_unique hm1_1 hm1_2 hk.1 hk.2
  rw [hm1_eq] at hm1_3
  have h_i_bound : (n - M k) / P k ≤ P (k + 1)^4 / 2 := by
    have h1 : n - M k ≤ P k * (P (k + 1)^4 / 2) := by
      have : n < M k + (P (k + 1)^4 / 2) * P k := hm1_3
      have : (P (k + 1)^4 / 2) * P k = P k * (P (k + 1)^4 / 2) := Nat.mul_comm _ _
      omega
    exact Nat.div_le_of_le_mul h1
  rw [target_set, Finset.mem_biUnion]
  use k
  refine ⟨Finset.mem_range.mpr h_k_lt, ?_⟩
  rw [Finset.mem_image]
  exact ⟨(n - M k) / P k, Finset.mem_Icc.mpr ⟨Nat.zero_le _, h_i_bound⟩, rfl⟩

lemma count_upper_bound (m : ℕ) : (MyGoodSet ∩ Set.Icc 1 (M m)).ncard ≤ 2 * P m^4 := by
  have h_sub : g_val '' (MyGoodSet ∩ Set.Icc 1 (M m)) ⊆ ↑(target_set m) := by
    intro x hx
    rcases hx with ⟨n, hn, rfl⟩
    exact g_val_maps_to m hn
  have h_fin : (MyGoodSet ∩ Set.Icc 1 (M m)).Finite := by
    apply Set.Finite.subset (Set.finite_Icc 1 (M m))
    intro x hx; exact hx.2
  have h1 : (g_val '' (MyGoodSet ∩ Set.Icc 1 (M m))).ncard ≤ (target_set m : Set (ℕ × ℕ)).ncard :=
    Set.ncard_le_ncard h_sub (Finset.finite_toSet _)
  have h_inj : Set.InjOn g_val (MyGoodSet ∩ Set.Icc 1 (M m)) :=
    Set.InjOn.mono (fun x hx => hx.1) g_val_inj
  rw [h_inj.ncard_image] at h1
  have h2 : (target_set m : Set (ℕ × ℕ)).ncard = (target_set m).card := finset_coe_ncard _
  rw [h2] at h1
  have h3 : (target_set m).card ≤ 2 * P m^4 := target_set_card m
  omega

lemma exists_f_le_two : ∃ᶠ N in Filter.atTop, (MyGoodSet ∩ Set.Icc 1 N).ncard / (N : ℝ).sqrt ≤ 2 := by
  apply Filter.frequently_atTop.mpr
  intro N
  use M N
  constructor
  · exact M_gt_m N |>.le
  · have h_count : (MyGoodSet ∩ Set.Icc 1 (M N)).ncard ≤ 2 * P N ^ 4 := count_upper_bound N
    have h_M : M N = P N ^ 8 := rfl
    have h_sqrt : (M N : ℝ).sqrt = (P N ^ 4 : ℕ) := by
      rw [h_M]
      have h_sq : (P N ^ 4)^2 = P N ^ 8 := by ring
      rw [← h_sq]
      push_cast
      exact Real.sqrt_sq (by positivity)
    have h_pos_N : 0 < P N := P_pos N
    have h_pos : (0 : ℝ) < ((P N ^ 4 : ℕ) : ℝ) := by positivity
    have h_ratio : ((MyGoodSet ∩ Set.Icc 1 (M N)).ncard : ℝ) / (M N : ℝ).sqrt ≤ 2 := by
      calc ((MyGoodSet ∩ Set.Icc 1 (M N)).ncard : ℝ) / (M N : ℝ).sqrt
        _ = ((MyGoodSet ∩ Set.Icc 1 (M N)).ncard : ℝ) / ((P N ^ 4 : ℕ) : ℝ) := by rw [h_sqrt]
        _ ≤ ((2 * P N ^ 4 : ℕ) : ℝ) / ((P N ^ 4 : ℕ) : ℝ) := by
          apply div_le_div_of_nonneg_right
          · exact Nat.cast_le.mpr h_count
          · positivity
        _ = (2 * ((P N ^ 4 : ℕ) : ℝ)) / ((P N ^ 4 : ℕ) : ℝ) := by push_cast; rfl
        _ = 2 := mul_div_cancel_right₀ 2 (ne_of_gt h_pos)
    exact h_ratio

lemma bdd_above_of_frequently_le {f : ℕ → ℝ} {c : ℝ} (h : ∃ᶠ N in Filter.atTop, f N ≤ c) :
  BddAbove {a | ∀ᶠ N in Filter.atTop, a ≤ f N} := by
  use c
  rintro a ha
  have h_and : ∃ᶠ N in Filter.atTop, f N ≤ c ∧ a ≤ f N := h.and_eventually ha
  rcases h_and.exists with ⟨N, hN1, hN2⟩
  exact le_trans hN2 hN1

lemma my_good_set_density : (0 : ℝ) < Filter.atTop.liminf (fun N => (MyGoodSet ∩ Set.Icc 1 N).ncard / (N : ℝ).sqrt) := by
  have h_bound : ∀ᶠ N in Filter.atTop, (1 / 3 : ℝ) ≤ (MyGoodSet ∩ Set.Icc 1 N).ncard / (N : ℝ).sqrt := by
    rw [Filter.eventually_atTop]
    use M 7
    intro N hN
    exact density_bound_N N hN
  have h_bdd : BddAbove {a | ∀ᶠ N in Filter.atTop, a ≤ (MyGoodSet ∩ Set.Icc 1 N).ncard / (N : ℝ).sqrt} :=
    bdd_above_of_frequently_le exists_f_le_two
  have h_liminf : (1 / 3 : ℝ) ≤ Filter.atTop.liminf (fun N => (MyGoodSet ∩ Set.Icc 1 N).ncard / (N : ℝ).sqrt) := by
    exact le_csSup h_bdd h_bound
  linarith
-- EVOLVE-BLOCK-END


theorem target_theorem_0
  : True ↔ ∃ (A : Set ℕ), IsGood A ∧ (0 : ℝ) < Filter.atTop.liminf (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ).sqrt) := by
  -- EVOLVE-BLOCK-START
  constructor
  · intro _
    use MyGoodSet
    exact ⟨my_good_set_is_good, my_good_set_density⟩
  · intro _
    trivial
  -- EVOLVE-BLOCK-END

end Erdos12PriorI

end

/- BEGIN ADAPTED PRIOR RESULT: PART II -/

section
/-
Copyright 2025 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/










open Classical Filter Set

namespace Erdos12PriorII

/--
A set `A` is "good" if it is infinite and there are no distinct `a,b,c` in `A`
such that `a ∣ (b+c)` and `b > a`, `c > a`.
-/
abbrev IsGood (A : Set ℕ) : Prop := A.Infinite ∧
  ∀ᵉ (a ∈ A) (b ∈ A) (c ∈ A), a ∣ b + c → a < b →
  a < c → b = c

open Erdos12PriorII

open MeasureTheory

open Polynomial

open scoped BigOperators

open scoped Classical

open scoped ENNReal

open scoped EuclideanGeometry

open scoped InnerProductSpace

open scoped intervalIntegral

open scoped List

open scoped Matrix

open scoped Nat

open scoped NNReal

open scoped Pointwise

open scoped ProbabilityTheory

open scoped Real

open scoped symmDiff

open scoped Topology

-- EVOLVE-BLOCK-START

lemma not_infinite_iff_eventually {P : ℕ → Prop} :
  ¬ {N : ℕ | P N}.Infinite ↔ ∀ᶠ N in atTop, ¬ P N := by
  rw [Set.not_infinite]
  rw [Filter.eventually_atTop]
  constructor
  · intro h_fin
    have h_bdd : BddAbove {N : ℕ | P N} := Set.Finite.bddAbove h_fin
    rcases h_bdd with ⟨M, hM⟩
    use M + 1
    intro N hN h_in
    have h_le : N ≤ M := hM h_in
    omega
  · rintro ⟨M, hM⟩
    have h_sub : {N : ℕ | P N} ⊆ Set.Iic M := by
      intro N hN
      by_contra h_gt
      have h_not_le : ¬ (N ≤ M) := h_gt
      have h_ge : N ≥ M := by omega
      have h_not_P := hM N h_ge
      exact h_not_P hN
    exact Set.Finite.subset (Set.finite_Iic M) h_sub

lemma sarkozy_case_same (a b d : ℕ) (h_intra : b + d < 3 * a) (hab : a < b) (had : a < d) (hdiv : a ∣ b + d) : False := by
  rcases hdiv with ⟨k, hk⟩
  have hk_eq : b + d = k * a := by
    rw [Nat.mul_comm] at hk
    exact hk
  have h_gt : b + d > 2 * a := by omega
  have h_k_ge_3 : k ≥ 3 := by
    by_contra hc
    have h_lt : k ≤ 2 := by omega
    have h_le_2a : k * a ≤ 2 * a := Nat.mul_le_mul_right a h_lt
    omega
  have h_ka_ge_3a : k * a ≥ 3 * a := Nat.mul_le_mul_right a h_k_ge_3
  omega

lemma sarkozy_case_diff2 (a b d p : ℕ) (hp : p > 2) (ha : a % p = 0) (hb : b % p = 1) (hd : d % p = 1) (hdiv : a ∣ b + d) : False := by
  have h_div : p ∣ a := Nat.dvd_of_mod_eq_zero ha
  have h_div2 : p ∣ b + d := dvd_trans h_div hdiv
  have h_mod : (b + d) % p = 0 := Nat.mod_eq_zero_of_dvd h_div2
  have h_add : (b % p + d % p) % p = (b + d) % p := Eq.symm (Nat.add_mod b d p)
  rw [hb, hd, h_mod] at h_add
  have h2 : 2 % p = 0 := h_add
  have h3 : 2 % p = 2 := Nat.mod_eq_of_lt hp
  omega

lemma sarkozy_case_diff1 (a b d p : ℕ) (hp : p > 2) (ha : a % p = 0) (hb : b % p = 0) (hd : d % p = 1) (hdiv : a ∣ b + d) : False := by
  have h_div : p ∣ a := Nat.dvd_of_mod_eq_zero ha
  have h_div2 : p ∣ b + d := dvd_trans h_div hdiv
  have h_mod : (b + d) % p = 0 := Nat.mod_eq_zero_of_dvd h_div2
  have h_add : (b % p + d % p) % p = (b + d) % p := Eq.symm (Nat.add_mod b d p)
  rw [hb, hd, h_mod] at h_add
  have h1 : 1 % p = 0 := h_add
  have hp1 : p > 1 := by omega
  have h2 : 1 % p = 1 := Nat.mod_eq_of_lt hp1
  omega

def IsGoodSarkozySeq (B : ℕ → Set ℕ) (p : ℕ → ℕ) (c : ℝ) : Prop :=
  (∀ n, ∀ x ∈ B n, x % p n = 0) ∧
  (∀ n, p n > 2) ∧
  (∀ n m, n < m → ∀ y ∈ B m, y % p n = 1) ∧
  (∀ n, ∀ x ∈ B n, ∀ y ∈ B n, ∀ z ∈ B n, x < y → x < z → y + z < 3 * x) ∧
  (∀ n m, n < m → ∀ x ∈ B n, ∀ y ∈ B m, x < y) ∧
  (⋃ n, B n).Infinite ∧
  ∀ᶠ (N : ℕ) in atTop, (N : ℝ) ^ (1 - c) ≤ (((⋃ n, B n) ∩ Icc 1 N).ncard : ℝ)

lemma sarkozy_implies_good {B : ℕ → Set ℕ} {p : ℕ → ℕ} {c : ℝ}
  (h : IsGoodSarkozySeq B p c) : IsGood (⋃ n, B n) := by
  rcases h with ⟨h_mod0, h_pgt2, h_mod1, h_intra, h_lt, h_inf, h_dense⟩
  constructor
  · exact h_inf
  · intro a ha b hb d hd hdiv hab had
    simp only [Set.mem_iUnion] at ha hb hd
    rcases ha with ⟨i, hai⟩
    rcases hb with ⟨j, hbj⟩
    rcases hd with ⟨m, hdm⟩
    have hij : i ≤ j := by
      by_contra hc
      have h_gt : j < i := by omega
      have hba : b < a := h_lt j i h_gt b hbj a hai
      omega
    have him : i ≤ m := by
      by_contra hc
      have h_gt : m < i := by omega
      have hda : d < a := h_lt m i h_gt d hdm a hai
      omega
    have h_cases : (i = j ∧ i = m) ∨ (i < j ∧ i < m) ∨ (i = j ∧ i < m) ∨ (i < j ∧ i = m) := by omega
    rcases h_cases with h1 | h2 | h3 | h4
    · have hbi : b ∈ B i := h1.1 ▸ hbj
      have hdi : d ∈ B i := h1.2 ▸ hdm
      have h_sum := h_intra i a hai b hbi d hdi hab had
      exfalso
      exact sarkozy_case_same a b d h_sum hab had hdiv
    · have hpi : p i > 2 := h_pgt2 i
      have hai0 : a % p i = 0 := h_mod0 i a hai
      have hbi1 : b % p i = 1 := h_mod1 i j h2.1 b hbj
      have hdi1 : d % p i = 1 := h_mod1 i m h2.2 d hdm
      exfalso
      exact sarkozy_case_diff2 a b d (p i) hpi hai0 hbi1 hdi1 hdiv
    · have hpi : p i > 2 := h_pgt2 i
      have hai0 : a % p i = 0 := h_mod0 i a hai
      have hbi0 : b % p i = 0 := by
        have hij_eq : j = i := h3.1.symm
        have hbi : b ∈ B i := hij_eq ▸ hbj
        exact h_mod0 i b hbi
      have hdi1 : d % p i = 1 := h_mod1 i m h3.2 d hdm
      exfalso
      exact sarkozy_case_diff1 a b d (p i) hpi hai0 hbi0 hdi1 hdiv
    · have hpi : p i > 2 := h_pgt2 i
      have hai0 : a % p i = 0 := h_mod0 i a hai
      have hbi1 : b % p i = 1 := h_mod1 i j h4.1 b hbj
      have hdi0 : d % p i = 0 := by
        have him_eq : m = i := h4.2.symm
        have hdi : d ∈ B i := him_eq ▸ hdm
        exact h_mod0 i d hdi
      have hdiv_symm : a ∣ d + b := by
        rw [Nat.add_comm]
        exact hdiv
      exfalso
      exact sarkozy_case_diff1 a d b (p i) hpi hai0 hdi0 hbi1 hdiv_symm

lemma sarkozy_seq_of_aux (B : ℕ → Set ℕ) (p : ℕ → ℕ) (M : ℕ → ℕ) (c : ℝ)
  (h_mod0 : ∀ n, ∀ x ∈ B n, x % p n = 0)
  (h_pgt2 : ∀ n, p n > 2)
  (h_mod1 : ∀ n m, n < m → ∀ y ∈ B m, y % p n = 1)
  (h_lower : ∀ n, ∀ x ∈ B n, x ≥ 10 * M n)
  (h_upper : ∀ n, ∀ x ∈ B n, x ≤ 14 * M n)
  (h_gap : ∀ n m, n < m → 14 * M n < 10 * M m)
  (h_inf : (⋃ n, B n).Infinite)
  (h_dense : ∀ᶠ (N : ℕ) in atTop, (N : ℝ) ^ (1 - c) ≤ (((⋃ n, B n) ∩ Icc 1 N).ncard : ℝ)) :
  IsGoodSarkozySeq B p c := by
  constructor
  · exact h_mod0
  · constructor
    · exact h_pgt2
    · constructor
      · exact h_mod1
      · constructor
        · intro n x hx y hy z hz _ _
          have hx_ge : x ≥ 10 * M n := h_lower n x hx
          have hy_le : y ≤ 14 * M n := h_upper n y hy
          have hz_le : z ≤ 14 * M n := h_upper n z hz
          omega
        · constructor
          · intro n m hnm x hx y hy
            have hx_le : x ≤ 14 * M n := h_upper n x hx
            have hy_ge : y ≥ 10 * M m := h_lower m y hy
            have h_gap_n : 14 * M n < 10 * M m := h_gap n m hnm
            omega
          · constructor
            · exact h_inf
            · exact h_dense

lemma sarkozy_primes : ∃ p : ℕ → ℕ, (∀ n, p n > 2) ∧ (∀ n m, n < m → p n ≠ p m) ∧ (∀ n, Nat.Prime (p n)) ∧ (∀ n, p n ≤ 2^(n+2)) := by
  choose A B using fun and=>Nat.exists_prime_lt_and_le_two_mul (2^ (and + 1)) (by (norm_num))
  exact ⟨A,(B ·|>.2.1.trans_le' (by bound)), fun and R M=>((B _).2.2.trans_lt ((2).pow_succ'▸lt_of_le_of_lt (pow_right_monotone (by decide) (and.succ_lt_succ M)) (B R).2.1)).ne,by simp_all[pow_succ']⟩

lemma mod_eq_of_mod_mul (x C P p_val : ℕ) (hP : P % p_val = 0) (hx : x % P = C % P) :
  x % p_val = C % p_val := by
  have hdvd : p_val ∣ P := Nat.dvd_of_mod_eq_zero hP
  exact Nat.ModEq.of_dvd hdvd hx

lemma sarkozy_CRT_single (p : ℕ → ℕ) (h_prime : ∀ n, Nat.Prime (p n)) (h_dist : ∀ n m, n < m → p n ≠ p m) (n : ℕ) :
  ∃ C : ℕ, C % p n = 0 ∧ ∀ m, m < n → C % p m = 1 := by
  let P := ∏ m ∈ Finset.range n, p m
  have h_coprime : Nat.Coprime (p n) P := by
    apply Nat.Coprime.prod_right
    intro m hm
    rw [Finset.mem_range] at hm
    have h_p_m := h_prime m
    have h_p_n := h_prime n
    have h_neq : p n ≠ p m := Ne.symm (h_dist m n hm)
    have h_coprime2 := (Nat.coprime_primes h_p_n h_p_m).mpr h_neq
    exact h_coprime2
  have h_CRT := Nat.chineseRemainder h_coprime 0 1
  use h_CRT.1
  constructor
  · have h1 : h_CRT.1 % (p n) = 0 % (p n) := h_CRT.2.1
    have h_0_mod : 0 % p n = 0 := Nat.zero_mod (p n)
    rw [h_0_mod] at h1
    exact h1
  · intro m hm
    have h2 : h_CRT.1 % P = 1 % P := h_CRT.2.2
    have h_mem : m ∈ Finset.range n := by
      rw [Finset.mem_range]
      exact hm
    have hdvd : p m ∣ P := Finset.dvd_prod_of_mem p h_mem
    have hP_mod : P % p m = 0 := Nat.mod_eq_zero_of_dvd hdvd
    have h3 := mod_eq_of_mod_mul (h_CRT.1) 1 P (p m) hP_mod h2
    have hp_gt : p m > 1 := (h_prime m).one_lt
    have h_1_mod : 1 % p m = 1 := Nat.mod_eq_of_lt hp_gt
    rw [h_1_mod] at h3
    exact h3

lemma sarkozy_CRT (p : ℕ → ℕ) (h_prime : ∀ n, Nat.Prime (p n)) (h_dist : ∀ n m, n < m → p n ≠ p m) :
  ∃ C : ℕ → ℕ, ∀ n, C n % p n = 0 ∧ ∀ m, m < n → C n % p m = 1 := by
  have h_ex : ∀ n, ∃ C : ℕ, C % p n = 0 ∧ ∀ m, m < n → C % p m = 1 := fun n => sarkozy_CRT_single p h_prime h_dist n
  use fun n => Classical.choose (h_ex n)
  intro n
  exact Classical.choose_spec (h_ex n)

def P_n_def (p : ℕ → ℕ) (n : ℕ) : ℕ := p n * ∏ m ∈ Finset.range n, p m

lemma P_n_mod_pn (p : ℕ → ℕ) (n : ℕ) : (P_n_def p n) % p n = 0 := by
  have hdvd : p n ∣ P_n_def p n := by
    rw [P_n_def]
    exact Nat.dvd_mul_right (p n) (∏ m ∈ Finset.range n, p m)
  exact Nat.mod_eq_zero_of_dvd hdvd

lemma P_n_mod_pm (p : ℕ → ℕ) (n m : ℕ) (hnm : m < n) : (P_n_def p n) % p m = 0 := by
  have hdvd : p m ∣ P_n_def p n := by
    rw [P_n_def]
    have hdvd2 : p m ∣ ∏ k ∈ Finset.range n, p k := by
      apply Finset.dvd_prod_of_mem
      rw [Finset.mem_range]
      exact hnm
    exact dvd_mul_of_dvd_right hdvd2 (p n)
  exact Nat.mod_eq_zero_of_dvd hdvd

lemma P_n_def_pos (p : ℕ → ℕ) (h_pgt2 : ∀ n, p n > 2) (n : ℕ) : P_n_def p n > 0 := by
  have h1 : p n > 0 := by
    have h := h_pgt2 n
    omega
  have h2 : ∏ m ∈ Finset.range n, p m > 0 := by
    apply Finset.prod_pos
    intro m hm
    have h := h_pgt2 m
    omega
  rw [P_n_def]
  exact Nat.mul_pos h1 h2

lemma M_n_growth (M : ℕ → ℕ) (h_gap : ∀ n, 14 * M n < 10 * M (n + 1)) (n : ℕ) : 10 * M n ≥ n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have h1 := h_gap n
    have h2 : 10 * M n ≤ 14 * M n := by omega
    omega

lemma B_n_props (p : ℕ → ℕ) (C : ℕ → ℕ) (M : ℕ → ℕ) (n : ℕ)
  (h_C_pn : C n % p n = 0)
  (h_C_pm : ∀ m, m < n → C n % p m = 1) :
  let B := { x ∈ Icc (10 * M n) (14 * M n) | x % (P_n_def p n) = C n % (P_n_def p n) };
  (∀ x ∈ B, x % p n = 0) ∧
  (∀ m, m < n → ∀ x ∈ B, x % p m = 1) ∧
  (∀ x ∈ B, x ≥ 10 * M n) ∧
  (∀ x ∈ B, x ≤ 14 * M n) := by
  intro B_val
  constructor
  · intro x hx
    have hx_mod_P : x % P_n_def p n = C n % P_n_def p n := hx.2
    have hP_mod_pn : P_n_def p n % p n = 0 := P_n_mod_pn p n
    have hx_mod_pn : x % p n = C n % p n := mod_eq_of_mod_mul x (C n) (P_n_def p n) (p n) hP_mod_pn hx_mod_P
    rw [h_C_pn] at hx_mod_pn
    exact hx_mod_pn
  · constructor
    · intro m hmn x hx
      have hx_mod_P : x % P_n_def p n = C n % P_n_def p n := hx.2
      have hP_mod_pm : P_n_def p n % p m = 0 := P_n_mod_pm p n m hmn
      have hx_mod_pm : x % p m = C n % p m := mod_eq_of_mod_mul x (C n) (P_n_def p n) (p m) hP_mod_pm hx_mod_P
      have hC_val : C n % p m = 1 := h_C_pm m hmn
      rw [hC_val] at hx_mod_pm
      exact hx_mod_pm
    · constructor
      · intro x hx
        exact hx.1.1
      · intro x hx
        exact hx.1.2

def ValidMSeq (c : ℝ) (p : ℕ → ℕ) (M : ℕ → ℕ) : Prop :=
  M 0 ≥ 100 ∧
  (∀ n, 14 * M n < 10 * M (n + 1)) ∧
  (∀ n, 4 * M n ≥ P_n_def p n) ∧
  (∀ n, ((14 * M (n + 1) : ℝ) ^ (1 - c) ≤ (4 * M n / P_n_def p n - 1 : ℝ)))

lemma valid_M_seq_gap (c : ℝ) (p M : ℕ → ℕ) (hM : ValidMSeq c p M) (n m : ℕ) (hnm : n < m) : 14 * M n < 10 * M m := by
  induction m with
  | zero => omega
  | succ m ih =>
    have h_cases : n = m ∨ n < m := by omega
    rcases h_cases with heq | h_lt
    · rw [heq]
      exact hM.2.1 m
    · have h1 := ih h_lt
      have h2 := hM.2.1 m
      omega

lemma prod_p_bound (p : ℕ → ℕ) (hp_bound : ∀ n, p n ≤ 2^(n+2)) (n : ℕ) :
  ∏ m ∈ Finset.range n, p m ≤ 2^((n+1)^2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ]
    have h1 : p n ≤ 2^(n+2) := hp_bound n
    have h2 : (∏ m ∈ Finset.range n, p m) * p n ≤ 2^((n+1)^2) * 2^(n+2) := Nat.mul_le_mul ih h1
    have h3 : 2^((n+1)^2) * 2^(n+2) = 2^((n+1)^2 + n + 2) := by
      rw [← Nat.pow_add]
      have : (n+1)^2 + (n+2) = (n+1)^2 + n + 2 := by ring
      rw [this]
    have h4 : (n+1)^2 + n + 2 ≤ (n+2)^2 := by
      have : (n+1)^2 + n + 2 = n^2 + 3*n + 3 := by ring
      have : (n+2)^2 = n^2 + 4*n + 4 := by ring
      nlinarith
    have h5 : 2^((n+1)^2 + n + 2) ≤ 2^((n+2)^2) := Nat.pow_le_pow_right (by decide) h4
    rw [h3] at h2
    exact le_trans h2 h5

lemma P_n_bound (p : ℕ → ℕ) (hp_bound : ∀ n, p n ≤ 2^(n+2)) (n : ℕ) :
  P_n_def p n ≤ 2^((n+2)^2) := by
  rw [P_n_def]
  have h1 : p n ≤ 2^(n+2) := hp_bound n
  have h2 : ∏ m ∈ Finset.range n, p m ≤ 2^((n+1)^2) := prod_p_bound p hp_bound n
  have h3 : p n * (∏ m ∈ Finset.range n, p m) ≤ 2^(n+2) * 2^((n+1)^2) := Nat.mul_le_mul h1 h2
  have h4 : 2^(n+2) * 2^((n+1)^2) = 2^(n+2 + (n+1)^2) := by rw [← Nat.pow_add]
  have h5 : n+2 + (n+1)^2 ≤ (n+2)^2 := by
    have : n+2 + (n+1)^2 = n^2 + 3*n + 3 := by ring
    have : (n+2)^2 = n^2 + 4*n + 4 := by ring
    nlinarith
  have h6 : 2^(n+2 + (n+1)^2) ≤ 2^((n+2)^2) := Nat.pow_le_pow_right (by decide) h5
  rw [h4] at h3
  exact le_trans h3 h6

lemma exponent_bound (c : ℝ) (A N : ℝ) (hc : c > 0) (hc_lt : c < 1) (hA : A * c ≥ 3) (hN : N ≥ 2 * A) (hA3 : A ≥ 4) :
  (A * (N + 1)^2 + 4) * (1 - c) ≤ A * N^2 - N^2 := by
  have h1 : A * c - 1 ≥ 2 := by linarith
  have h2 : 2 * N^2 ≥ 4 * A * N := by nlinarith
  have h3 : 4 * A * N - 2 * A * N = 2 * A * N := by ring
  have h4 : 2 * A * N ≥ 4 * A^2 := by nlinarith
  have h5 : 4 * A^2 - A - 4 ≥ 56 := by nlinarith
  nlinarith

lemma exists_valid_M_seq (c : ℝ) (hc : c > 0) (hc_lt : c < 1) (p : ℕ → ℕ) (h_pgt2 : ∀ n, p n > 2) (hp_bound : ∀ n, p n ≤ 2^(n+2)) : ∃ M : ℕ → ℕ, ValidMSeq c p M := by
  let A_nat := Nat.ceil (3 / c) + 1
  let M := fun n => 2^(A_nat * (n + 2 * A_nat)^2)
  use M
  have hA_pos : (A_nat : ℝ) ≥ 4 := by
    have h1 : 3 < 3 / c := by
      rw [lt_div_iff₀ hc]
      linarith
    have h2 : (Nat.ceil (3 / c) : ℝ) ≥ 3 / c := Nat.le_ceil (3 / c)
    dsimp [A_nat]
    push_cast
    linarith
  have hAc : (A_nat : ℝ) * c ≥ 3 := by
    have h1 : (Nat.ceil (3 / c) : ℝ) ≥ 3 / c := Nat.le_ceil (3 / c)
    have h2 : (A_nat : ℝ) ≥ 3 / c + 1 := by
      dsimp [A_nat]
      push_cast
      linarith
    have hc_ge : c ≥ 0 := by linarith
    have h3 : (A_nat : ℝ) * c ≥ (3 / c + 1) * c := mul_le_mul_of_nonneg_right h2 hc_ge
    have h4 : (3 / c + 1) * c = 3 + c := by
      have : 3 / c * c = 3 := div_mul_cancel₀ 3 (ne_of_gt hc)
      linarith
    linarith
  constructor
  · have h1 : A_nat ≥ 4 := by exact_mod_cast hA_pos
    have h2 : A_nat * (0 + 2 * A_nat)^2 = 4 * A_nat^3 := by ring
    exact (.trans (by decide) (pow_right_monotone (by decide) (h2.ge.trans' ↑(mul_right_mono ↑(Nat.pow_le_pow_left h1 (3))))))
  · constructor
    · intro n
      have h1 : A_nat * (n + 2 * A_nat)^2 + 4 ≤ A_nat * (n + 1 + 2 * A_nat)^2 := by
        have hA : A_nat ≥ 1 := by exact_mod_cast (le_trans (by norm_num : (1 : ℝ) ≤ 4) hA_pos)
        have h_eq : A_nat * (n + 1 + 2 * A_nat)^2 = A_nat * (n + 2 * A_nat)^2 + A_nat * (2 * n + 4 * A_nat + 1) := by ring
        rw [h_eq]
        have h_term : A_nat * (2 * n + 4 * A_nat + 1) ≥ 4 := by nlinarith
        linarith
      have h2 : M (n + 1) ≥ M n * 16 := by
        dsimp [M]
        have h_pow : 2^(A_nat * (n + 1 + 2 * A_nat)^2) ≥ 2^(A_nat * (n + 2 * A_nat)^2 + 4) := by
          have h02 : 0 < 2 := by decide
          exact Nat.pow_le_pow_right h02 h1
        have h_split : 2^(A_nat * (n + 2 * A_nat)^2 + 4) = 2^(A_nat * (n + 2 * A_nat)^2) * 16 := by
          have : 2^4 = 16 := by norm_num
          rw [Nat.pow_add, this]
        linarith
      have h3 : 14 * M n < 10 * M (n + 1) := by
        have hM_pos : M n ≥ 1 := by
          have h0 : (0 : ℕ) < 2 := by decide
          dsimp [M]
          exact Nat.one_le_pow _ _ h0
        calc 14 * M n < 160 * M n := by linarith
        _ = 10 * (M n * 16) := by ring
        _ ≤ 10 * M (n + 1) := by nlinarith
      exact h3
    · constructor
      · intro n
        have hP := P_n_bound p hp_bound n
        have h1 : (n + 2)^2 ≤ A_nat * (n + 2 * A_nat)^2 := by
          have hA : A_nat ≥ 4 := by exact_mod_cast hA_pos
          have h_bound : n + 2 ≤ n + 2 * A_nat := by linarith
          have h_sq : (n + 2)^2 ≤ (n + 2 * A_nat)^2 := by
            have : n + 2 ≤ n + 2 * A_nat := by linarith
            nlinarith
          calc (n + 2)^2 ≤ (n + 2 * A_nat)^2 := h_sq
          _ ≤ 4 * (n + 2 * A_nat)^2 := by nlinarith
          _ ≤ A_nat * (n + 2 * A_nat)^2 := by nlinarith
        have h2 : 2^((n + 2)^2) ≤ 2^(A_nat * (n + 2 * A_nat)^2) := Nat.pow_le_pow_right (by decide) h1
        have h3 : P_n_def p n ≤ M n := le_trans hP h2
        linarith
      · intro n
        let N_nat := n + 2 * A_nat
        let N : ℝ := N_nat
        have hN : N ≥ 2 * (A_nat : ℝ) := by
          dsimp [N, N_nat]
          push_cast
          linarith
        have h_exp := exponent_bound c A_nat N hc hc_lt hAc hN hA_pos
        have hP_bound := P_n_bound p hp_bound n
        have h_le : (n + 2)^2 ≤ N_nat^2 := by
          dsimp [N_nat]
          have hA : A_nat ≥ 1 := by exact_mod_cast (le_trans (by norm_num : (1 : ℝ) ≤ 4) hA_pos)
          have : n + 2 ≤ n + 2 * A_nat := by linarith
          nlinarith
        have hP_le_N : P_n_def p n ≤ 2^(N_nat^2) := by
          have h_pow : 2^((n + 2)^2) ≤ 2^(N_nat^2) := Nat.pow_le_pow_right (by decide) h_le
          exact le_trans hP_bound h_pow
        have h_M_div : 2^(A_nat * N_nat^2 - N_nat^2) * P_n_def p n ≤ M n := by
          have h_prod : 2^(A_nat * N_nat^2 - N_nat^2) * 2^(N_nat^2) = 2^(A_nat * N_nat^2) := by
            rw [← Nat.pow_add]
            have hA : A_nat ≥ 1 := by exact_mod_cast (le_trans (by norm_num : (1 : ℝ) ≤ 4) hA_pos)
            have : A_nat * N_nat^2 - N_nat^2 + N_nat^2 = A_nat * N_nat^2 := Nat.sub_add_cancel (by nlinarith)
            rw [this]
          have h_mul : 2^(A_nat * N_nat^2 - N_nat^2) * P_n_def p n ≤ 2^(A_nat * N_nat^2 - N_nat^2) * 2^(N_nat^2) := Nat.mul_le_mul_left _ hP_le_N
          exact le_trans h_mul (le_of_eq h_prod)
        have h_RHS_lower : (2^(A_nat * N_nat^2 - N_nat^2) : ℝ) ≤ 4 * (M n : ℝ) / (P_n_def p n : ℝ) - 1 := by
          have h_M_div_real : (2^(A_nat * N_nat^2 - N_nat^2) : ℝ) * (P_n_def p n : ℝ) ≤ (M n : ℝ) := by exact_mod_cast h_M_div
          have hP_pos : (P_n_def p n : ℝ) > 0 := by exact_mod_cast P_n_def_pos p h_pgt2 n
          have h_div_real : (2^(A_nat * N_nat^2 - N_nat^2) : ℝ) ≤ (M n : ℝ) / (P_n_def p n : ℝ) := (le_div_iff₀ hP_pos).mpr h_M_div_real
          have h_val : (2^(A_nat * N_nat^2 - N_nat^2) : ℝ) ≥ 1 := by
            have h0 : (0 : ℕ) < 2 := by decide
            have h_pow_ge : 2^(A_nat * N_nat^2 - N_nat^2) ≥ 1 := Nat.one_le_pow _ _ h0
            exact_mod_cast h_pow_ge
          have h_rw : 4 * (M n : ℝ) / (P_n_def p n : ℝ) = 4 * ((M n : ℝ) / (P_n_def p n : ℝ)) := by ring
          rw [h_rw]
          linarith
        have hLHS2 : (14 * (M (n + 1) : ℝ)) ^ (1 - c) ≤ (2 : ℝ)^(((A_nat : ℝ) * (N + 1)^2 + 4) * (1 - c)) := by
          have h1 : 14 * (M (n + 1) : ℝ) ≤ (2 : ℝ)^((A_nat : ℝ) * (N + 1)^2 + 4) := by
            have h_int : 14 * M (n + 1) ≤ 2^(A_nat * (N_nat + 1)^2 + 4) := by
              have h_split : 2^(A_nat * (N_nat + 1)^2 + 4) = 2^(A_nat * (N_nat + 1)^2) * 16 := by
                have : 16 = 2^4 := rfl
                rw [this, ← Nat.pow_add, Nat.add_comm (A_nat * (N_nat + 1)^2) 4]
              have h_M_def : M (n + 1) = 2^(A_nat * (N_nat + 1)^2) := by
                dsimp [M, N_nat]
                have h_eq : n + 1 + 2 * A_nat = n + 2 * A_nat + 1 := by omega
                rw [h_eq]
              linarith
            have h_cast : (14 * (M (n + 1) : ℝ)) ≤ ((2^(A_nat * (N_nat + 1)^2 + 4) : ℕ) : ℝ) := by
              have h_eq_L : ((14 * M (n + 1) : ℕ) : ℝ) = 14 * (M (n + 1) : ℝ) := by push_cast; rfl
              rw [← h_eq_L]
              exact Nat.cast_le.mpr h_int
            have h_eq : ((2^(A_nat * (N_nat + 1)^2 + 4) : ℕ) : ℝ) = (2 : ℝ)^((A_nat : ℝ) * (N + 1)^2 + 4) := by
              have h_cast_pow : ((2^(A_nat * (N_nat + 1)^2 + 4) : ℕ) : ℝ) = (2 : ℝ)^((A_nat * (N_nat + 1)^2 + 4 : ℕ) : ℝ) := by exact_mod_cast rfl
              rw [h_cast_pow]
              congr 1
              push_cast [N_nat, N]
              ring
            linarith
          have h2 : 0 ≤ 14 * (M (n + 1) : ℝ) := by positivity
          have h3 : 0 ≤ 1 - c := by linarith
          have h_rpow := Real.rpow_le_rpow h2 h1 h3
          have h_mul : ((2 : ℝ)^((A_nat : ℝ) * (N + 1)^2 + 4)) ^ (1 - c) = (2 : ℝ)^(((A_nat : ℝ) * (N + 1)^2 + 4) * (1 - c)) := by
            exact (Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ)) _ _).symm
          rw [h_mul] at h_rpow
          exact h_rpow
        have h_pow_le : (2 : ℝ)^(((A_nat : ℝ) * (N + 1)^2 + 4) * (1 - c)) ≤ (2 : ℝ)^((A_nat : ℝ) * N^2 - N^2) := by
          apply Real.rpow_le_rpow_of_exponent_le (by linarith) h_exp
        have h_final : (14 * (M (n + 1) : ℝ)) ^ (1 - c) ≤ 4 * (M n : ℝ) / (P_n_def p n : ℝ) - 1 := by
          have h_step1 := le_trans hLHS2 h_pow_le
          have h_cast2 : (2 : ℝ)^((A_nat : ℝ) * N^2 - N^2) = (2^(A_nat * N_nat^2 - N_nat^2) : ℝ) := by
            have h_cast3 : (2 : ℝ)^(((A_nat * N_nat^2 - N_nat^2 : ℕ) : ℝ)) = (2^(A_nat * N_nat^2 - N_nat^2) : ℝ) := by exact_mod_cast rfl
            have : (A_nat : ℝ) * N^2 - N^2 = ((A_nat * N_nat^2 - N_nat^2 : ℕ) : ℝ) := by
              have h1 : A_nat * N_nat^2 ≥ N_nat^2 := by
                have : A_nat ≥ 1 := by exact_mod_cast (le_trans (by norm_num : (1 : ℝ) ≤ 4) hA_pos)
                nlinarith
              rw [Nat.cast_sub h1]
              push_cast [N_nat, N]
              ring
            rw [this]
            exact h_cast3
          rw [h_cast2] at h_step1
          exact le_trans h_step1 h_RHS_lower
        exact h_final

lemma B_seq_infinite (M : ℕ → ℕ) (B : ℕ → Set ℕ) (h_gap : ∀ n, 14 * M n < 10 * M (n + 1)) (h_sub : ∀ n, B n ⊆ Icc (10 * M n) (14 * M n)) (h_nonempty : ∀ n, (B n).Nonempty) : (⋃ n, B n).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  let n := a + 1
  have h_ne := h_nonempty n
  rcases h_ne with ⟨x, hx⟩
  use x
  have hx_sub := h_sub n hx
  have hx_ge : x ≥ 10 * M n := hx_sub.1
  have h_Mn_ge : 10 * M n ≥ n := M_n_growth M h_gap n
  have hx_gt_a : x > a := by omega
  constructor
  · rw [Set.mem_iUnion]
    exact ⟨n, hx⟩
  · exact hx_gt_a

lemma B_seq_nonempty (M : ℕ → ℕ) (p : ℕ → ℕ) (C : ℕ → ℕ) (n : ℕ) (hM_len : 4 * M n ≥ P_n_def p n) (h_p_pos : P_n_def p n > 0) :
  ({ x ∈ Icc (10 * M n) (14 * M n) | x % (P_n_def p n) = C n % (P_n_def p n) } : Set ℕ).Nonempty := by
  let P := P_n_def p n
  let C_mod := C n % P
  let start := 10 * M n
  let offset := (C_mod + P - start % P) % P
  let x := start + offset
  have h_offset_lt : offset < P := Nat.mod_lt _ h_p_pos
  have hx_ge : 10 * M n ≤ x := Nat.le_add_right _ _
  have hx_le : x ≤ 14 * M n := by
    have h1 : x < 10 * M n + P := Nat.add_lt_add_left h_offset_lt _
    have h2 : 10 * M n + P ≤ 10 * M n + 4 * M n := Nat.add_le_add_left hM_len _
    have h3 : 10 * M n + 4 * M n = 14 * M n := by ring
    omega
  have hx_mod : x % P = C_mod := by
    have h_off_mod : offset % P = offset := Nat.mod_eq_of_lt h_offset_lt
    calc x % P = (start + offset) % P := rfl
    _ = (start % P + offset % P) % P := Nat.add_mod start offset P
    _ = (start % P + offset) % P := by rw [h_off_mod]
    _ = (start % P + (C_mod + P - start % P) % P) % P := rfl
    _ = ((start % P) % P + (C_mod + P - start % P) % P) % P := by rw [Nat.mod_mod start P]
    _ = (start % P + (C_mod + P - start % P)) % P := Eq.symm (Nat.add_mod (start % P) (C_mod + P - start % P) P)
    _ = (C_mod + P) % P := by
      have h_sub : start % P ≤ C_mod + P := by
        have h_lt : start % P < P := Nat.mod_lt _ h_p_pos
        omega
      have h_add : start % P + (C_mod + P - start % P) = C_mod + P := Nat.add_sub_of_le h_sub
      rw [h_add]
    _ = C_mod % P := Nat.add_mod_right C_mod P
    _ = C_mod := Nat.mod_mod (C n) P
  use x
  exact ⟨⟨hx_ge, hx_le⟩, hx_mod⟩

lemma B_seq_ncard (M : ℕ → ℕ) (p : ℕ → ℕ) (C : ℕ → ℕ) (n : ℕ)
    (_hM_len : 4 * M n ≥ P_n_def p n) (h_p_pos : P_n_def p n > 0) :
    (4 * M n / P_n_def p n - 1 : ℝ) ≤
      (({x ∈ Icc (10 * M n) (14 * M n) |
          x % P_n_def p n = C n % P_n_def p n} : Set ℕ).ncard : ℝ) := by
  let P := P_n_def p n
  let start := 10 * M n
  let offset := (C n % P + P - start % P) % P
  let q := 4 * M n / P
  let f := fun j : ℕ => start + offset + P * j
  have hP : 0 < P := h_p_pos
  have hoff : offset < P := Nat.mod_lt _ hP
  have hmod : (start + offset) % P = C n % P := by
    have hsub : start % P ≤ C n % P + P := by
      have hlt := Nat.mod_lt start hP
      omega
    calc
      (start + offset) % P = (start % P + offset % P) % P := Nat.add_mod _ _ _
      _ = (start % P + (C n % P + P - start % P) % P) % P := by
        dsimp [offset]
        rw [Nat.mod_mod]
      _ = (start % P + (C n % P + P - start % P)) % P := by
        simp only [Nat.add_mod, Nat.mod_mod]
      _ = (C n % P + P) % P := by rw [Nat.add_sub_of_le hsub]
      _ = C n % P := by rw [Nat.add_mod_right, Nat.mod_mod]
  have hinj : Function.Injective f := by
    intro i j hij
    have hmul : P * i = P * j := Nat.add_left_cancel hij
    exact Nat.eq_of_mul_eq_mul_left hP hmul
  have hmem : ∀ j ∈ Finset.range q,
      f j ∈ ({x ∈ Icc (10 * M n) (14 * M n) |
        x % P = C n % P} : Set ℕ) := by
    intro j hj
    have hjq : j + 1 ≤ q := Finset.mem_range.mp hj
    have hbound : P * j + P ≤ 4 * M n := by
      calc
        P * j + P = P * (j + 1) := by ring
        _ ≤ P * q := Nat.mul_le_mul_left P hjq
        _ ≤ 4 * M n := Nat.mul_div_le _ _
    have hxupper : f j ≤ 14 * M n := by dsimp [f, start]; omega
    have hxlower : 10 * M n ≤ f j := by dsimp [f, start]; omega
    refine ⟨⟨hxlower, hxupper⟩, ?_⟩
    dsimp [f]
    simpa only [Nat.add_mod, Nat.mul_mod_right, Nat.add_zero, Nat.mod_mod] using hmod
  let S := (Finset.range q).image f
  have hsub : (S : Set ℕ) ⊆
      {x ∈ Icc (10 * M n) (14 * M n) | x % P = C n % P} := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    exact hmem j hj
  have hfinite : ({x ∈ Icc (10 * M n) (14 * M n) |
      x % P = C n % P} : Set ℕ).Finite :=
    (Set.finite_Icc _ _).subset (fun _ hx => hx.1)
  have hcard := Set.ncard_le_ncard hsub hfinite
  have hScard : (S : Set ℕ).ncard = q := by
    simp only [S, Set.ncard_coe_finset, Finset.card_image_of_injective _ hinj,
      Finset.card_range]
  rw [hScard] at hcard
  have hP_real : (0 : ℝ) < P := by exact_mod_cast hP
  have hlt : (4 * M n : ℝ) < (P : ℝ) * ((q : ℝ) + 1) := by
    exact_mod_cast Nat.lt_mul_div_succ (4 * M n) hP
  have hdiv : (4 * M n : ℝ) / P < (q : ℝ) + 1 :=
    (div_lt_iff₀ hP_real).mpr (by nlinarith)
  have hfloor : (4 * M n : ℝ) / P - 1 ≤ q := by linarith
  exact hfloor.trans (by exact_mod_cast hcard)

lemma exists_M_n_and_B_n (c : ℝ) (hc : c > 0) (hc_lt : c < 1) (p : ℕ → ℕ) (h_pgt2 : ∀ n, p n > 2) (hp_bound : ∀ n, p n ≤ 2^(n+2)) (C : ℕ → ℕ)
  (_h_C_pn : ∀ n, C n % p n = 0)
  (_h_C_pm : ∀ n m, m < n → C n % p m = 1) :
  ∃ (B : ℕ → Set ℕ) (M : ℕ → ℕ),
  (∀ n, B n = { x ∈ Icc (10 * M n) (14 * M n) | x % (P_n_def p n) = C n % (P_n_def p n) }) ∧
  (∀ n m, n < m → 14 * M n < 10 * M m) ∧
  (⋃ n, B n).Infinite ∧
  ∀ᶠ (N : ℕ) in atTop, (N : ℝ) ^ (1 - c) ≤ (((⋃ n, B n) ∩ Icc 1 N).ncard : ℝ) := by
  obtain ⟨M, hM⟩ := exists_valid_M_seq c hc hc_lt p h_pgt2 hp_bound
  let B := fun n => { x ∈ Icc (10 * M n) (14 * M n) | x % (P_n_def p n) = C n % (P_n_def p n) }
  use B, M
  constructor
  · intro n; rfl
  · constructor
    · intro n m hnm
      exact valid_M_seq_gap c p M hM n m hnm
    · constructor
      · have h_gap : ∀ n, 14 * M n < 10 * M (n + 1) := fun n => hM.2.1 n
        have h_sub : ∀ n, B n ⊆ Icc (10 * M n) (14 * M n) := by
          intro n x hx
          exact hx.1
        have h_nonempty : ∀ n, (B n).Nonempty := by
          intro n
          have hM_len : 4 * M n ≥ P_n_def p n := hM.2.2.1 n
          have h_p_pos : P_n_def p n > 0 := P_n_def_pos p h_pgt2 n
          exact B_seq_nonempty M p C n hM_len h_p_pos
        exact B_seq_infinite M B h_gap h_sub h_nonempty
      · have h_dense : ∀ᶠ (N : ℕ) in atTop, (N : ℝ) ^ (1 - c) ≤ (((⋃ n, B n) ∩ Icc 1 N).ncard : ℝ) := by
          rw [Filter.eventually_atTop]
          use 14 * M 0
          intro N hN
          have h_exists_n : ∃ n, 14 * M n ≤ N ∧ N < 14 * M (n + 1) := by rcases↑hM
                                                                         exact (by_contra ((by valid :).elim fun and R L=>Set.infinite_of_injective_forall_mem ( strictMono_nat_of_lt_succ (by bound[and ·])).injective (·.rec hN (not_lt.1 fun and' =>L ⟨·,·, and'⟩)) (Set.finite_le_nat N)))
          rcases h_exists_n with ⟨n, hn_ge, hn_lt⟩
          have h_subset : B n ⊆ (⋃ k, B k) ∩ Icc 1 N := by rcases (↑ hM)
                                                           use fun and(a)=>⟨Set.mem_iUnion_of_mem n a, a.1.1.trans' (Nat.mul_pos (by decide) (n.rec (by bound) (by linarith[‹(∀_, _) ∧_›.1 ·,·]))), a.1.2.trans hn_ge⟩
          have h_card : ((B n).ncard : ℝ) ≤ (((⋃ k, B k) ∩ Icc 1 N).ncard : ℝ) := by exact Nat.cast_le.2<|Set.ncard_le_ncard h_subset
          have h1 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
          have h2 : (N : ℝ) ≤ (14 * M (n + 1) : ℝ) := by
            have hn_lt_cast : (N : ℝ) < ↑(14 * M (n + 1)) := Nat.cast_lt.mpr hn_lt
            have h_eq : ↑(14 * M (n + 1)) = (14 * M (n + 1) : ℝ) := by push_cast; rfl
            rw [h_eq] at hn_lt_cast
            exact le_of_lt hn_lt_cast
          have h3 : 0 ≤ 1 - c := by linarith
          have h_bound : (N : ℝ) ^ (1 - c) ≤ (14 * M (n + 1) : ℝ) ^ (1 - c) := Real.rpow_le_rpow h1 h2 h3
          have h_val : (14 * M (n + 1) : ℝ) ^ (1 - c) ≤ 4 * M n / P_n_def p n - 1 := hM.2.2.2 n
          have hM_len : 4 * M n ≥ P_n_def p n := hM.2.2.1 n
          have h_p_pos : P_n_def p n > 0 := P_n_def_pos p h_pgt2 n
          have h_card_val : (4 * M n / P_n_def p n - 1 : ℝ) ≤ ((B n).ncard : ℝ) := B_seq_ncard M p C n hM_len h_p_pos
          linarith
        exact h_dense

lemma exists_sarkozy_seq_aux (c : ℝ) (hc : c > 0) (hc_lt : c < 1) :
  ∃ (B : ℕ → Set ℕ) (p : ℕ → ℕ) (M : ℕ → ℕ),
  (∀ n, ∀ x ∈ B n, x % p n = 0) ∧
  (∀ n, p n > 2) ∧
  (∀ n m, n < m → ∀ y ∈ B m, y % p n = 1) ∧
  (∀ n, ∀ x ∈ B n, x ≥ 10 * M n) ∧
  (∀ n, ∀ x ∈ B n, x ≤ 14 * M n) ∧
  (∀ n m, n < m → 14 * M n < 10 * M m) ∧
  (⋃ n, B n).Infinite ∧
  ∀ᶠ (N : ℕ) in atTop, (N : ℝ) ^ (1 - c) ≤ (((⋃ n, B n) ∩ Icc 1 N).ncard : ℝ) := by
  have ⟨p, hp_gt2, hp_dist, hp_prime, hp_bound⟩ := sarkozy_primes
  have ⟨C, hC⟩ := sarkozy_CRT p hp_prime hp_dist
  have hC_pn : ∀ n, C n % p n = 0 := fun n => (hC n).1
  have hC_pm : ∀ n m, m < n → C n % p m = 1 := fun n m hnm => (hC n).2 m hnm
  have ⟨B, M, hB_def, hM_gap, hB_inf, hB_dense⟩ := exists_M_n_and_B_n c hc hc_lt p hp_gt2 hp_bound C hC_pn hC_pm
  use B, p, M
  constructor
  · intro n x hx
    have h_props := B_n_props p C M n (hC_pn n) (fun m hnm => hC_pm n m hnm)
    have hx_in : x ∈ { x ∈ Icc (10 * M n) (14 * M n) | x % (P_n_def p n) = C n % (P_n_def p n) } := by
      rw [← hB_def n]
      exact hx
    exact h_props.1 x hx_in
  · constructor
    · exact hp_gt2
    · constructor
      · intro n m hnm y hy
        have h_props := B_n_props p C M m (hC_pn m) (fun k hkm => hC_pm m k hkm)
        have hy_in : y ∈ { x ∈ Icc (10 * M m) (14 * M m) | x % (P_n_def p m) = C m % (P_n_def p m) } := by
          rw [← hB_def m]
          exact hy
        exact h_props.2.1 n hnm y hy_in
      · constructor
        · intro n x hx
          have h_props := B_n_props p C M n (hC_pn n) (fun m hnm => hC_pm n m hnm)
          have hx_in : x ∈ { x ∈ Icc (10 * M n) (14 * M n) | x % (P_n_def p n) = C n % (P_n_def p n) } := by
            rw [← hB_def n]
            exact hx
          exact h_props.2.2.1 x hx_in
        · constructor
          · intro n x hx
            have h_props := B_n_props p C M n (hC_pn n) (fun m hnm => hC_pm n m hnm)
            have hx_in : x ∈ { x ∈ Icc (10 * M n) (14 * M n) | x % (P_n_def p n) = C n % (P_n_def p n) } := by
              rw [← hB_def n]
              exact hx
            exact h_props.2.2.2 x hx_in
          · constructor
            · exact hM_gap
            · constructor
              · exact hB_inf
              · exact hB_dense

lemma exists_sarkozy_seq (c : ℝ) (hc : c > 0) (hc_lt : c < 1) :
  ∃ (B : ℕ → Set ℕ) (p : ℕ → ℕ), IsGoodSarkozySeq B p c := by
  obtain ⟨B, p, M, h1, h2, h3, h4, h5, h6, h7, h8⟩ := exists_sarkozy_seq_aux c hc hc_lt
  use B, p
  exact sarkozy_seq_of_aux B p M c h1 h2 h3 h4 h5 h6 h7 h8

lemma exists_good_set_dense_c_lt_1 (c : ℝ) (hc : c > 0) (hc_lt : c < 1) :
  ∃ A : Set ℕ, IsGood A ∧ ¬ {N : ℕ | ((A ∩ Icc 1 N).ncard : ℝ) < (N : ℝ) ^ (1 - c)}.Infinite := by
  obtain ⟨B, p, hB⟩ := exists_sarkozy_seq c hc hc_lt
  use ⋃ n, B n
  constructor
  · exact sarkozy_implies_good hB
  · have h_equiv := @not_infinite_iff_eventually (fun N => (((⋃ n, B n) ∩ Icc 1 N).ncard : ℝ) < (N : ℝ) ^ (1 - c))
    rw [h_equiv]
    apply hB.2.2.2.2.2.2.mono
    intro N hN
    exact not_lt.mpr hN

-- EVOLVE-BLOCK-END


theorem target_theorem_0
  : False ↔ ∃ c > (0 : ℝ), ∀ (A : Set ℕ), IsGood A → {N : ℕ | (A ∩ Icc 1 N).ncard < (N : ℝ) ^ (1 - c)}.Infinite := by
  -- EVOLVE-BLOCK-START
  have h_ans : False ↔ False := Iff.rfl
  rw [h_ans]
  apply Iff.intro
  · intro h
    exfalso
    exact h
  · intro h
    obtain ⟨c, hc_pos, hc_forall⟩ := h
    let c' := min c (1/2)
    have hc'_pos : c' > 0 := lt_min hc_pos (by linarith)
    have hc'_lt : c' < 1 := by
      have h : c' ≤ 1/2 := min_le_right c (1/2)
      linarith
    have h_exists := exists_good_set_dense_c_lt_1 c' hc'_pos hc'_lt
    obtain ⟨A, hA_good, hA_dense⟩ := h_exists
    have h_inf := hc_forall A hA_good
    have h_inf_diff : ({N : ℕ | ((A ∩ Icc 1 N).ncard : ℝ) < (N : ℝ) ^ (1 - c)} \ {0}).Infinite := Set.Infinite.sdiff h_inf (Set.finite_singleton 0)
    have h_sub : {N : ℕ | ((A ∩ Icc 1 N).ncard : ℝ) < (N : ℝ) ^ (1 - c)} \ {0} ⊆ {N : ℕ | ((A ∩ Icc 1 N).ncard : ℝ) < (N : ℝ) ^ (1 - c')} := by
      rintro N ⟨hN, hN_neq⟩
      have hN_neq' : N ≠ 0 := hN_neq
      have hpos : N > 0 := Nat.pos_of_ne_zero hN_neq'
      have hn_ge : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr hpos
      have hc_le : 1 - c ≤ 1 - c' := by
        have h2 : c' ≤ c := min_le_left c (1/2)
        linarith
      have h1 : (N : ℝ) ^ (1 - c) ≤ (N : ℝ) ^ (1 - c') := Real.rpow_le_rpow_of_exponent_le hn_ge hc_le
      exact lt_of_lt_of_le hN h1
    have h_inf' : {N : ℕ | ((A ∩ Icc 1 N).ncard : ℝ) < (N : ℝ) ^ (1 - c')}.Infinite := Set.Infinite.mono h_sub h_inf_diff
    exact hA_dense h_inf'
  -- EVOLVE-BLOCK-END

end Erdos12PriorII

end

namespace Erdos12AllParts

/-- The original infinite-set hypothesis, with two distinct larger summands. -/
abbrev IsGood (A : Set ℕ) : Prop := Erdos12Proof.IsGood A

/-- Part (i): a positive real lower limit at square-root scale. -/
def PartI : Prop :=
  ∃ A : Set ℕ, IsGood A ∧
    (0 : ℝ) < Filter.atTop.liminf
      (fun N => (A ∩ Set.Icc 1 N).ncard / (N : ℝ).sqrt)

/-- The assertion refuted by part (ii). -/
def UniversalPowerSaving : Prop :=
  ∃ c > (0 : ℝ), ∀ A : Set ℕ, IsGood A →
    {N : ℕ | (A ∩ Set.Icc 1 N).ncard < (N : ℝ) ^ (1 - c)}.Infinite

/-- Part (iii): convergence of the reciprocal sum for every good set. -/
def PartIII : Prop :=
  ∀ A : Set ℕ, IsGood A → Summable (fun n : A => (1 / n : ℝ))

/-- Prior result of AlphaProof Nexus / Google DeepMind, adapted above. -/
theorem part_i : PartI := by
  exact Erdos12PriorI.target_theorem_0.mp True.intro

/-- Prior result of AlphaProof Nexus / Google DeepMind, adapted above. -/
theorem part_ii : ¬ UniversalPowerSaving := by
  intro h
  exact Erdos12PriorII.target_theorem_0.mpr h

/-- The reciprocal-sum theorem from the supplied Howe--Huffman--Kohlmeyer--Kruer proof. -/
theorem part_iii : PartIII := Erdos12Proof.erdos_12_iii

/-- The dense set depends on the exponent; this does not exchange the quantifiers. -/
theorem parameterwise_dense (c : ℝ) (hc : 0 < c) (hc1 : c < 1) :
    ∃ A : Set ℕ, IsGood A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (N : ℝ) ^ (1 - c) ≤ ((A ∩ Set.Icc 1 N).ncard : ℝ) := by
  obtain ⟨B, p, hB⟩ := Erdos12PriorII.exists_sarkozy_seq c hc hc1
  refine ⟨⋃ n, B n, Erdos12PriorII.sarkozy_implies_good hB, ?_⟩
  exact Filter.eventually_atTop.mp hB.2.2.2.2.2.2

/-- The stronger statement in the accompanying manuscript, including finite sets. -/
theorem uniform_reciprocal_bound :
    ∃ C : ℝ, ∀ A : Set ℕ, Erdos12Proof.PropertyP A →
      Summable (fun n : A => (1 / n : ℝ)) ∧ (∑' n : A, (1 / n : ℝ)) ≤ C :=
  Erdos12Proof.uniform_bound_implies_strong_statement
    (Erdos12Proof.odd_primitive_bound_implies_uniform
      (Erdos12Proof.prefix_score_bound_implies_odd_primitive_bound
        Erdos12Proof.prefix_score_bound))

/-- All three numbered questions, with the negative answer to part (ii) explicit. -/
theorem all_parts : PartI ∧ ¬ UniversalPowerSaving ∧ PartIII :=
  ⟨part_i, part_ii, part_iii⟩

end Erdos12AllParts

/-
Apache License 2.0 for the embedded Google DeepMind source:

                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/
