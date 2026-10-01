module
public import Border.Support

@[expose] public section
open scoped BigOperators
open Finset
namespace Border.Implementation
attribute [local instance 100000] Classical.propDecidable
universe u v
variable {ι : Type u} [Fintype ι] {T : ι → Type v} [∀ i, Fintype (T i)]

theorem rectangular_mass (p : ∀ i, T i → ℝ) (P : ∀ i, T i → Prop) :
    (∑ t : ∀ i, T i, if ∀ i, P i (t i) then productPrior p t else 0) =
      ∏ i, ∑ a, if P i a then p i a else 0 := by
  rw [Fintype.prod_sum]
  apply sum_congr rfl
  intro t _
  by_cases ht : ∀ i, P i (t i)
  · simp [ht, productPrior]
  · push Not at ht
    obtain ⟨i, hi⟩ := ht
    rw [ite_eq_right (fun h => hi (h i))]
    exact (prod_eq_zero (mem_univ i) (by simp [hi])).symm

theorem product_prior_isPrior (p : ∀ i, T i → ℝ)
    (hp : ∀ i a, 0 ≤ p i a) (hn : ∀ i, ∑ a, p i a = 1) : IsPrior (productPrior p) := by
  refine ⟨fun t => prod_nonneg (fun i _ => hp i (t i)), ?_⟩
  change (∑ t : ∀ i, T i, ∏ i, p i (t i)) = 1
  rw [← Fintype.prod_sum]
  simp [hn]

theorem product_marginal (p : ∀ i, T i → ℝ) (hn : ∀ i, ∑ a, p i a = 1)
    (i : ι) (a : T i) : marginal (productPrior p) i a = p i a := by
  let P : ∀ j, T j → Prop := fun j b => ∀ h : j = i, h ▸ b = a
  have hP : ∀ t : ∀ i, T i, (∀ j, P j (t j)) ↔ t i = a := by
    intro t
    constructor
    · intro h
      exact h i rfl
    · intro h j hji
      subst j
      exact h
  have hi := rectangular_mass p P
  have hsum : ∀ j, (∑ b, if P j b then p j b else 0) = if j = i then p i a else 1 := by
    intro j
    by_cases hji : j = i
    · subst j
      simp [P]
    · simpa [P, hji] using hn j
  calc
    marginal (productPrior p) i a =
        ∑ t, if ∀ j, P j (t j) then productPrior p t else 0 := by
      unfold marginal
      apply sum_congr rfl
      intro t _
      simp only [hP]
    _ = ∏ j, ∑ b, if P j b then p j b else 0 := hi
    _ = ∏ j, if j = i then p i a else 1 := prod_congr rfl (fun j _ => hsum j)
    _ = p i a := by simp

theorem product_hitMass (p : ∀ i, T i → ℝ) (hn : ∀ i, ∑ a, p i a = 1)
    (S : ∀ i, Finset (T i)) :
    hitMass (productPrior p) S = 1 - ∏ i, (1 - ∑ a ∈ S i, p i a) := by
  have hrect := rectangular_mass p (fun i a => a ∉ S i)
  have hsum : ∀ i, (∑ a, if a ∉ S i then p i a else 0) = 1 - ∑ a ∈ S i, p i a := by
    intro i
    have hs := sum_compl_add_sum (S i) (p i)
    rw [hn i] at hs
    have hc : (∑ a, if a ∉ S i then p i a else 0) = ∑ a ∈ (S i)ᶜ, p i a := by
      have hfilter : univ.filter (fun a : T i => a ∉ S i) = (S i)ᶜ := by
        ext a
        simp
      rw [← sum_filter, hfilter]
    rw [hc]
    linarith
  have hprod : (∏ i, ∑ a, if a ∉ S i then p i a else 0) =
      ∏ i, (1 - ∑ a ∈ S i, p i a) := prod_congr rfl (fun i _ => hsum i)
  have hrect' := hrect.trans hprod
  have htotal : (∑ t, productPrior p t) = 1 := by
    change (∑ t : ∀ i, T i, ∏ i, p i (t i)) = 1
    rw [← Fintype.prod_sum]
    simp [hn]
  have hadd : hitMass (productPrior p) S +
      (∑ t, if ∀ i, t i ∉ S i then productPrior p t else 0) = 1 := by
    rw [hitMass, ← sum_add_distrib, ← htotal]
    apply sum_congr rfl
    intro t _
    by_cases ht : ∃ i, t i ∈ S i
    · have hn' : ¬∀ i, t i ∉ S i := by simpa using ht
      simp [hn']
    · have hn' : ∀ i, t i ∉ S i := by simpa using ht
      simp [hn']
  rw [hrect'] at hadd
  linarith

end Border.Implementation

namespace Border
attribute [local instance 100000] Classical.propDecidable
universe u v
variable {ι : Type u} [Fintype ι] {T : ι → Type v} [∀ i, Fintype (T i)]

/-- The independent-prior corollary; the distributions may differ between bidders. -/
theorem independent_border_feasibility (p q : ∀ i, T i → ℝ)
    (hp : ∀ i a, 0 ≤ p i a) (hn : ∀ i, ∑ a, p i a = 1)
    (hq : ∀ i a, 0 ≤ q i a ∧ q i a ≤ 1) :
    Feasible (productPrior p) q ↔ IndependentBorderCondition p q := by
  rw [border_feasibility (productPrior p) (Implementation.product_prior_isPrior p hp hn) q hq]
  unfold BorderCondition IndependentBorderCondition
  simp only [Implementation.product_marginal p hn, Implementation.product_hitMass p hn]

theorem independent_border_conditional_feasibility (p q : ∀ i, T i → ℝ)
    (hp : ∀ i a, 0 ≤ p i a) (hn : ∀ i, ∑ a, p i a = 1)
    (hq : ∀ i a, 0 ≤ q i a ∧ q i a ≤ 1) :
    ConditionallyFeasible (productPrior p) q ↔ IndependentBorderCondition p q := by
  exact (feasible_iff_conditional (productPrior p) (Implementation.product_prior_isPrior p hp hn) q).symm.trans
    (independent_border_feasibility p q hp hn hq)

end Border
