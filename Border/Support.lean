module
public import Border.Theorem

@[expose] public section
open scoped BigOperators
open Finset
namespace Border.Implementation
universe u v
variable {ι : Type u} [Fintype ι] {T : ι → Type v} [∀ i, Fintype (T i)]

theorem fiber_zero_of_marginal_zero (μ : (∀ i, T i) → ℝ) (hμ : ∀ t, 0 ≤ μ t)
    (i : ι) (a : T i) (ha : marginal μ i a = 0)
    (t : ∀ i, T i) (ht : t i = a) : μ t = 0 := by
  classical
  have hterm : (if t i = a then μ t else 0) ≤ marginal μ i a :=
    by
      unfold marginal
      exact single_le_sum (f := fun s : ∀ i, T i => if s i = a then μ s else 0)
        (fun s _ => by split_ifs <;> first | exact hμ s | exact le_rfl) (mem_univ t)
  exact le_antisymm (by simpa [ht, ha] using hterm) (hμ t)

theorem interimMass_zero_of_marginal_zero (μ : (∀ i, T i) → ℝ) (hμ : ∀ t, 0 ≤ μ t)
    (x : (∀ i, T i) → ι → ℝ) (i : ι) (a : T i) (ha : marginal μ i a = 0) :
    interimMass μ x i a = 0 := by
  classical
  unfold interimMass
  apply sum_eq_zero
  intro t _
  split_ifs with ht
  · rw [fiber_zero_of_marginal_zero μ hμ i a ha t ht, zero_mul]
  · rfl

end Border.Implementation

namespace Border
universe u v
variable {ι : Type u} [Fintype ι] {T : ι → Type v} [∀ i, Fintype (T i)]

/-- Weighted feasibility is exactly conditional feasibility on positive marginal support. -/
theorem feasible_iff_conditional (μ : (∀ i, T i) → ℝ) (hμ : IsPrior μ)
    (q : ∀ i, T i → ℝ) : Feasible μ q ↔ ConditionallyFeasible μ q := by
  constructor
  · rintro ⟨x,hx,h⟩
    refine ⟨x,hx,fun i a ha => ?_⟩
    rw [h i a]
    exact mul_div_cancel_left₀ (q i a) (ne_of_gt ha)
  · rintro ⟨x,hx,h⟩
    refine ⟨x,hx,fun i a => ?_⟩
    by_cases ha : 0 < marginal μ i a
    · exact (div_eq_iff (ne_of_gt ha)).mp (h i a ha) |>.trans (mul_comm _ _)
    · have hz : marginal μ i a = 0 := le_antisymm (le_of_not_gt ha)
        (Implementation.marginal_nonneg μ hμ.1 i a)
      rw [Implementation.interimMass_zero_of_marginal_zero μ hμ.1 x i a hz, hz, zero_mul]

/-- Theorem 7 with the paper's positive-support conditional interpretation. -/
theorem border_conditional_feasibility (μ : (∀ i, T i) → ℝ) (hμ : IsPrior μ)
    (q : ∀ i, T i → ℝ) (hq : ∀ i a, 0 ≤ q i a ∧ q i a ≤ 1) :
    ConditionallyFeasible μ q ↔ BorderCondition μ q :=
  (feasible_iff_conditional μ hμ q).symm.trans (border_feasibility μ hμ q hq)

omit [∀ i, Fintype (T i)] in
/-- Each bidder's ex post winning probability lies in the unit interval. -/
theorem allocation_le_one (x : (∀ i, T i) → ι → ℝ) (hx : IsAllocation x)
    (t : ∀ i, T i) (i : ι) : x t i ≤ 1 := by
  classical
  exact (single_le_sum (fun j _ => hx.1 t j) (mem_univ i)).trans (hx.2 t)

end Border
