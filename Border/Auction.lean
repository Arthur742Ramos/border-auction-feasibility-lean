module
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic

@[expose] public section
open scoped BigOperators
namespace Border
universe u v
variable {ι : Type u} [Fintype ι] {T : ι → Type v} [∀ i, Fintype (T i)]

/-- A finite joint prior, with no independence restriction. -/
noncomputable def IsPrior (μ : (∀ i, T i) → ℝ) : Prop := by
  classical
  exact (∀ t, 0 ≤ μ t) ∧ ∑ t, μ t = 1

noncomputable def marginal (μ : (∀ i, T i) → ℝ) (i : ι) (a : T i) : ℝ := by
  classical
  exact ∑ t, if t i = a then μ t else 0

noncomputable def interimMass (μ : (∀ i, T i) → ℝ)
    (x : (∀ i, T i) → ι → ℝ) (i : ι) (a : T i) : ℝ := by
  classical
  exact ∑ t, if t i = a then μ t * x t i else 0

/-- Random allocation of at most one item at each profile; withholding is allowed. -/
def IsAllocation (x : (∀ i, T i) → ι → ℝ) : Prop :=
  (∀ t i, 0 ≤ x t i) ∧ ∀ t, ∑ i, x t i ≤ 1

/-- Feasibility stated without conditioning on null events. -/
def Feasible (μ : (∀ i, T i) → ℝ) (q : ∀ i, T i → ℝ) : Prop :=
  ∃ x, IsAllocation x ∧ ∀ i a, interimMass μ x i a = marginal μ i a * q i a

/-- The paper's definition: the conditional reduced form agrees on positive support. -/
def ConditionallyFeasible (μ : (∀ i, T i) → ℝ) (q : ∀ i, T i → ℝ) : Prop :=
  ∃ x, IsAllocation x ∧ ∀ i a, 0 < marginal μ i a →
    interimMass μ x i a / marginal μ i a = q i a

noncomputable def hitMass (μ : (∀ i, T i) → ℝ) (S : ∀ i, Finset (T i)) : ℝ := by
  classical
  exact ∑ t, if ∃ i, t i ∈ S i then μ t else 0

/-- Border's inequalities for every collection of bidder-specific subsets. -/
def BorderCondition (μ : (∀ i, T i) → ℝ) (q : ∀ i, T i → ℝ) : Prop :=
  ∀ S : ∀ i, Finset (T i),
    (∑ i, ∑ a ∈ S i, marginal μ i a * q i a) ≤ hitMass μ S

noncomputable def productPrior (p : ∀ i, T i → ℝ) (t : ∀ i, T i) : ℝ := ∏ i, p i (t i)

def IndependentBorderCondition (p q : ∀ i, T i → ℝ) : Prop :=
  ∀ S : ∀ i, Finset (T i),
    (∑ i, ∑ a ∈ S i, p i a * q i a) ≤ 1 - ∏ i, (1 - ∑ a ∈ S i, p i a)

end Border
