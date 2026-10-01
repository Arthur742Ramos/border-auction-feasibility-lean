module
public import Border.Flow
public import Border.Auction

@[expose] public section
open scoped BigOperators
open Finset
namespace Border.Implementation
universe u v
variable {ι : Type u} [Fintype ι] {T : ι → Type v} [∀ i, Fintype (T i)]

theorem marginal_nonneg (μ : (∀ i, T i) → ℝ) (hμ : ∀ t, 0 ≤ μ t) (i : ι) (a : T i) :
    0 ≤ marginal μ i a := by
  classical
  unfold marginal
  exact sum_nonneg fun t _ => by split_ifs <;> first | exact hμ t | exact le_rfl

noncomputable def nodeCondition (μ : (∀ i, T i) → ℝ) (q : ∀ i, T i → ℝ) : Prop := by
  classical
  exact ∀ s : Finset (Sigma T),
    (∑ a ∈ s, marginal μ a.1 a.2 * q a.1 a.2) ≤
      ∑ t, if ∃ a ∈ s, t a.1 = a.2 then μ t else 0

theorem node_condition_iff (μ : (∀ i, T i) → ℝ) (q : ∀ i, T i → ℝ) :
    nodeCondition μ q ↔ BorderCondition μ q := by
  classical
  constructor
  · intro h S
    let s : Finset (Sigma T) := univ.filter fun a => a.2 ∈ S a.1
    have hh : ∀ t : ∀ i, T i, (∃ a ∈ s, t a.1 = a.2) ↔ ∃ i, t i ∈ S i := by
      intro t
      constructor
      · rintro ⟨⟨i,a⟩, ha, hta⟩
        refine ⟨i, ?_⟩
        rw [hta]
        simpa [s] using ha
      · rintro ⟨i, hi⟩
        exact ⟨⟨i,t i⟩, by simp [s, hi], rfl⟩
    have hsum : (∑ a ∈ s, marginal μ a.1 a.2 * q a.1 a.2) =
        ∑ i, ∑ a ∈ S i, marginal μ i a * q i a := by
      simp only [s, sum_filter]
      rw [Fintype.sum_sigma]
      simp [sum_ite_mem]
    have hi := h s
    simpa only [hsum, hh, hitMass] using hi
  · intro h s
    let S : ∀ i, Finset (T i) := fun i => univ.filter fun a => (⟨i,a⟩ : Sigma T) ∈ s
    have hh : ∀ t : ∀ i, T i, (∃ i, t i ∈ S i) ↔ ∃ a ∈ s, t a.1 = a.2 := by
      intro t
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨⟨i,t i⟩, by simpa [S] using hi, rfl⟩
      · rintro ⟨⟨i,a⟩, ha, hta⟩
        exact ⟨i, by simp [S, hta, ha]⟩
    have hsum : (∑ i, ∑ a ∈ S i, marginal μ i a * q i a) =
        ∑ a ∈ s, marginal μ a.1 a.2 * q a.1 a.2 := by
      simp only [S, sum_filter]
      rw [← Fintype.sum_sigma (fun a : Sigma T =>
        if a ∈ s then marginal μ a.1 a.2 * q a.1 a.2 else 0)]
      simp [sum_ite_mem]
    have hi := h S
    simpa only [hitMass, hsum, hh] using hi

theorem flow_row_sum (μ : (∀ i, T i) → ℝ)
    (f : (∀ i, T i) → Sigma T → ℝ)
    (hf : f ∈ flowSet (fun (t : ∀ i, T i) (a : Sigma T) => t a.1 = a.2) μ) (t : ∀ i, T i) :
    ∑ a, f t a = ∑ i, f t ⟨i, t i⟩ := by
  classical
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro i _
  apply sum_eq_single (t i)
  · intro a _ ha
    exact hf.2.2 t ⟨i,a⟩ (Ne.symm ha)
  · simp

theorem feasible_of_condition (μ : (∀ i, T i) → ℝ) (hμ : ∀ t, 0 ≤ μ t)
    (q : ∀ i, T i → ℝ) (hq : ∀ i a, 0 ≤ q i a) (h : BorderCondition μ q) :
    Feasible μ q := by
  classical
  obtain ⟨f, hf, hcol⟩ := fractional_hall (fun (t : ∀ i, T i) (a : Sigma T) => t a.1 = a.2)
    (fun a => marginal μ a.1 a.2 * q a.1 a.2)
    (fun a => mul_nonneg (marginal_nonneg μ hμ a.1 a.2) (hq a.1 a.2))
    μ hμ ((node_condition_iff μ q).mpr h)
  let x : (∀ i, T i) → ι → ℝ := fun t i => f t ⟨i,t i⟩ / μ t
  have hx0 : ∀ t i, 0 ≤ x t i := fun t i => div_nonneg (hf.1 t _) (hμ t)
  have hmass : ∀ t i, μ t * x t i = f t ⟨i,t i⟩ := by
    intro t i
    by_cases ht : μ t = 0
    · have hfi : f t ⟨i,t i⟩ = 0 := le_antisymm
        (ht ▸ (single_le_sum (fun a _ => hf.1 t a) (mem_univ _)).trans (hf.2.1 t))
        (hf.1 t _)
      simp [x, ht, hfi]
    · dsimp [x]
      field_simp
  refine ⟨x, ⟨hx0, ?_⟩, ?_⟩
  · intro t
    by_cases ht : μ t = 0
    · simp [x, ht]
    · have hpos : 0 < μ t := lt_of_le_of_ne (hμ t) (Ne.symm ht)
      change (∑ i, f t ⟨i,t i⟩ / μ t) ≤ 1
      rw [← sum_div]
      apply (div_le_one hpos).mpr
      rw [← flow_row_sum μ f hf t]
      exact hf.2.1 t
  · intro i a
    have hterm : ∀ t, (if t i = a then μ t * x t i else 0) = f t ⟨i,a⟩ := by
      intro t
      by_cases ht : t i = a
      · simp only [ht, ↓reduceIte, hmass]
      · simp [ht, hf.2.2 t ⟨i,a⟩ ht]
    calc
      interimMass μ x i a = ∑ t, f t ⟨i,a⟩ := by simp only [interimMass, hterm]
      _ = marginal μ i a * q i a := congrFun hcol ⟨i,a⟩

theorem condition_of_feasible (μ : (∀ i, T i) → ℝ) (hμ : ∀ t, 0 ≤ μ t)
    (q : ∀ i, T i → ℝ) (h : Feasible μ q) : BorderCondition μ q := by
  classical
  obtain ⟨x, hx, hmass⟩ := h
  let f : (∀ i, T i) → Sigma T → ℝ :=
    fun t a => if t a.1 = a.2 then μ t * x t a.1 else 0
  have hf : f ∈ flowSet (fun (t : ∀ i, T i) (a : Sigma T) => t a.1 = a.2) μ := by
    refine ⟨?_, ?_, ?_⟩
    · intro t a
      dsimp [f]
      split_ifs <;> first | exact mul_nonneg (hμ t) (hx.1 t a.1) | exact le_rfl
    · intro t
      change (∑ a : Sigma T, if t a.1 = a.2 then μ t * x t a.1 else 0) ≤ μ t
      rw [Fintype.sum_sigma]
      simp only [sum_ite_eq, mem_univ, ↓reduceIte]
      rw [← mul_sum]
      simpa using mul_le_mul_of_nonneg_left (hx.2 t) (hμ t)
    · intro t a hta
      simp [f, hta]
  have hcol : ∀ a : Sigma T, columnMap f a = marginal μ a.1 a.2 * q a.1 a.2 := by
    intro a
    exact hmass a.1 a.2
  apply (node_condition_iff μ q).mp
  intro s
  simpa only [hcol] using flow_cut (fun (t : ∀ i, T i) (a : Sigma T) => t a.1 = a.2) μ f hf s

end Border.Implementation

namespace Border
universe u v
variable {ι : Type u} [Fintype ι] {T : ι → Type v} [∀ i, Fintype (T i)]

/-- Border's finite correlated-prior feasibility theorem (weighted form). -/
theorem border_feasibility (μ : (∀ i, T i) → ℝ) (hμ : IsPrior μ)
    (q : ∀ i, T i → ℝ) (hq : ∀ i a, 0 ≤ q i a ∧ q i a ≤ 1) :
    Feasible μ q ↔ BorderCondition μ q :=
  ⟨Implementation.condition_of_feasible μ hμ.1 q,
    Implementation.feasible_of_condition μ hμ.1 q (fun i a => (hq i a).1)⟩

end Border
