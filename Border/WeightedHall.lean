module
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Tactic

@[expose] public section
open scoped BigOperators
open Finset
namespace Border.Implementation

variable {A Ω : Type*} [Fintype A] [Fintype Ω] [DecidableEq A]

/-- The finite threshold decomposition of the cut inequalities. -/
theorem cut_weight_bound (R : Ω → A → Prop) [DecidableRel R]
    (d : A → ℝ) (c : Ω → ℝ) (hc : ∀ t, 0 ≤ c t)
    (hcut : ∀ s : Finset A, ∑ a ∈ s, d a ≤ ∑ t, if ∃ a ∈ s, R t a then c t else 0)
    (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (z : Ω → ℝ)
    (hz : ∀ t, 0 ≤ z t) (hedge : ∀ t a, R t a → w a ≤ z t) :
    ∑ a, w a * d a ≤ ∑ t, c t * z t := by
  classical
  suffices H : ∀ s : Finset A, ∀ w : A → ℝ, (∀ a, 0 ≤ w a) →
      (∀ a, a ∉ s → w a = 0) → ∀ z : Ω → ℝ, (∀ t, 0 ≤ z t) →
      (∀ t a, R t a → w a ≤ z t) →
      ∑ a, w a * d a ≤ ∑ t, c t * z t by
    exact H univ w hw (by simp) z hz hedge
  intro s
  refine Finset.strongInductionOn s ?_
  intro s ih w hw hs z hz he
  by_cases hp : ∀ a ∈ s, w a = 0
  · have hzero : w = 0 := by
      funext a
      by_cases ha : a ∈ s
      · exact hp a ha
      · exact hs a ha
    simp only [hzero, Pi.zero_apply, zero_mul, sum_const_zero]
    exact sum_nonneg fun t _ => mul_nonneg (hc t) (hz t)
  · let p := s.filter (fun a => 0 < w a)
    have pne : p.Nonempty := by
      push Not at hp
      obtain ⟨a, ha, hwa⟩ := hp
      exact ⟨a, mem_filter.mpr ⟨ha, lt_of_le_of_ne (hw a) (Ne.symm hwa)⟩⟩
    obtain ⟨j, hj, hmin⟩ := exists_min_image p w pne
    have hjp := (mem_filter.mp hj).2
    have hjs := (mem_filter.mp hj).1
    let v : A → ℝ := fun a => if a ∈ p then w a - w j else 0
    let u : Ω → ℝ := fun t => if ∃ a ∈ p, R t a then z t - w j else z t
    have hv : ∀ a, 0 ≤ v a := by
      intro a
      dsimp [v]
      split_ifs with ha
      · exact sub_nonneg.mpr (hmin a ha)
      · exact le_rfl
    have hvzero : ∀ a, a ∉ s.erase j → v a = 0 := by
      intro a ha
      by_cases hap : a ∈ p
      · have has := (mem_filter.mp hap).1
        have haj : a = j := by simpa [mem_erase, has] using ha
        simp [v, haj]
      · simp [v, hap]
    have hu : ∀ t, 0 ≤ u t := by
      intro t
      dsimp [u]
      split_ifs with ht
      · obtain ⟨a, ha, hra⟩ := ht
        exact sub_nonneg.mpr ((hmin a ha).trans (he t a hra))
      · exact hz t
    have he' : ∀ t a, R t a → v a ≤ u t := by
      intro t a hra
      by_cases ha : a ∈ p
      · simp only [v, ha, ↓reduceIte, u, show ∃ b ∈ p, R t b from ⟨a, ha, hra⟩]
        exact sub_le_sub_right (he t a hra) _
      · simpa [v, ha] using hu t
    have hi := ih (s.erase j) (erase_ssubset hjs) v hv hvzero u hu he'
    have hwdecomp : ∀ a, w a = v a + if a ∈ p then w j else 0 := by
      intro a
      by_cases ha : a ∈ p
      · simp [v, ha]
      · have hwa : w a = 0 := by
          by_cases has : a ∈ s
          · have hnot : ¬ 0 < w a := by simpa [p, has] using ha
            exact le_antisymm (le_of_not_gt hnot) (hw a)
          · exact hs a has
        simp [v, ha, hwa]
    have hzdecomp : ∀ t, z t = u t + if ∃ a ∈ p, R t a then w j else 0 := by
      intro t
      dsimp [u]
      split_ifs <;> ring
    have hscale := mul_le_mul_of_nonneg_left (hcut p) (le_of_lt hjp)
    have hd : (∑ a, w a * d a) = (∑ a, v a * d a) + w j * ∑ a ∈ p, d a := by
      calc
        _ = ∑ a, (v a + if a ∈ p then w j else 0) * d a :=
          sum_congr rfl fun a _ => congrArg (fun r => r * d a) (hwdecomp a)
        _ = _ := by simp [add_mul, sum_add_distrib, ite_mul, sum_ite_mem, mul_sum]
    have hcdecomp : (∑ t, c t * z t) = (∑ t, c t * u t) +
        w j * ∑ t, if ∃ a ∈ p, R t a then c t else 0 := by
      calc
        _ = ∑ t, c t * (u t + if ∃ a ∈ p, R t a then w j else 0) :=
          sum_congr rfl fun t _ => congrArg (fun r => c t * r) (hzdecomp t)
        _ = _ := by
          simp only [mul_add, sum_add_distrib, mul_sum]
          congr 1
          apply sum_congr rfl
          intro t _
          split_ifs <;> ring
    rw [hd, hcdecomp]
    exact add_le_add hi hscale

end Border.Implementation
