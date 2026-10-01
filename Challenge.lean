module
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Tactic

/-!
Self-contained comparison surface for Border's finite auction feasibility theorem.
All definitions and all six selected theorems are fully proved in this module.
Only pinned Mathlib is imported. The helper proofs below mirror the library,
under a different namespace; they do not constitute independent proof discovery.
-/
/- Source: Border/Auction.lean; helpers renamed for comparison. -/
section
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
end

/- Source: Border/WeightedHall.lean; helpers renamed for comparison. -/
section
@[expose] public section
open scoped BigOperators
open Finset
namespace Border.ChallengeProof

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

end Border.ChallengeProof
end

/- Source: Border/Flow.lean; helpers renamed for comparison. -/
section
@[expose] public section
open scoped BigOperators
open Finset Set
namespace Border.ChallengeProof
variable {A Ω : Type*} [Fintype A] [Fintype Ω] [DecidableEq A]

def flowSet (R : Ω → A → Prop) (c : Ω → ℝ) : Set (Ω → A → ℝ) :=
  {f | (∀ t a, 0 ≤ f t a) ∧ (∀ t, ∑ a, f t a ≤ c t) ∧
    ∀ t a, ¬ R t a → f t a = 0}

def columnMap : (Ω → A → ℝ) →ₗ[ℝ] (A → ℝ) where
  toFun f a := ∑ t, f t a
  map_add' f g := by ext a; simp [sum_add_distrib]
  map_smul' r f := by ext a; simp [mul_sum]

omit [Fintype Ω] [DecidableEq A] in
theorem flowSet_closed (R : Ω → A → Prop) (c : Ω → ℝ) : IsClosed (flowSet R c) := by
  unfold flowSet
  apply IsClosed.inter
  · change IsClosed {f : Ω → A → ℝ | ∀ t a, 0 ≤ f t a}
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun t => isClosed_iInter fun a =>
      isClosed_le (f := fun _ : Ω → A → ℝ => 0) continuous_const
        (g := fun f => f t a) (by fun_prop)
  · apply IsClosed.inter
    · change IsClosed {f : Ω → A → ℝ | ∀ t, ∑ a, f t a ≤ c t}
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun t => isClosed_le (f := fun f : Ω → A → ℝ => ∑ a, f t a)
        (by fun_prop) continuous_const
    · change IsClosed {f : Ω → A → ℝ | ∀ t a, ¬ R t a → f t a = 0}
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun t => isClosed_iInter fun a =>
        isClosed_iInter fun _ => isClosed_eq (f := fun f : Ω → A → ℝ => f t a)
          (by fun_prop) continuous_const

theorem flowSet_compact (R : Ω → A → Prop) (c : Ω → ℝ) : IsCompact (flowSet R c) := by
  apply isCompact_Icc.of_isClosed_subset (flowSet_closed R c)
  intro f hf
  refine ⟨fun t a => hf.1 t a, fun t a => ?_⟩
  exact (single_le_sum (fun b _ => hf.1 t b) (mem_univ a)).trans (hf.2.1 t)

omit [Fintype Ω] [DecidableEq A] in
theorem flowSet_convex (R : Ω → A → Prop) (c : Ω → ℝ) : Convex ℝ (flowSet R c) := by
  intro f hf g hg r s hr hs hrs
  refine ⟨?_, ?_, ?_⟩
  · intro t a
    exact add_nonneg (mul_nonneg hr (hf.1 t a)) (mul_nonneg hs (hg.1 t a))
  · intro t
    change (∑ a, (r * f t a + s * g t a)) ≤ c t
    rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    calc
      _ ≤ r * c t + s * c t := add_le_add
        (mul_le_mul_of_nonneg_left (hf.2.1 t) hr)
        (mul_le_mul_of_nonneg_left (hg.2.1 t) hs)
      _ = c t := by rw [← add_mul, hrs, one_mul]
  · intro t a hR
    change r * f t a + s * g t a = 0
    rw [hf.2.2 t a hR, hg.2.2 t a hR]
    ring

theorem linear_apply_sum (L : (A → ℝ) →ₗ[ℝ] ℝ) (d : A → ℝ) :
    L d = ∑ a, L (Pi.single a 1) * d a := by
  classical
  rw [← Finset.univ_sum_single d, map_sum]
  apply sum_congr rfl
  intro a _
  have h : Pi.single a (d a) = d a • Pi.single a (1 : ℝ) := by
    ext b
    by_cases hb : b = a <;> simp [hb]
  rw [h, map_smul]
  simp [mul_comm]

theorem greedy_flow (R : Ω → A → Prop) [DecidableRel R]
    (c : Ω → ℝ) (hc : ∀ t, 0 ≤ c t) (w : A → ℝ) :
    ∃ f ∈ flowSet R c, ∃ z : Ω → ℝ,
      (∀ t, 0 ≤ z t) ∧ (∀ t a, R t a → w a ≤ z t) ∧
      (∑ a, w a * columnMap f a) = ∑ t, c t * z t := by
  classical
  let W : Ω → Option A → ℝ := fun t o => o.elim 0 (fun a => if R t a then w a else 0)
  have hex : ∀ t, ∃ o : Option A, ∀ b, W t b ≤ W t o := by
    intro t
    obtain ⟨o, _, ho⟩ := exists_max_image univ (W t) univ_nonempty
    exact ⟨o, fun b => ho b (mem_univ b)⟩
  choose winner hwin using hex
  let z : Ω → ℝ := fun t => W t (winner t)
  let f : Ω → A → ℝ := fun t a => if winner t = some a ∧ R t a then c t else 0
  have hfzero : ∀ t a, ¬R t a → f t a = 0 := by
    intro t a ha
    simp [f, ha]
  have hfsum : ∀ t, ∑ a, f t a ≤ c t := by
    intro t
    cases hwt : winner t with
    | none => simpa [f, hwt] using hc t
    | some a =>
      by_cases hra : R t a
      · have hf : f t = Pi.single a (c t) := by
          ext b
          by_cases hb : b = a
          · subst b; simp [f, hwt, hra]
          · simp [f, hwt, hb, Ne.symm hb]
        simp [hf]
      · have hf : f t = 0 := by
          ext b
          by_cases hb : b = a
          · subst b; simp [f, hwt, hra]
          · simp [f, hwt, Ne.symm hb]
        simpa [hf] using hc t
  refine ⟨f, ⟨?_, hfsum, hfzero⟩, z, ?_, ?_, ?_⟩
  · intro t a
    dsimp [f]
    split_ifs <;> first | exact hc t | exact le_rfl
  · intro t
    exact hwin t none
  · intro t a hra
    simpa [W, hra] using hwin t (some a)
  · change (∑ a, w a * ∑ t, f t a) = _
    simp_rw [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro t _
    cases hwt : winner t with
    | none => simp [f, z, W, hwt]
    | some a =>
      by_cases hra : R t a
      · rw [sum_eq_single a]
        · simp [f, z, W, hwt, hra, mul_comm]
        · intro b _ hba
          simp [f, hwt, Ne.symm hba]
        · simp
      · have hf : f t = 0 := by
          ext b
          by_cases hb : b = a
          · subst b; simp [f, hwt, hra]
          · simp [f, hwt, Ne.symm hb]
        simp [hf, z, W, hwt, hra]

/-- Fractional Hall's theorem for real capacities, proved by finite-dimensional separation. -/
theorem fractional_hall (R : Ω → A → Prop) [DecidableRel R]
    (d : A → ℝ) (hd : ∀ a, 0 ≤ d a) (c : Ω → ℝ) (hc : ∀ t, 0 ≤ c t)
    (hcut : ∀ s : Finset A, ∑ a ∈ s, d a ≤ ∑ t, if ∃ a ∈ s, R t a then c t else 0) :
    ∃ f ∈ flowSet R c, columnMap f = d := by
  classical
  let K := columnMap '' flowSet R c
  have hconv : Convex ℝ K := (flowSet_convex R c).linear_image columnMap
  have hcomp : IsCompact K := (flowSet_compact R c).image columnMap.continuous_of_finiteDimensional
  suffices d ∈ K by exact this
  by_contra hnot
  obtain ⟨L, u, hLu, hud⟩ := geometric_hahn_banach_closed_point hconv hcomp.isClosed hnot
  let w : A → ℝ := fun a => L (Pi.single a 1)
  obtain ⟨f, hf, z, hz, he, hval⟩ := greedy_flow R c hc w
  have hbound := cut_weight_bound R d c hc hcut (fun a => max (w a) 0)
    (fun a => le_max_right _ _) z hz (fun t a hra => max_le (he t a hra) (hz t))
  have hle : L d ≤ L (columnMap f) := by
    change L.toLinearMap d ≤ L.toLinearMap (columnMap f)
    rw [linear_apply_sum L.toLinearMap d, linear_apply_sum L.toLinearMap (columnMap f)]
    change (∑ a, w a * d a) ≤ ∑ a, w a * columnMap f a
    calc
      _ ≤ ∑ a, max (w a) 0 * d a := sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_right (le_max_left _ _) (hd a)
      _ ≤ ∑ t, c t * z t := hbound
      _ = _ := hval.symm
  exact (hud.trans_le hle).not_ge (le_of_lt (hLu _ ⟨f, hf, rfl⟩))

omit [DecidableEq A] in
theorem flow_cut (R : Ω → A → Prop) [DecidableRel R] (c : Ω → ℝ)
    (f : Ω → A → ℝ) (hf : f ∈ flowSet R c) (s : Finset A) :
    ∑ a ∈ s, columnMap f a ≤ ∑ t, if ∃ a ∈ s, R t a then c t else 0 := by
  classical
  change (∑ a ∈ s, ∑ t, f t a) ≤ _
  rw [sum_comm]
  apply sum_le_sum
  intro t _
  split_ifs with hhit
  · exact (sum_le_sum_of_subset_of_nonneg (subset_univ s)
      (fun a _ _ => hf.1 t a)).trans (hf.2.1 t)
  · have hzero : ∀ a ∈ s, f t a = 0 := by
      intro a ha
      exact hf.2.2 t a (fun hR => hhit ⟨a, ha, hR⟩)
    simp [sum_eq_zero hzero]

end Border.ChallengeProof
end

/- Source: Border/Theorem.lean; helpers renamed for comparison. -/
section
@[expose] public section
open scoped BigOperators
open Finset
namespace Border.ChallengeProof
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

end Border.ChallengeProof

namespace Border
universe u v
variable {ι : Type u} [Fintype ι] {T : ι → Type v} [∀ i, Fintype (T i)]

/-- Border's finite correlated-prior feasibility theorem (weighted form). -/
theorem border_feasibility (μ : (∀ i, T i) → ℝ) (hμ : IsPrior μ)
    (q : ∀ i, T i → ℝ) (hq : ∀ i a, 0 ≤ q i a ∧ q i a ≤ 1) :
    Feasible μ q ↔ BorderCondition μ q :=
  ⟨ChallengeProof.condition_of_feasible μ hμ.1 q,
    ChallengeProof.feasible_of_condition μ hμ.1 q (fun i a => (hq i a).1)⟩

end Border
end

/- Source: Border/Support.lean; helpers renamed for comparison. -/
section
@[expose] public section
open scoped BigOperators
open Finset
namespace Border.ChallengeProof
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

end Border.ChallengeProof

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
        (ChallengeProof.marginal_nonneg μ hμ.1 i a)
      rw [ChallengeProof.interimMass_zero_of_marginal_zero μ hμ.1 x i a hz, hz, zero_mul]

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
end

/- Source: Border/Independent.lean; helpers renamed for comparison. -/
section
@[expose] public section
open scoped BigOperators
open Finset
namespace Border.ChallengeProof
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

end Border.ChallengeProof

namespace Border
attribute [local instance 100000] Classical.propDecidable
universe u v
variable {ι : Type u} [Fintype ι] {T : ι → Type v} [∀ i, Fintype (T i)]

/-- The independent-prior corollary; the distributions may differ between bidders. -/
theorem independent_border_feasibility (p q : ∀ i, T i → ℝ)
    (hp : ∀ i a, 0 ≤ p i a) (hn : ∀ i, ∑ a, p i a = 1)
    (hq : ∀ i a, 0 ≤ q i a ∧ q i a ≤ 1) :
    Feasible (productPrior p) q ↔ IndependentBorderCondition p q := by
  rw [border_feasibility (productPrior p) (ChallengeProof.product_prior_isPrior p hp hn) q hq]
  unfold BorderCondition IndependentBorderCondition
  simp only [ChallengeProof.product_marginal p hn, ChallengeProof.product_hitMass p hn]

theorem independent_border_conditional_feasibility (p q : ∀ i, T i → ℝ)
    (hp : ∀ i a, 0 ≤ p i a) (hn : ∀ i, ∑ a, p i a = 1)
    (hq : ∀ i a, 0 ≤ q i a ∧ q i a ≤ 1) :
    ConditionallyFeasible (productPrior p) q ↔ IndependentBorderCondition p q := by
  exact (feasible_iff_conditional (productPrior p) (ChallengeProof.product_prior_isPrior p hp hn) q).symm.trans
    (independent_border_feasibility p q hp hn hq)

end Border
end
