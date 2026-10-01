module
public import Border.WeightedHall

@[expose] public section
open scoped BigOperators
open Finset Set
namespace Border.Implementation
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

end Border.Implementation
