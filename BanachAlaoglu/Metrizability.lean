

import Mathlib.Analysis.NormedSpace.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Basic

-- TODO: Tag in mathlib
attribute [simp] abs_mul abs_inv

open Function

variable {X : Type*} {E : ℕ → Type*} [TopologicalSpace X] [CompactSpace X]

section PseudoMetricSpace
variable [∀ n, PseudoMetricSpace (E n)] (gs : ∀ n, X → E n)

/- Define metric -/
private noncomputable def ourMetric (x y : X) : ℝ :=
  ∑' n, (1/2)^n * min (dist (gs n x) (gs n y)) 1

variable {gs}

/- Prove requirements of pseudometricspace: `ourMetric_self`, `ourMetric_comm` and
`ourMetric_triangle`. -/
lemma ourMetric_self {x y} : x = y → ourMetric gs x y = 0 := by
  intro x_eq_y
  simp [ourMetric, one_div, inv_pow, x_eq_y, sub_self, norm_zero, mul_zero, tsum_zero]

lemma ourMetric_comm {x y} : ourMetric gs x y = ourMetric gs y x := by
  unfold ourMetric
  rw [tsum_congr]
  intro b
  rw [dist_comm]

/- A helper lemma used in `ourMetric_triangle`. -/
lemma ourMetric_bdd {x y} : (∀ (i : ℕ), ‖(fun n ↦ (1 / 2) ^ n * min (dist (gs n x) (gs n y)) 1) i‖
  ≤ (fun n ↦ (1 / 2) ^ n) i) := by
  intro i
  simp only [one_div, inv_pow, Real.norm_eq_abs, abs_mul, abs_inv, abs_pow, Nat.abs_ofNat, inv_pos,
    Nat.ofNat_pos, pow_pos, mul_le_iff_le_one_right]
  rw [abs_of_nonneg (by positivity)]
  exact min_le_right (dist (gs i x) (gs i y)) 1

/- A helper lemma used in `ourMetric_triangle`. -/
lemma summable_if_bounded {x y} : Summable fun n ↦ (1 / 2) ^ n * min (dist (gs n x) (gs n y)) 1 :=
  Summable.of_norm_bounded (fun n ↦ (1 / 2) ^ n) summable_geometric_two (ourMetric_bdd)

lemma ourMetric_triangle {x y z} : ourMetric gs x z ≤ ourMetric gs x y + ourMetric gs y z := by
  unfold ourMetric
  have tri_ineq n : (1/2)^n * min (dist (gs n x) (gs n z)) 1
      ≤ (1/2)^n * min (dist (gs n x) (gs n y)) 1 + (1/2)^n * min (dist (gs n y) (gs n z)) 1 := by
    rw [← mul_add, mul_le_mul_left]
    simp only [ne_eq, min_le_iff]
    cases' (min_cases (dist (gs n x) (gs n z)) 1)
    · cases' (min_cases (dist (gs n x) (gs n y)) 1) with h1 h2
      · obtain ⟨eq_dist, _⟩ := h1
        rw [eq_dist]
        cases' (min_cases (dist (gs n y) (gs n z)) 1) with h1 h2
        · obtain ⟨eq_dist, _⟩ := h1
          rw [eq_dist]
          left
          exact dist_triangle (gs n x) (gs n y) (gs n z)
        · obtain ⟨eq_one, _⟩ := h2
          rw [eq_one]
          right
          simp [add_le_add_left]
          positivity
      · obtain ⟨eq_one, _⟩ := h2
        rw [eq_one]
        cases' (min_cases (dist (gs n y) (gs n z)) 1) with h1 h2
        · obtain ⟨eq_dist, _⟩ := h1
          rw [eq_dist]
          right
          simp [add_le_add_left]
          positivity
        · obtain ⟨eq_one, _⟩ := h2
          rw [eq_one]
          right
          simp [add_le_add_left]

    · cases' (min_cases (dist (gs n x) (gs n y)) 1) with h1 h2
      · obtain ⟨eq_dist, _⟩ := h1
        rw [eq_dist]
        cases' (min_cases (dist (gs n y) (gs n z)) 1) with h1 h2
        · obtain ⟨eq_dist, _⟩ := h1
          rw [eq_dist]
          left
          exact dist_triangle (gs n x) (gs n y) (gs n z)
        · obtain ⟨eq_one, _⟩ := h2
          rw [eq_one]
          right
          simp [add_le_add_left]
          positivity
      · obtain ⟨eq_one, _⟩ := h2
        rw [eq_one]
        cases' (min_cases (dist (gs n y) (gs n z)) 1) with h1 h2
        · obtain ⟨eq_dist, _⟩ := h1
          rw [eq_dist]
          right
          simp [add_le_add_left]
          positivity
        · obtain ⟨eq_one, _⟩ := h2
          rw [eq_one]
          right
          simp [add_le_add_left]
    · positivity

  rw [← tsum_add]
  apply tsum_le_tsum
  · exact fun i ↦ tri_ineq i
  · exact summable_if_bounded
  · simpa [mul_add] using Summable.add summable_if_bounded summable_if_bounded
  exact summable_if_bounded
  exact summable_if_bounded

set_option linter.unusedVariables false in
/- Create a copy of the space `X` without the typeclass instances. -/
def pseudoMetricCopy (X : Type*) (gs : ∀n, X → E n) := X

/- Define a pseudometricspace on the space `pseudoMetricCopy`. -/
noncomputable def ourPseudoMetricSpace : PseudoMetricSpace X  where
  dist := ourMetric gs
  dist_self x := ourMetric_self rfl
  dist_comm x y := ourMetric_comm
  dist_triangle x y z := ourMetric_triangle
  edist_dist := by simp only [← ENNReal.ofReal_coe_nnreal, NNReal.coe_mk, implies_true]

end PseudoMetricSpace

section MetricSpace

variable [∀ n, MetricSpace (E n)] (gs : ∀ n, X → E n)
variable (gs_sep : (∀ ⦃x y⦄, x≠y → ∃ n, gs n x ≠ gs n y))

lemma ourMetric_self' (gs_sep : (∀ ⦃x y⦄, x ≠ y → ∃ n, gs n x ≠ gs n y)) {x y} :
    ourMetric gs x y = 0 → x = y := by
  intro sum
  rw [ourMetric] at sum
  have sum_zero : ∑' n, (1/2)^n * min (dist (gs n x) (gs n y)) 1 = 0 →
      ∀ n, (1/2)^n * min (dist (gs n x) (gs n y)) 1 = 0 := by
    have tsum_zero (g : ℕ → ℝ) (h : ∀ (i : ℕ), g i ≥ 0) (h' : Summable g) :
        ∑' (i : ℕ), g i = 0 ↔ ∀ (i : ℕ), g i = 0 := by
      calc
        _ ↔ HasSum g 0 := (Summable.hasSum_iff h').symm
        _ ↔ g = 0 := hasSum_zero_iff_of_nonneg h
        _ ↔ _ := Function.funext_iff
    intro sum
    let f := fun n ↦ (1/2)^n * min (dist (gs n x) (gs n y)) 1
    have terms_pos n : f n >= 0 := by positivity
    apply (tsum_zero (fun n ↦ (1/2)^n * min (dist (gs n x) (gs n y)) 1) (terms_pos)
        summable_if_bounded).mp
    exact sum
  apply sum_zero at sum
  simp only [one_div, inv_pow, mul_eq_zero, inv_eq_zero, pow_eq_zero_iff', OfNat.ofNat_ne_zero,
    ne_eq, false_and, norm_eq_zero, sub_eq_zero, false_or] at sum
  contrapose! sum
  specialize gs_sep sum
  obtain ⟨a, gs_neq⟩ := gs_sep
  use a
  by_contra h
  cases' le_or_lt (dist (gs a x) (gs a y)) 1 with h1 h2
  · simp only [min_eq_left_iff.mpr h1, dist_eq_zero, one_div, inv_pow, mul_eq_zero, inv_eq_zero,
      pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, false_and, false_or] at *

    have : min (dist (gs a x) (gs a y)) 1 = dist (gs a x) (gs a y) := by exact min_eq_left h1
    --have : dist (gs a x) (gs a y) = 0 → gs a x = gs a y := fun _ ↦ h
    rw [eq_comm] at h
    have := @zero_eq_dist X
    simp_all only [zero_le_one, min_eq_left]
    exact gs_neq trivial

  · linarith [min_eq_right_iff.mpr (LT.lt.le h2)]

noncomputable def ourMetricSpace : MetricSpace X where
  dist := ourMetric gs
  dist_self x := ourMetric_self rfl
  dist_comm x y := ourMetric_comm
  dist_triangle x y z := ourMetric_triangle
  edist_dist := by simp only [← ENNReal.ofReal_coe_nnreal, NNReal.coe_mk, implies_true]
  eq_of_dist_eq_zero := ourMetric_self' gs gs_sep

noncomputable def ourTopologicalSpace : TopologicalSpace X where
  IsOpen s := ∀ x ∈ s, ∃ ε > 0, ∀ (y : X), ourMetric gs x y < ε → y ∈ s
  isOpen_univ := by
    intro _ _
    simp_all only [Set.mem_univ, gt_iff_lt, implies_true, and_true]
    exact exists_zero_lt
  isOpen_inter := by
    intro s t
    intro sOpen tOpen
    intro x x_in_inter
    have : x ∈ s ∩ t → x ∈ s ∧ x ∈ t := by exact fun _ ↦ x_in_inter
    specialize sOpen x (by exact Set.mem_of_mem_inter_left x_in_inter)
    specialize tOpen x (by exact Set.mem_of_mem_inter_right x_in_inter)
    obtain ⟨es, espos⟩ := sOpen
    obtain ⟨et, etpos⟩ := tOpen
    use min es et
    constructor
    · have foo : es > 0 := by
        simp_all only [Set.mem_inter_iff, and_self, imp_self, gt_iff_lt]
      have : et > 0 := by
        simp_all only [Set.mem_inter_iff, and_self, imp_self, gt_iff_lt]
      exact lt_min foo this
    · intro y
      intro le_eset
      simp_all only [Set.mem_inter_iff, and_self, imp_self, gt_iff_lt, lt_min_iff]
  isOpen_sUnion := by
    intro s a x a_1
    simp_all only [gt_iff_lt, Set.mem_sUnion]
    obtain ⟨w, h⟩ := a_1
    obtain ⟨left, right⟩ := h
    specialize a w left x right
    obtain ⟨eps, h⟩ := a
    use eps
    simp_all only [true_and]
    intro y a
    obtain ⟨_, right_1⟩ := h
    apply Exists.intro
    · apply And.intro
      · exact left
      · simp_all only

def t₀ := TopologicalSpace X
variable (t₀ : TopologicalSpace X)

/- Define a function from `TopologicalSpace X` to `ourTopologicalSpace`-/
--

#check PseudoMetricSpace X
--#check Continuous[t₀, (ourTopologicalSpace gs)] id
#check @Continuous X X t₀ (ourTopologicalSpace gs) id

def fst {X : Type*} [TopologicalSpace X] := t₀
noncomputable def snd (X : Type*) [TopologicalSpace X] := @ourTopologicalSpace X E _


lemma continuous_ourMetric (gs_continuous : ∀ n, Continuous (gs n)) :
    Continuous (fun (p : X × X) ↦ ourMetric gs p.1 p.2) := by
  unfold ourMetric
  refine continuous_tsum (by fun_prop) summable_geometric_two ?_
  simp only [one_div, inv_pow, abs_mul, abs_inv, abs_pow, Real.norm_eq_abs, Nat.abs_ofNat,
    inv_pos, Nat.ofNat_pos, pow_pos, mul_le_iff_le_one_right, Prod.forall]
  intro n a b
  rw [abs_of_nonneg (by positivity)]
  exact min_le_right _ _

#check (@instTopologicalSpaceProd X X (@ourTopologicalSpace X E _ gs) (@ourTopologicalSpace X E _ gs))
#check @dist X
#check @Continuous (X × X) ℝ (@instTopologicalSpaceProd X X (@ourTopologicalSpace X E _ gs) (@ourTopologicalSpace X E _ gs)) _ (fun (p : X × X) ↦ dist (p.1) (p.2))

lemma continuous_ourMetric' (gs_continuous : ∀ n, Continuous (gs n)) :
    Continuous  (fun (p : X × X) ↦ ourMetric gs (p.1) (p.2)) := by
  exact @continuous_ourMetric X E _ gs t₀ gs_continuous


#check (@Metric.continuous_iff' X X)
#check continuous_def
lemma continuous_mk : @Continuous X X t₀ (@ourTopologicalSpace X E _ gs) id := by
  --have := @ourPseudoMetricSpace X E _ gs
  --have := @ourTopologicalSpace X E _ gs
  --have := (@continuous_iff_continuous_dist X X _ _ id).mpr --ourPseudoMetricSpace

--  have := (@Metric.continuous_iff' X X (@ourPseudoMetricSpace X E _ gs) t₀ id).mpr

 --simp_all only [id_eq, gt_iff_lt]

  rw [continuous_def]

  intro s s_open
  have : @IsOpen X (ourTopologicalSpace gs) s = ∀ x ∈ s, ∃ ε > 0, ∀ (y : X), ourMetric gs x y < ε → y ∈ s := by
    exact rfl
  rw [this] at s_open
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  specialize s_open x hx
  rcases s_open with ⟨ε, ε_pos, h_metric⟩
  let t := { y | ourMetric gs x y < ε }
  use t
  constructor
  · intros y hy
    simp only [Set.mem_preimage]
    exact h_metric y hy

  · constructor
    ·
      have metric_cont := continuous_ourMetric gs t₀
      simp_all only [ne_eq, gt_iff_lt, eq_iff_iff, Set.preimage_id_eq, id_eq, t]
      specialize h_metric

      have := @continuous_ourMetric' X E _ gs
      let dist_fun : X → ℝ := fun y ↦ ourMetric gs x y
      have dist_cont : Continuous dist_fun := by
        simp [dist_fun]

        sorry
      exact dist_cont.isOpen_preimage (Set.Iio ε) (@isOpen_Iio _ _ _ _ ε)

    · have x_in_t : x ∈ t := by
        simp [t]
        have metric_self : ourMetric gs x x = 0 := by
          exact @ourMetric_self X E _ gs x x rfl
        exact lt_of_eq_of_lt metric_self ε_pos
        --rw [metric_self]
      exact x_in_t


  -- Use the fact that `ourMetric gs x x = 0`

  --intro x ε hε
  --have cont_dist : Continuous (fun y ↦ dist (kopio.mk X gs gs_sep y)
    --  (kopio.mk X gs gs_sep x)) := by
    --apply Continuous.along_fst (cont_ourMetric' gs_sep gs_cont)

--  have interval_open : IsOpen (Set.Iio ε) := by exact isOpen_Iio
  --have := @IsOpen.mem_nhds X x _ _ (cont_dist.isOpen_preimage _ interval_open) (by simpa using hε)
  --filter_upwards [this] with y hy using hy

  --apply continuous_def.mpr
  --intro s s_open



  --have := @continuous_id X _


--lemma continuous_function : Continuous[t₀, ourTopologicalSpace] id := by sorry

--#check Continuous[t₀, ourTopologicalSpace]

lemma continuous_toOrigin : @Continuous X X (@ourTopologicalSpace X E _ gs) t₀ id := by
  have ourTopo := @ourTopologicalSpace X E _ gs


  --have symm (s : Set X) : continuous_toOrigin X gs gs_sep ⁻¹' s = metricCopy.mk X gs gs_sep '' s :=
    --Eq.symm (Set.EqOn.image_eq_self fun ⦃x⦄ ↦ congrFun rfl)
  have closed_impl (s : Set X) : IsClosed s → IsClosed (id ⁻¹' s) := by
    intro s_closed
    exact s_closed


  have := continuous_iff_isClosed.mpr closed_impl
  have : @IsClosed X (ourTopologicalSpace gs) (id ⁻¹' M) := by
      --simp only [symm M]

      have M_image_cpt : @IsCompact X (ourTopologicalSpace gs) (M) := by
        rw [@isCompact_iff_finite_subcover]
        have M_cpt_X := @IsClosed.isCompact X t₀ M
        simp_all only [ne_eq, Set.preimage_id_eq, id_eq, implies_true]

      specialize this M
      simp only [Set.preimage_id_eq, id_eq] at *
      specialize blah M
      have := @IsCompact.isClosed X (ourTopologicalSpace gs) (?_) M M_image_cpt
      exact this
      · rw [t2Space_iff]
        intro x y x_ne_y
        let d := ourMetric gs x y
        have d_pos : 0 < d := by
          unfold_let
          rw [ourMetric]
          apply tsum_pos
          · exact summable_if_bounded
          · intro i
            positivity
          · have (a b : ℝ) ( ha : a > 0) (hb :b > 0) : a * b > 0 := by
              exact Real.mul_pos ha hb
            apply Real.mul_pos
            · positivity
            ·

              sorry


          · exact USize.size
    --have s_cpt_X := IsClosed.isCompact s_closed
  --   rw [isCompact_iff_finite_subcover] at s_cpt_X
  --   have open_preimage s : IsOpen s → IsOpen (metricCopy.mk X gs gs_sep ⁻¹' s) :=
  --     continuous_def.mp (continuous_metricCopy_mk gs_sep gs_continuous) s
  --   have closed_preimage_s : IsClosed (metricCopy.toOrigin X gs gs_sep ⁻¹' s) := by
  --     have s_image_cpt : IsCompact (metricCopy.mk X gs gs_sep '' s) := by
  --       apply isCompact_of_finite_subcover
  --       intro _ Us Usi_open
  --       simp only [metricCopy.mk, id_eq, Set.image_id']
  --       exact fun a ↦ s_cpt_X Us (fun i ↦ open_preimage (Us i) (Usi_open i)) a
  --     simpa [symm s] using IsCompact.isClosed s_image_cpt
  --   exact closed_preimage_s
  -- exact continuous_iff_isClosed.mpr closed_impl

  sorry



noncomputable def homeomorph_OurMetric :
  X ≃ₜ X where
    toFun := id
    invFun := id
    left_inv := congrFun rfl
    right_inv := congrFun rfl
    continuous_toFun := continuous_id --continuous_mk
    continuous_invFun := continuous_id--continuous_toOrigin


lemma equal : t₀ = (@ourTopologicalSpace X E _ gs) := by
  refine TopologicalSpace.ext_iff.mpr ?_
  have mk := @continuous_mk X E _ gs
  have too := @continuous_toOrigin X E _ gs
  intro s
  constructor
  · specialize too t₀
    simp [continuous_def] at too
    exact too s
  · specialize mk t₀
    simp [continuous_def] at mk
    exact mk s


/- If X is compact, and there exists a seq of continuous real-valued functions that
separates points on X, then X is metrizable. -/
lemma X_metrizable (gs : ∀ n, X → E n) (gs_continuous : ∀ n, Continuous (gs n))
    (gs_sep : (∀ ⦃x y⦄, x≠y → ∃ n, gs n x ≠ gs n y)) :
    TopologicalSpace.MetrizableSpace X := by
    have hom := (@Homeomorph X X t₀ (@ourTopologicalSpace X E _ gs))
    use ourMetricSpace gs gs_sep
    have : (@ourPseudoMetricSpace X E _ gs).toUniformSpace.toTopologicalSpace = ourTopologicalSpace gs := by
      --exact equal gs UniformSpace.toTopologicalSpace
      sorry


--have := hom.embedding.metrizableSpace

    sorry
    --(homeomorph_OurMetric gs_continuous gs_sep).embedding.metrizableSpace

--end Metrizable_of_compactSpace
end MetricSpace
