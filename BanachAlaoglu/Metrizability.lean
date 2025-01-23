

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
variable (t₀ : TopologicalSpace X) (CompactSpace_t₀ : @CompactSpace X t₀)
--instance CompactSpace_t₀ : @CompactSpace X t₀ := by
variable (gs_continuous : ∀ n, Continuous (gs n))



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
--#check @Continuous (X × X) ℝ (@instTopologicalSpaceProd X X (@ourTopologicalSpace X E _ gs) (@ourTopologicalSpace X E _ gs)) _ (fun (p : X × X) ↦ dist (p.1) (p.2))

lemma continuous_ourMetric' (gs_continuous : ∀ n, Continuous (gs n)) :
    Continuous  (fun (p : X × X) ↦ ourMetric gs (p.1) (p.2)) := by
  exact @continuous_ourMetric X E _ gs t₀ gs_continuous


#check (@Metric.continuous_iff' X X)
#check continuous_def
lemma continuous_mk : @Continuous X X t₀ (@ourTopologicalSpace X E _ gs) id := by
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
  · exact h_metric
  · constructor
    · have metric_cont := continuous_ourMetric gs t₀
      simp_all only [ne_eq, gt_iff_lt, eq_iff_iff, Set.preimage_id_eq, id_eq, t]
      specialize h_metric

      have := @continuous_ourMetric' X E _ gs t₀
      let dist_fun : X → ℝ := fun y ↦ ourMetric gs x y
      --have : Continuous
      have dist_cont : @Continuous X ℝ t₀ _ dist_fun := by
        unfold_let
        exact @Continuous.along_snd X X ℝ _ _ _ (fun (p : X × X) ↦ ourMetric gs p.1 p.2) (continuous_ourMetric gs t₀ gs_continuous) x
      exact dist_cont.isOpen_preimage (Set.Iio ε) (@isOpen_Iio _ _ _ _ ε)
    · have x_in_t : x ∈ t := by
        simp [t]
        have metric_self : ourMetric gs x x = 0 := by
          exact @ourMetric_self X E _ gs x x rfl
        exact lt_of_eq_of_lt metric_self ε_pos
        --rw [metric_self]
      exact x_in_t



lemma continuous_toOrigin : @Continuous X X (@ourTopologicalSpace X E _ gs) t₀ id := by
  have : ∀ (s : Set X), @IsClosed X t₀ s → @IsClosed X (ourTopologicalSpace gs) (id ⁻¹'s) := by
    intro M M_closed
    --have M_cpt_X := @IsClosed.isCompact --M_closed
    --rw [isCompact_iff_finite_subcover] at M_cpt_X
    have : ∀ s : Set X, @IsOpen X (ourTopologicalSpace gs) s → @IsOpen X t₀ (id ⁻¹' s) := by
      intro s
      have := continuous_mk gs t₀ gs_continuous
      rw [continuous_def] at this
      specialize this s
      exact this

    have : @IsClosed X (ourTopologicalSpace gs) (id ⁻¹' M) := by
      have M_image_cpt : @IsCompact X (ourTopologicalSpace gs) (M) := by
        have M_cpt_X := @IsClosed.isCompact X t₀ M CompactSpace_t₀ M_closed
        simp_all only [ne_eq, Set.preimage_id_eq, id_eq, implies_true]
        rw [@isCompact_iff_finite_subcover] at *
        intro I c_elem c_elem_open set_in_inter
        specialize M_cpt_X c_elem
        refine IsCompact.elim_finite_subcover ?hs c_elem ?hUo set_in_inter
        · exact IsClosed.isCompact M_closed
        · intro i
          apply this
          exact c_elem_open i
      simp only [Set.preimage_id_eq, id_eq] at *
      have := @IsCompact.isClosed X (ourTopologicalSpace gs) (?_) M M_image_cpt
      exact this
      · rw [t2Space_iff]
        intro x y x_ne_y
        let d := ourMetric gs x y
        have d_nonneg : 0 ≤ d := by
          unfold_let
          rw [ourMetric]
          apply tsum_nonneg
          · intro i
            positivity
        let U := {z | ourMetric gs x z < d / 2}
        let V := {z | ourMetric gs y z < d / 2}
        have U_open : @IsOpen X (ourTopologicalSpace gs) U := by
          intro z hz
          use d / 2 - ourMetric gs x z
          constructor
          · simp only [gt_iff_lt, sub_pos]
            exact hz
          · intro w hw
            have h_triangle : ourMetric gs x w ≤ ourMetric gs x z + ourMetric gs z w := by exact
              ourMetric_triangle
            have h_bound : ourMetric gs x w < d / 2 := by linarith [h_triangle, hw]
            simp only [U, Set.mem_setOf_eq]
            exact h_bound
        have ne_imp_pos : x ≠ y → ourMetric gs x y > 0 := by
              intro x_ne_y
              rw[ourMetric]
              have := gs_sep x_ne_y
              obtain ⟨n, neq⟩  := this

              apply tsum_pos summable_if_bounded (by intro i; positivity) n


              · have (a b : ℝ) ( ha : a > 0) (hb :b > 0) : a * b > 0 := by
                  exact Real.mul_pos ha hb
                apply Real.mul_pos
                · positivity
                · simp only [lt_min_iff, dist_pos, zero_lt_one, and_true]
                  exact neq




        have V_open : @IsOpen X (ourTopologicalSpace gs) V := by
          intro z hz
          use d / 2 - ourMetric gs y z
          constructor
          · simp only [gt_iff_lt, sub_pos]
            exact hz
          · intro w hw
            have h_triangle : ourMetric gs y w ≤ ourMetric gs y z + ourMetric gs z w := by exact
              ourMetric_triangle
            have h_bound : ourMetric gs y w < d / 2 := by linarith [h_triangle, hw]
            simp only [V, Set.mem_setOf_eq]
            exact h_bound
        use U, V
        refine ⟨U_open, V_open, ?_, ?_⟩
        · simp [U]
          rw [ourMetric_self]
          ·

            simp only [Nat.ofNat_pos, div_pos_iff_of_pos_right, gt_iff_lt]
            simp [d]
            apply ne_imp_pos
            exact x_ne_y

          · rfl
        · constructor
          · simp [V]
            rw [ourMetric_self]
            · simp only [Nat.ofNat_pos, div_pos_iff_of_pos_right, gt_iff_lt]
              simp [d]
              apply ne_imp_pos
              exact x_ne_y
            · rfl
          · have disjoint {a : Set X} {b : Set X} : a ∩ b = ∅ ↔ ∀ t, t ∈ a → t ∉ b := by
              constructor
              intro h
              intros z hzU hzV
              have := @Set.mem_inter_iff X z a b
              simp_all only [ne_eq, Set.mem_empty_iff_false, and_self, iff_true]

              intro h
              simp_all only [ne_eq]
              ext1 x
              simp_all only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and, not_false_eq_true, implies_true]

            rw [Set.disjoint_iff]
            simp only [Set.subset_empty_iff]
            rw [disjoint]
            intro t t_in_U
            simp_all only [ne_eq, implies_true, Set.mem_setOf_eq, not_lt, d, U, V]
            have blah : ourMetric gs x y ≤ ourMetric gs t y + ourMetric gs x t := by
              rw [add_comm]
              exact ourMetric_triangle

            --simp at this --using [t_in_U]
            have boo := LT.lt.le t_in_U
            --apply ourMetric_comm at boo
            have hmm := @le_add_of_le_add_left ℝ _ _ _ (ourMetric gs x y) (ourMetric gs t y) (ourMetric gs x t) (ourMetric gs x y / 2) blah boo
            --have : 0 ≤ ourMetric gs t y := by sorry
            have haa := @sub_le_sub_right ℝ _ _ _ (ourMetric gs x y) (ourMetric gs t y + ourMetric gs x y / 2) (hmm) (ourMetric gs x y / 2)
            have heh : ourMetric gs x y / 2 - ourMetric gs x y / 2 = 0 := by
              exact @sub_self ℝ _ (ourMetric gs x y / 2)
            have : ourMetric gs x y - ourMetric gs x y / 2 = ourMetric gs x y / 2 := by
              exact sub_half (ourMetric gs x y)
            rw [this] at haa

            simp [add_assoc, heh] at haa
            nth_rewrite 2 [ourMetric_comm]
            exact haa


    exact this
  rw [@continuous_iff_isClosed X X (@ourTopologicalSpace X E _ gs) t₀ id]
  exact fun s a ↦ this s a

example (a b c d : ℝ) (h1 : a < b + c) (h2: b < d) : a ≤ d + c :=  by apply?


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
  · specialize too gs_sep t₀ CompactSpace_t₀
    specialize too gs_continuous
    simp [continuous_def] at too
    exact too s

  · specialize mk t₀
    specialize mk gs_continuous
    simp [continuous_def] at mk
    exact mk s




/- If X is compact, and there exists a seq of continuous real-valued functions that
separates points on X, then X is metrizable. -/
lemma X_metrizable (gs : ∀ n, X → E n) (gs_continuous : ∀ n, Continuous (gs n))
    (gs_sep : (∀ ⦃x y⦄, x≠y → ∃ n, gs n x ≠ gs n y)) :
    TopologicalSpace.MetrizableSpace X := by
    letI : MetricSpace X := ourMetricSpace gs gs_sep --TopologicalSpace.metrizableSpaceMetric
    use this
    have hom := (@Homeomorph X X t₀ (@ourTopologicalSpace X E _ gs))

    --use ourMetricSpace gs gs_sep

    have : (@ourPseudoMetricSpace X E _ gs).toUniformSpace.toTopologicalSpace = ourTopologicalSpace gs := by
      --refine equal gs gs_sep --UniformSpace.toTopologicalSpace ?CompactSpace_t₀ ?gs_continuous
      refine equal gs gs_sep UniformSpace.toTopologicalSpace ?CompactSpace_t₀ ?gs_continuous

      --have := (@ourPseudoMetricSpace X E _ gs).toUniformSpace
      --have := @UniformSpace.toTopologicalSpace X this
      --have := equal gs gs_sep t₀ CompactSpace_t₀ gs_continuous
      --rw [← this]
      --refine TopologicalSpace.ext_iff.mpr ?_

      ·

        sorry



      ·

        sorry


--have := hom.embedding.metrizableSpace

    rw [this]
    exact Eq.symm (equal gs gs_sep t₀ CompactSpace_t₀ gs_continuous)

    --(homeomorph_OurMetric gs_continuous gs_sep).embedding.metrizableSpace

--end Metrizable_of_compactSpace
end MetricSpace
