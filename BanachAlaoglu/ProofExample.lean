import Mathlib

/- Let X and Y be topological spaces, f : X → Y a continuous function and
K ⊆ X a sequentially compact subset. Then the image f[K]⊆ Y is sequentially compact.
-/

lemma IsSeqCompact.image' {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
    (f_cont : SeqContinuous f) {K : Set X} (K_cpt : IsSeqCompact K) :
  IsSeqCompact (f '' K) := by
  intro ys ys_in_fK
  let xs := fun n ↦ Exists.choose (ys_in_fK n)
  obtain ⟨xs_in_K, fxs_eq_ys⟩ : (∀ n, xs n ∈ K) ∧ ∀ n, f (xs n) = ys n :=
    forall_and.mp fun n ↦ Exists.choose_spec (ys_in_fK n)
  simp only [Set.mem_image, exists_exists_and_eq_and]
  obtain ⟨a, a_in_K, phi, phi_mono, xs_phi_lim⟩ := K_cpt xs_in_K
  refine ⟨a, a_in_K, phi, phi_mono, ?_⟩
  apply Filter.Tendsto.congr (fun x ↦ fxs_eq_ys (phi x))
  apply f_cont
  exact xs_phi_lim
