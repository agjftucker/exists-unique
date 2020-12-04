import missing_mathlib.topology.constructions
import missing_mathlib.data.set.function
import u_prop

open finset

variables {𝒩 : Type} [decidable_eq 𝒩] [inner_product_space ℝ (X 𝒩)]
variables {T : with_top ℝ} {ℋ : well_behaved_soln 𝒩 T} {ℰ : equity_function 𝒩 T}

lemma join_continuous {t : Tt T} (f g : X 𝒩 → 𝒩 → Tτ t → ℝ) :
  continuous f → continuous g → continuous (f ⊔ g) :=
begin
  intros hf hg,
  rw continuous_iff_continuous_forall,
  intro i,
  rw continuous_iff_continuous_forall,
  intro τ,
  apply continuous.max,
  all_goals
  { revert τ,
    rw ←continuous_iff_continuous_forall,
    revert i,
    rw ←continuous_iff_continuous_forall,
    assumption, },
end

lemma continuous_of_continuous_on_compl {A : finset 𝒩} :
  continuous_wrt_assets_on_compl (fun t y (h : y ∉ U ℋ ℰ A t), (u ℋ ℰ A t y : 𝒩 → Tτ t → ℝ)) →
  continuous_wrt_assets (u ℋ ℰ A) :=
begin
  intros h t,
  rw [u_eq_ite, continuous_iff_continuous_forall],
  intro i,
  cases dec_em (i ∈ A) with hi hi,
  { revert t,
    simp_rw if_pos hi,
    apply ℋ.continuity_preserving,
    intro t,
    specialize h t,
    rw continuous_iff_continuous_forall at h,
    convert h i,
    dsimp only [],
    funext y,
    rw ←u_match, },
  { simp_rw if_neg hi,
    exact continuous_const, },
end

lemma u_eq_sup' {A : finset 𝒩} (hA : A.nonempty) (t : Tt T) :
  (U ℋ ℰ A t)ᶜ.eq_on (u ℋ ℰ A t) (A.ssubsets.sup' ⟨∅, empty_mem_ssubsets hA⟩ (fun B, u ℋ ℰ B t)) :=
begin
  intros y hy,
  rw u_match,
  apply le_antisymm,
  { apply le_sup' (fun B, u ℋ ℰ B t),
    rw mem_ssubsets_iff,
    use [(φ ℋ ℰ A t y).prop, hy], },
  { apply sup'_le _ (fun B, u ℋ ℰ B t),
    intros B hB y,
    change u ℋ ℰ B t y ≤ u ℋ ℰ (φ ℋ ℰ A t y) t y,
    rw u_match B,
    apply u_mono,
    apply φ_mono,
    rw mem_ssubsets_iff at hB,
    exact hB.1, },
end

lemma uA_continuous_of_uB_continuous (A : finset 𝒩) :
  (∀ B < A, continuous_wrt_assets (u ℋ ℰ B)) → continuous_wrt_assets (u ℋ ℰ A) :=
begin
  intro ih,
  cases dec_em (A = ∅) with he hne,
  { subst he,
    intro t,
    rw [u_eq_ite, continuous_iff_continuous_forall],
    intro i,
    simp_rw if_neg (not_mem_empty i),
    exact continuous_const, },
  { rw [←ne.def, ←nonempty_iff_ne_empty] at hne,
    apply continuous_of_continuous_on_compl,
    intro t,
    change continuous ((U ℋ ℰ A t)ᶜ.restrict (u ℋ ℰ A t)),
    rw set.restrict_eq_iff_eq_on.mpr (u_eq_sup' hne t),
    rw ←continuous_on_iff_continuous_restrict,
    apply continuous.continuous_on,
    apply of_sup'_of_forall ⟨∅, empty_mem_ssubsets hne⟩ (fun B, u ℋ ℰ B t) join_continuous,
    intros B hB,
    apply ih,
    rwa mem_ssubsets_iff at hB, },
end

lemma u_continuous_wrt_assets : ∀ (A : finset 𝒩), continuous_wrt_assets (u ℋ ℰ A) :=
finset.strong_induction uA_continuous_of_uB_continuous
