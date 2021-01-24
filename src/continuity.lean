import missing_mathlib.topology.constructions
import u_prop

variables {𝒩 : Type} [decidable_eq 𝒩] {T : with_top ℝ}
variables {ℋ : well_behaved_soln 𝒩 T} {ℰ : equity_function 𝒩 T}

lemma join_continuous {t : Tt T} (f g : debt_fn 𝒩 T) :
  continuous (f t) → continuous (g t) → continuous ((f ⊔ g) t) :=
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
  (∀ t, continuous_on (u ℋ ℰ A t) (U ℋ ℰ A t)ᶜ) → continuous_wrt_assets (u ℋ ℰ A) :=
begin
  intros h t,
  rw [u_eq_ite, continuous_iff_continuous_forall],
  intro i,
  split_ifs,
  { revert t,
    apply ℋ.continuity_preserving,
    intro t,
    simp_rw ←u_match,
    specialize h t,
    rw [continuous_on_iff_continuous_restrict, continuous_iff_continuous_forall] at h,
    exact h i, },
  { exact continuous_const, },
end

open finset

lemma u_eq_on_compl {A : finset 𝒩} (hA : A.nonempty) {t : Tt T} :
  (U ℋ ℰ A t)ᶜ.eq_on (u ℋ ℰ A t) (A.ssubsets.sup' ⟨∅, empty_mem_ssubsets hA⟩ (u ℋ ℰ) t) :=
fun y, u_eq_sup'

lemma uA_continuous_of_uB_continuous (A : finset 𝒩) :
  (∀ B < A, continuous_wrt_assets (u ℋ ℰ B)) → continuous_wrt_assets (u ℋ ℰ A) :=
begin
  intro ih,
  apply continuous_of_continuous_on_compl,
  intro t,
  cases A.eq_empty_or_nonempty with he hne,
  { rw [he, U_empty_eq_univ, set.compl_univ],
    apply continuous_on_empty, },
  { rw continuous_on_congr (u_eq_on_compl hne),
    apply continuous.continuous_on,
    apply of_sup'_of_forall ⟨∅, empty_mem_ssubsets hne⟩ (u ℋ ℰ) join_continuous,
    intros B hB,
    apply ih,
    rwa mem_ssubsets_iff at hB, },
end

lemma u_continuous_wrt_assets : ∀ (A : finset 𝒩), continuous_wrt_assets (u ℋ ℰ A) :=
finset.strong_induction uA_continuous_of_uB_continuous
