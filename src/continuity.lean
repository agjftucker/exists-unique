import u_prop

local prefix `𝒫`:100 := fun {α : Type} (s : finset α), {t // t ≤ s}

variables {𝒩 : Type} {T : with_top ℝ}

lemma join_continuous {t : Tt T} (f g : debt_fn 𝒩 T) :
  continuous (f t) → continuous (g t) → continuous ((f ⊔ g) t) :=
begin
  intros hf hg,
  rw continuous_pi_iff,
  intro i,
  rw continuous_pi_iff,
  intro τ,
  apply continuous.max,
  all_goals
  { revert τ,
    rw ←continuous_pi_iff,
    revert i,
    rw ←continuous_pi_iff,
    assumption, },
end

variables [decidable_eq 𝒩] {ℋ : well_behaved_soln 𝒩 T} {ℰ : equity_function 𝒩 T}

section v
variable {ψ : ∀ (B : finset 𝒩), Tt T → X 𝒩 → 𝒫 B}

lemma v_continuous_of_continuous_on_compl {A : finset 𝒩} :
  (∀ t, continuous_on (v ℋ ψ A t) (V ψ A t)ᶜ) → continuous_wrt_assets (v ℋ ψ A) :=
begin
  intros h t,
  rw show v ℋ ψ A t = fun y i, ite _ _ _,
  { funext y i, rw v_eq_ite, },
  rw continuous_pi_iff,
  intro i,
  split_ifs,
  { revert t,
    apply ℋ.continuity_preserving,
    intro t,
    specialize h t,
    rw [continuous_on_iff_continuous_restrict, continuous_pi_iff] at h,
    exact h i, },
  { exact continuous_const, },
end

end v

section u
open finset

lemma u_continuous_of_continuous_on_compl {A : finset 𝒩} :
  (∀ t, continuous_on (u ℋ ℰ A t) (U ℋ ℰ A t)ᶜ) → continuous_wrt_assets (u ℋ ℰ A) :=
v_continuous_of_continuous_on_compl

lemma u_eq_on_compl {A : finset 𝒩} (hA : A.nonempty) {t : Tt T} :
  (U ℋ ℰ A t)ᶜ.eq_on (u ℋ ℰ A t) (A.ssubsets.sup' ⟨∅, empty_mem_ssubsets hA⟩ (u ℋ ℰ) t) :=
fun y, u_eq_sup'

lemma uA_continuous_of_uB_continuous (A : finset 𝒩) :
  (∀ B < A, continuous_wrt_assets (u ℋ ℰ B)) → continuous_wrt_assets (u ℋ ℰ A) :=
begin
  intro ih,
  apply u_continuous_of_continuous_on_compl,
  intro t,
  cases A.eq_empty_or_nonempty with he hne,
  { rw [he, U_empty_eq_univ, set.compl_univ],
    apply continuous_on_empty, },
  { rw continuous_on_congr (u_eq_on_compl hne),
    apply continuous.continuous_on,
    apply sup'_induction ⟨∅, empty_mem_ssubsets hne⟩ (u ℋ ℰ) join_continuous,
    intros B hB,
    apply ih,
    rwa mem_ssubsets at hB, },
end

lemma u_continuous_wrt_assets : ∀ A, continuous_wrt_assets (u ℋ ℰ A) :=
finset.strong_induction uA_continuous_of_uB_continuous

end u
