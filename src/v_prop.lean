--import multiset
import v_def

variables {𝒩 : Type} [fintype 𝒩] [decidable_eq 𝒩] [inner_product_space ℝ (X 𝒩)]
variables {T : with_top ℝ} (ℋ : well_behaved_soln 𝒩 T)

{ψ ψ' : finset 𝒩 → Tt T → X 𝒩 → finset 𝒩} (hψ : ∀ B, ψ B ≤ B) (hψ' : ∀ B, ψ' B ≤ B)

lemma v_eq_of_ψ_eq_on_ssubsets : ∀ A, (∀ B < A, ψ B = ψ' B) → (∀ B < A, v ℋ hψ B = v ℋ hψ' B) :=
finset.strong_induction
begin
  intros A ih h' B hB,
  conv_lhs { rw [v, finset.strong_induction_eq, ←v], },
  conv_rhs { rw [v, finset.strong_induction_eq, ←v], },
  congr,
  { exact h' B hB, },
  { specialize ih B hB (λ C hC, h' C (trans hC hB)),
    funext C hC,
    exact ih C hC, },
end

lemma v_match : ∀ A t y, v ℋ hψ A t y = v ℋ hψ (ψ A t y) t y :=
begin
  intros A t y,
  by_cases hA : ψ A t y = A,
  { rw hA, },
  { funext i,
    conv_lhs
    { rw [v, finset.strong_induction_eq, ←v, v_mk],
      change ite (i ∈ A) (ℋ (λ s x h, v ℋ hψ (ψ A s x) s x i) t y) 0, },
    split_ifs with hi,
    { apply ℋ.matches_on_complement,
      exact hA, },
    { conv_rhs
      { rw [v, finset.strong_induction_eq, ←v, v_mk],
        change ite (i ∈ ψ A t y) (ℋ (λ s x h, v ℋ hψ (ψ (ψ A t y) s x) s x i) t y) 0, },
      rw if_neg (λ h, hi (hψ A t y h)), }, },
end

lemma v_nonneg : ∀ A, 0 ≤ v ℋ hψ A :=
finset.strong_induction
begin
  intros A ih,
  rw [v, finset.strong_induction_eq, ←v, v_mk],
  intros t y i,
  change 0 ≤ ite (i ∈ A) (ℋ (λ s x h, v ℋ hψ (ψ A s x) s x i) t y) 0,
  split_ifs with hi,
  { apply ℋ.positivity_preserving,
    intros s x h,
    apply ih,
    exact lt_of_le_of_ne (hψ A s x) h, },
  { exact le_refl 0, },
end

lemma pos_op {A B : finset 𝒩} (hr : B ≤ A) :
  (∀ s x, x ∉ V ψ A s ∩ V ψ B s → v ℋ hψ B s x ≤ v ℋ hψ A s x) → v ℋ hψ B ≤ v ℋ hψ A :=
begin
  intros hc t y,
  intro i,
  conv_lhs
  { rw [v, finset.strong_induction_eq],
    change ite (i ∈ B) (ℋ (λ s x h, v ℋ hψ (ψ B s x) s x i) t y) 0, },
  split_ifs with hi,
  { conv_rhs
    { rw [v, finset.strong_induction_eq],
      change ite (i ∈ A) (ℋ (λ s x h, v ℋ hψ (ψ A s x) s x i) t y) 0,
      rw if_pos (hr hi), },
    revert t y,
    let vA := λ s x (h : x ∉ V ψ A s), v ℋ hψ (ψ A s x) s x i,
    let vB := λ s x (h : x ∉ V ψ B s), v ℋ hψ (ψ B s x) s x i,
    change ℋ vB ≤ ℋ vA,
    have hA : ℋ vA = ℋ (λ s x (h : x ∉ V ψ A s ∩ V ψ B s), ℋ vA s x),
    { apply ℋ.compatible_on_subsets,
      intro s,
      apply set.inter_subset_left, },
    have hB : ℋ vB = ℋ (λ s x (h : x ∉ V ψ A s ∩ V ψ B s), ℋ vB s x),
    { apply ℋ.compatible_on_subsets,
      intro s,
      apply set.inter_subset_right, },
    rw [hA, hB],
    apply ℋ.mono_wrt_val_on_compl,
    intros t y h,
    specialize hc t y h i,
    conv_lhs at hc
    { rw [v, finset.strong_induction_eq],
      change ite (i ∈ B) (ℋ (λ s x h, v ℋ hψ (ψ B s x) s x i) t y) 0, },
    conv_rhs at hc
    { rw [v, finset.strong_induction_eq],
      change ite (i ∈ A) (ℋ (λ s x h, v ℋ hψ (ψ A s x) s x i) t y) 0, },
    rw [if_pos hi, if_pos (hr hi)] at hc,
    exact hc, },
  { apply v_nonneg, },
end
