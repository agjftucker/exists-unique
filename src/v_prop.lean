import v_def

local prefix `𝒫`:100 := fun {α : Type} (s : finset α), {t // t ≤ s}

variables {𝒩 : Type} [decidable_eq 𝒩] {T : with_top ℝ}
variables {ℋ : well_behaved_soln 𝒩 T}

variables {ψ ψ' : ∀ (B : finset 𝒩), Tt T → X 𝒩 → 𝒫 B}

lemma V_empty_eq_univ (t : Tt T) : V ψ ∅ t = set.univ :=
begin
  apply set.eq_univ_of_forall,
  intro y,
  apply finset.empty_subset,
end

lemma ssubsets_nonempty {A : finset 𝒩} {t : Tt T} {y : X 𝒩} : y ∉ V ψ A t → A.ssubsets.nonempty :=
begin
  intro hy,
  use ∅,
  apply finset.empty_mem_ssubsets,
  rw finset.nonempty_iff_ne_empty,
  intro he,
  apply hy,
  rw [he, V_empty_eq_univ],
  trivial,
end

lemma v_eq_of_ψ_eq_on_ssubsets (A : finset 𝒩) :
  (∀ B < A, ψ B = ψ' B) → (∀ B < A, v ℋ ψ B = v ℋ ψ' B) :=
begin
  induction A using finset.strong_induction with A ih,
  intros hψ B hB,
  conv_lhs { rw [v, finset.strong_induction_eq, ←v], },
  conv_rhs { rw [v, finset.strong_induction_eq, ←v], },
  congr,
  { exact hψ B hB, },
  { specialize ih B hB (fun C hC, hψ C (trans hC hB)),
    funext C hC,
    exact ih C hC, },
end

lemma v_match : ∀ A t y, v ℋ ψ A t y = v ℋ ψ (ψ A t y) t y :=
begin
  intros A t y,
  cases dec_em (y ∈ V ψ A t) with hy hy,
  { rw le_antisymm (ψ A t y).prop hy, },
  { funext i,
    conv_lhs
    { rw [v, finset.strong_induction_eq, ←v],
      change ite (i ∈ A) (ℋ (fun s x _, v ℋ ψ (ψ A s x) s x i) t y) 0, },
    split_ifs with hi,
    { apply ℋ.matching_on_complement,
      exact hy, },
    conv_rhs
    { rw [v, finset.strong_induction_eq, ←v],
      change ite (i ∈ ↑(ψ A t y)) (ℋ (fun s x _, v ℋ ψ (ψ (ψ A t y) s x) s x i) t y) 0,
      rw if_neg (fun h, hi ((ψ A t y).prop h)), }, },
end

lemma v_eq_ite (A : finset 𝒩) (t : Tt T) (y : X 𝒩) (i : 𝒩) : v ℋ ψ A t y i =
  ite (i ∈ A) (ℋ (fun s x (h : x ∉ V ψ A s), v ℋ ψ A s x i) t y) 0 :=
begin
  conv_lhs
  { rw [v, finset.strong_induction_eq],
    change ite (i ∈ A) (ℋ (fun s x (h : x ∉ V ψ A s), v ℋ ψ (ψ A s x) s x i) t y) 0, },
  simp_rw ←v_match,
end

lemma v_nonneg (A : finset 𝒩) : 0 ≤ v ℋ ψ A :=
begin
  induction A using finset.strong_induction with A ih,
  rw [v, finset.strong_induction_eq, ←v],
  intros t y i,
  change 0 ≤ ite (i ∈ A) (ℋ (fun s x _, v ℋ ψ (ψ A s x) s x i) t y) 0,
  split_ifs with hi,
  { apply ℋ.positivity_preserving,
    intros s x h,
    apply ih,
    use [(ψ A s x).prop, h], },
  { exact refl 0, },
end

lemma pos_op {A B : finset 𝒩} (hle : B ≤ A) :
  (∀ s x, x ∉ V ψ A s ∩ V ψ B s → v ℋ ψ B s x ≤ v ℋ ψ A s x) → v ℋ ψ B ≤ v ℋ ψ A :=
begin
  intros hc t y i,
  let vA := λ s x (h : x ∉ V ψ A s), v ℋ ψ (ψ A s x) s x i,
  let vB := λ s x (h : x ∉ V ψ B s), v ℋ ψ (ψ B s x) s x i,
  conv_lhs
  { rw [v, finset.strong_induction_eq, ←v],
    change ite (i ∈ B) (ℋ vB t y) 0, },
  split_ifs with hi,
  { conv_rhs
    { rw [v, finset.strong_induction_eq, ←v],
      change ite (i ∈ A) (ℋ vA t y) 0, },
    rw if_pos (hle hi),
    revert t y,
    change ℋ vB ≤ ℋ vA,
    have hB : ℋ vB = ℋ (λ s x (h : x ∉ V ψ A s ∩ V ψ B s), ℋ vB s x),
    { apply ℋ.compatible_on_subsets,
      intro s,
      exact set.inter_subset_right _ _, },
    have hA : ℋ vA = ℋ (λ s x (h : x ∉ V ψ A s ∩ V ψ B s), ℋ vA s x),
    { apply ℋ.compatible_on_subsets,
      intro s,
      exact set.inter_subset_left _ _, },
    rw [hB, hA],
    apply ℋ.mono_wrt_val_on_compl,
    intros t y h,
    specialize hc t y h i,
    conv_lhs at hc
    { rw [v, finset.strong_induction_eq],
      change ite (i ∈ B) (ℋ vB t y) 0, },
    conv_rhs at hc
    { rw [v, finset.strong_induction_eq],
      change ite (i ∈ A) (ℋ vA t y) 0, },
    rw [if_pos hi, if_pos (hle hi)] at hc,
    exact hc, },
  { apply v_nonneg, },
end
