import u_def v_prop q_prop

local prefix `𝒫`:100 := fun {α : Type} (s : finset α), {t // t ≤ s}

variables {𝒩 : Type} [decidable_eq 𝒩] [inner_product_space ℝ (X 𝒩)]
variables {T : with_top ℝ} {ℋ : well_behaved_soln 𝒩 T} {ℰ : equity_function 𝒩 T}

lemma u_match : ∀ A t y, u ℋ ℰ A t y = u ℋ ℰ (φ ℋ ℰ A t y) t y := v_match

namespace φp

variables {A : finset 𝒩}
variable p_ : ∀ B < A, ∀ C ≤ B, u ℋ ℰ C ≤ u ℋ ℰ B
include p_

lemma uB_le_uA_of_uC_le_uA : ∀ B ≤ A, (∀ C < B, u ℋ ℰ C ≤ u ℋ ℰ A) → u ℋ ℰ B ≤ u ℋ ℰ A :=
begin
  intros B hB h,
  apply pos_op hB,
  intros t y hy,
  rw [←set.mem_compl_iff, set.compl_inter] at hy,
  cases hy,
  { rw [v_match B, v_match A],
    apply p_ _ ⟨(φ ℋ ℰ A t y).prop, hy⟩,
    apply φ_mono hB, },
  { rw v_match B,
    apply h,
    exact ⟨(φ ℋ ℰ B t y).prop, hy⟩, },
end

lemma uB_le_uA_of_uC_le_uA' :
  ∀ B, (∀ C < B, C ≤ A → u ℋ ℰ C ≤ u ℋ ℰ A) → B ≤ A → u ℋ ℰ B ≤ u ℋ ℰ A :=
begin
  intros B h hB,
  apply uB_le_uA_of_uC_le_uA p_ B hB,
  intros C hC,
  exact h C hC (trans (le_of_lt hC) hB),
end

variable (A)

lemma uB_le_uA : ∀ B ≤ A, u ℋ ℰ B ≤ u ℋ ℰ A :=
finset.strong_induction (uB_le_uA_of_uC_le_uA' p_)

end φp

lemma u_mono : ∀ {A B : finset 𝒩}, B ≤ A → u ℋ ℰ B ≤ u ℋ ℰ A :=
finset.strong_induction φp.uB_le_uA

lemma hr1 {A : finset 𝒩} {t : Tt T} {y : X 𝒩} (B C D : 𝒫 A) :
  C < ⊤ → D ≤ C → r ℋ ℰ t y D B → r ℋ ℰ t y C B :=
begin
  intros hlt hle hr i hi,
  apply lt_of_lt_of_le (hr i hi),
  apply ℰ.mono_wrt_debt_valuation,
  apply u_mono hle,
end

lemma q_φ {A : finset 𝒩} {t : Tt T} {y : X 𝒩} : q (r ℋ ℰ t y) (φ ℋ ℰ A t y) :=
begin
  rw q_iff (r_iff' A),
  rw φ_eq,
  apply si.q_φ hr1 hr2,
end

lemma q_of_mem_U {A : finset 𝒩} {t : Tt T} {y : X 𝒩} : y ∈ U ℋ ℰ A t → q (r ℋ ℰ t y) A :=
begin
  intro h,
  rw ←le_antisymm (φ ℋ ℰ A t y).prop h,
  apply q_φ,
end

lemma mem_U_iff_q {A : finset 𝒩} {t : Tt T} {y : X 𝒩} : y ∈ U ℋ ℰ A t ↔ q (r ℋ ℰ t y) A :=
iff.intro q_of_mem_U mem_U_of_q

lemma φ_idempotent {A : finset 𝒩} : ∀ t y, y ∈ U ℋ ℰ (φ ℋ ℰ A t y) t :=
-- ∀ t y, (φ ℋ ℰ (φ ℋ ℰ A t y) t y : finset 𝒩) = φ ℋ ℰ A t y :=
begin
  intros t y,
  apply mem_U_of_q,
  apply q_φ,
end

lemma φ_maximal {A : finset 𝒩} {t : Tt T} {y : X 𝒩} :
  ∀ B ≤ A, ↑(φ ℋ ℰ A t y) < B → y ∉ U ℋ ℰ B t :=
begin
  intros B hB hφ,
  rw mem_U_iff_q,
  intro hq,
  apply hφ.2,
  rw φ_eq,
  exact si.le_φ_of_q (r_iff' A) ⟨B, hB⟩ hq,
end

lemma φ_consistent (A : finset 𝒩) (t : Tt T) (y : X 𝒩) : y ∈ U ℋ ℰ A t ↔ r ℋ ℰ t y A A :=
begin
  split,
  { intros hq i hi,
    rw mem_U_iff_q at hq,
    cases hq with _ B hlt hr hq,
    { exact false.elim hi, },
    { apply lt_of_lt_of_le (hr i hi),
      apply ℰ.mono_wrt_debt_valuation,
      apply u_mono (le_of_lt hlt), }, },
  { intro hr,
    cases dec_em (y ∈ U ℋ ℰ A t) with h hn,
    { exact h, },
    { rw mem_U_iff_q,
      refine q.succ ⟨(φ ℋ ℰ A t y).prop, hn⟩ _ q_φ,
      intros i hi,
      delta E_star,
      rw ←u_match,
      apply hr i hi, }, },
end
