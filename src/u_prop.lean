import u_def v_prop q_prop

local prefix `𝒫`:100 := fun {α : Type} (s : finset α), {t // t ≤ s}

variables {𝒩 : Type} [decidable_eq 𝒩] {T : with_top ℝ}
variables {ℋ : well_behaved_soln 𝒩 T} {ℰ : equity_function 𝒩 T}

lemma u_match : ∀ A t y, u ℋ ℰ A t y = u ℋ ℰ (φ ℋ ℰ A t y) t y := v_match

lemma u_eq_ite (A : finset 𝒩) (t : Tt T) (y : X 𝒩) (i : 𝒩) : u ℋ ℰ A t y i =
  ite (i ∈ A) (ℋ (fun s x (h : x ∉ U ℋ ℰ A s), u ℋ ℰ A s x i) t y) 0 :=
begin
  conv_lhs
  { rw [u, v, finset.strong_induction_eq],
    change ite (i ∈ A) (ℋ (fun s x (h : x ∉ U ℋ ℰ A s), u ℋ ℰ (φ ℋ ℰ A s x) s x i) t y) 0, },
  simp_rw ←u_match,
end

namespace φp

variables {A : finset 𝒩} (p_ : ∀ B < A, ∀ C ≤ B, u ℋ ℰ C ≤ u ℋ ℰ B)
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

lemma u_eq_sup' {A : finset 𝒩} {t : Tt T} {y : X 𝒩} (h : y ∉ U ℋ ℰ A t) :
  u ℋ ℰ A t y = A.ssubsets.sup' (ssubsets_nonempty_of_not_mem_U h) (u ℋ ℰ) t y :=
begin
  apply le_antisymm,
  { rw u_match,
    apply finset.le_sup' (u ℋ ℰ),
    rw finset.mem_ssubsets_iff,
    use [(φ ℋ ℰ A t y).prop, h], },
  { apply finset.sup'_le _ (u ℋ ℰ),
    intros B hB y,
    apply u_mono,
    rw finset.mem_ssubsets_iff at hB,
    exact hB.1, },
end

lemma hr0 {t : Tt T} {y : X 𝒩} (B : finset 𝒩) : r ℋ ℰ t y B ∅ :=
begin
  intros i hi,
  exfalso,
  exact hi,
end

lemma hr1 {t : Tt T} {y : X 𝒩} (C D : finset 𝒩) (hle : D ≤ C) :
  ∀ B, r ℋ ℰ t y D B → r ℋ ℰ t y C B :=
begin
  intros B hr i hi,
  apply lt_of_lt_of_le (hr i hi),
  apply ℰ.mono_wrt_debt_valuation,
  apply u_mono hle,
end

lemma hr2 {t : Tt T} {y : X 𝒩} (B C D : finset 𝒩) :
  r ℋ ℰ t y D B → r ℋ ℰ t y D C → r ℋ ℰ t y D (B ⊔ C) :=
begin
  intros rDB rDC i hi,
  cases finset.mem_union.mp hi with hB hC,
  { exact rDB i hB, },
  { exact rDC i hC, },
end

instance (t : Tt T) (y : X 𝒩) : tuckerian (r ℋ ℰ t y) :=
{ bottom := hr0,
  sup := hr2,
  downward_closed := hr1 }

instance (A : finset 𝒩) (t : Tt T) (y : X 𝒩) : tuckerian (r' ℋ ℰ A t y) :=
{ bottom := fun B, hr0 ↑B,
  sup := fun B C D, hr2 ↑B ↑C ↑D,
  downward_closed := fun C D hle B, hr1 ↑C ↑D hle ↑B }

lemma q_φ {A : finset 𝒩} {t : Tt T} {y : X 𝒩} : q (r ℋ ℰ t y) (φ ℋ ℰ A t y) :=
begin
  rw q_iff (r_iff' A),
  rw φ_eq,
  exact si.q_φ,
end

lemma q_of_mem_U {A : finset 𝒩} {t : Tt T} {y : X 𝒩} : y ∈ U ℋ ℰ A t → q (r ℋ ℰ t y) A :=
begin
  intro h,
  rw ←le_antisymm (φ ℋ ℰ A t y).prop h,
  apply q_φ,
end

lemma mem_U_iff_q {A : finset 𝒩} {t : Tt T} {y : X 𝒩} : y ∈ U ℋ ℰ A t ↔ q (r ℋ ℰ t y) A :=
iff.intro q_of_mem_U mem_U_of_q

lemma φ_idempotent (A : finset 𝒩) : ∀ t y, y ∈ U ℋ ℰ (φ ℋ ℰ A t y) t :=
-- ∀ t y, (φ ℋ ℰ (φ ℋ ℰ A t y) t y : finset 𝒩) = φ ℋ ℰ A t y :=
begin
  intros t y,
  apply mem_U_of_q,
  apply q_φ,
end

lemma φ_maximal (A B : finset 𝒩) (t : Tt T) (y : X 𝒩) :
  ↑(φ ℋ ℰ A t y) < B → B ≤ A → y ∉ U ℋ ℰ B t :=
begin
  intros hφ hB,
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
      apply u_mono hlt.1, }, },
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

section
variables (ℋ) (ℰ)

structure survivors_fn (ψ :  ∀ (A : finset 𝒩), Tt T → X 𝒩 → 𝒫 A) : Prop :=
(idempotent : ∀ A t y, y ∈ V ψ (ψ A t y) t)
(maximal : ∀ A B t y, ↑(ψ A t y) < B → B ≤ A → y ∉ V ψ B t)
(consistent : ∀ A t y, y ∈ V ψ A t ↔ ∀ i ∈ A, 0 < E_star ℰ (v ℋ ψ A) t y i)

end

lemma exists_soln : survivors_fn ℋ ℰ (φ ℋ ℰ) :=
⟨φ_idempotent, φ_maximal, φ_consistent⟩
