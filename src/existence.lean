import u_prop

local prefix `𝒫`:100 := fun {α : Type} (s : finset α), {t // t ≤ s}

variables {𝒩 : Type} [decidable_eq 𝒩] {T : with_top ℝ}
variables (ℋ : well_behaved_soln 𝒩 T) (ℰ : equity_function 𝒩 T)

structure survivors_fn (ψ :  ∀ (A : finset 𝒩), Tt T → X 𝒩 → 𝒫 A) : Prop :=
(idempotent : ∀ A t y, y ∈ V ψ (ψ A t y) t)
(maximal : ∀ A B t y, ↑(ψ A t y) < B → B ≤ A → y ∉ V ψ B t)
(consistent : ∀ A t y, y ∈ V ψ A t ↔ ∀ i ∈ A, 0 < E_star ℰ (v ℋ ψ A) t y i)

variables {ℋ} {ℰ}

lemma φ_idempotent (A : finset 𝒩) : ∀ t y, y ∈ U ℋ ℰ (φ ℋ ℰ A t y) t :=
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
  { intros hU i hi,
    cases q_of_mem_U hU with _ B hlt hr hq,
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

lemma exists_soln : survivors_fn ℋ ℰ (φ ℋ ℰ) :=
⟨φ_idempotent, φ_maximal, φ_consistent⟩

theorem φ_greatest (A : finset 𝒩) (t : Tt T) (y : X 𝒩) :
  ∀ B ≤ A, y ∈ U ℋ ℰ B t → B ≤ φ ℋ ℰ A t y :=
begin
  intros B hB hU,
  apply le_trans hU,
  apply φ_mono hB,
end

noncomputable instance (A : finset 𝒩) (t : Tt T) (y : X 𝒩) : order_top {B : 𝒫 A | y ∈ U ℋ ℰ B t} :=
{ top := ⟨φ ℋ ℰ A t y, φ_idempotent A t y⟩,
  le_top := fun ⟨B, hB⟩, φ_greatest A t y B B.prop hB,
  .. subtype.partial_order _ }

lemma mem_Vψ_iff_q {ψ : ∀ A, Tt T → X 𝒩 → 𝒫 A} {A : finset 𝒩} (ih : ∀ B < A, ψ B = φ ℋ ℰ B)
  {B : finset 𝒩} (hB : B < A) : ∀ t y, y ∈ V ψ B t ↔ q (r ℋ ℰ t y) B :=
begin
  intros t y,
  rw ← mem_U_iff_q,
  change B ≤ ψ B t y ↔ B ≤ φ ℋ ℰ B t y,
  rw ih B hB,
end

variables {ψ : ∀ (A : finset 𝒩), Tt T → X 𝒩 → 𝒫 A} (hψ : survivors_fn ℋ ℰ ψ)
variables {A : finset 𝒩} (ih : ∀ B < A, ψ B = φ ℋ ℰ B)
include hψ ih

lemma U_subset_Vψ : U ℋ ℰ A ⊆ V ψ A :=
begin
  intros t y hA,
  rw mem_U_iff_q at hA,
  by_contra hnV,
  have ltA : ↑(ψ A t y) < A := ⟨(ψ A t y).prop, hnV⟩,
  have hq : q (r ℋ ℰ t y) (ψ A t y),
  { rw ← mem_Vψ_iff_q ih ltA,
    apply hψ.idempotent, },
  obtain ⟨B, hB₁, hB₂, hB₃, hB₄⟩ := exists_ge_term_of_q hA (ψ A t y) ltA hq,
  cases lt_or_eq_of_le hB₁ with ltB eqB,
  { apply hψ.maximal A B t y ltB hB₂.1,
    rw mem_Vψ_iff_q ih hB₂,
    exact hB₃, },
  { apply hnV,
    rw hψ.consistent,
    delta E_star,
    rw [v_match, v_eq_of_ψ_eq_on_ssubsets A ih _ ltA, eqB],
    exact hB₄, },
end

lemma ψ_eq_φ_on_compl_Vψ {t : Tt T} : (V ψ A t)ᶜ.eq_on (ψ A t) (φ ℋ ℰ A t) :=
begin
  intros y hnV,
  have hUψ : y ∈ U ℋ ℰ (ψ A t y) t,
  { delta U V,
    rw ← ih _ ⟨(ψ A t y).prop, hnV⟩,
    apply hψ.idempotent, },
  suffices : (⟨ψ A t y, hUψ⟩ : {B : 𝒫 A | y ∈ U ℋ ℰ B t}) = ⊤,
  { rwa subtype.ext_iff at this, },
  apply unique_maximal_of_greatest,
  rintros ⟨B, hUB⟩ hψB,
  apply hψ.maximal A B t y hψB B.prop,
  refine U_subset_Vψ hψ _ t hUB,
  intros C hC,
  apply ih,
  exact lt_of_lt_of_le hC B.prop,
end

lemma vψ_eq_u_on_compl_Vψ {t : Tt T} : (V ψ A t)ᶜ.eq_on (v ℋ ψ A t) (u ℋ ℰ A t) :=
begin
  intros y hnV,
  rw [v_match, u_match, ← ψ_eq_φ_on_compl_Vψ hψ ih hnV],
  rw v_eq_of_ψ_eq_on_ssubsets _ ih _ ⟨(ψ A t y).prop, hnV⟩,
  refl,
end
