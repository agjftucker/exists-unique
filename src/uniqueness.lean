import missing_mathlib.topology.algebra.ordered
import existence continuity monotonicity

local prefix `𝒫`:100 := fun {α : Type} (s : finset α), {t // t ≤ s}

variables {𝒩 : Type} [decidable_eq 𝒩] {T : with_top ℝ}
variables {ℋ : well_behaved_soln 𝒩 T} {ℰ : equity_function 𝒩 T}

variable (crash : ∀ ψ A t y,
  ∃ (η : ℝ) (hη : η ≤ 0) (i : 𝒩) (hi : i ∈ A), E_star ℰ (v ℋ ψ A) t (y + η) i ≤ 0)

section ind

variables {ψ : ∀ (A : finset 𝒩), Tt T → X 𝒩 → 𝒫 A} (hψ : survivors_fn ℋ ℰ ψ)
variables {A : finset 𝒩} (ih : ∀ B < A, ψ B = φ ℋ ℰ B)
include hψ ih

lemma vψ_continuous_wrt_assets : continuous_wrt_assets (v ℋ ψ A) :=
begin
  apply v_continuous_of_continuous_on_compl,
  intro t,
  rw continuous_on_congr (vψ_eq_u_on_compl_Vψ hψ ih),
  apply continuous.continuous_on,
  apply u_continuous_wrt_assets,
end

lemma Eψ_continuous_wrt_assets : continuous_wrt_assets (E_star ℰ (v ℋ ψ A)) :=
fun t, ℰ.continuity_preserving (vψ_continuous_wrt_assets hψ ih t)

lemma Eψ_min_continuous_wrt_assets (h : A.nonempty) {t : Tt T} :
  continuous (fun y, A.inf' h (E_star ℰ (v ℋ ψ A) t y)) :=
begin
  suffices : continuous (A.inf' h (fun i y, E_star ℰ (v ℋ ψ A) t y i)),
  { convert this,
    ext y,
    rw finset.inf'_apply, },
  apply finset.of_inf'_of_forall h,
  { exact fun _ _, continuous.min, },
  { intros i hi,
    apply continuous_iff_continuous_forall.mp,
    apply Eψ_continuous_wrt_assets hψ ih, },
end

lemma Eψ_min_continuous_wrt_η (h : A.nonempty) {t : Tt T} {y : X 𝒩} :
  continuous (fun (η : ℝ), A.inf' h (E_star ℰ (v ℋ ψ A) t (y + η))) :=
begin
  apply (Eψ_min_continuous_wrt_assets hψ ih h).comp,
  apply (continuous_add_left y).comp,
  rw continuous_iff_continuous_forall,
  intro i,
  exact continuous_id,
end

include crash

lemma exists_η₀_of_mem_Vψ (h : A.nonempty) {t : Tt T} {y : X 𝒩} :
  y ∈ V ψ A t → ∃ (η₀ : ℝ) (hη₀ : η₀ < 0), A.inf' h (E_star ℰ (v ℋ ψ A) t (y + η₀)) = 0 :=
begin
  intro hV,
  specialize crash ψ A t y,
  rcases crash with ⟨η, hη, i, hi, hE⟩,
  have hl : A.inf' h (E_star ℰ (v ℋ ψ A) t (y + η)) ≤ 0,
  { exact le_trans (finset.inf'_le _ hi) hE, },
  have hu : 0 < A.inf' h (E_star ℰ (v ℋ ψ A) t (y + 0)),
  { rw [add_zero y, finset.lt_inf'_iff],
    rwa hψ.consistent at hV, },
  have := intermediate_value_Ico hη (Eψ_min_continuous_wrt_η hψ ih h).continuous_on ⟨hl, hu⟩,
  rcases this with ⟨η₀, hη₀, he⟩,
  exact ⟨η₀, hη₀.2, he⟩,
end

lemma Vψ_subset_U : V ψ A ⊆ U ℋ ℰ A :=
begin
  intros t y hV,
  rw φ_consistent,
  intros i hi,
  rcases exists_η₀_of_mem_Vψ crash hψ ih ⟨i, hi⟩ hV with ⟨η₀, hη₀, he⟩,
  rw show y = y + η₀ + (-η₀ : ℝ),
  { exact eq_sub_of_add_eq rfl, },
  suffices : 0 ≤ E_star ℰ (u ℋ ℰ A) t (y + η₀) i,
  { apply lt_of_le_of_lt this,
    apply E_strict_mono_wrt_assets,
    linarith, },
  convert finset.inf'_le (E_star ℰ (u ℋ ℰ A) t (y + η₀)) hi,
  rw ← he,
  dunfold E_star,
  congr' 2,
  apply vψ_eq_u_on_compl_Vψ hψ ih,
  intro h,
  rw [hψ.consistent, ← finset.lt_inf'_iff ⟨i, hi⟩] at h,
  linarith,
  apply_instance,
end

variable (A)

lemma ψ_eq_φ_of_eq_on_ssubsets : ψ A = φ ℋ ℰ A :=
begin
  funext t y,
  by_cases hV : y ∈ V ψ A t,
  { apply subtype.ext,
    transitivity A,
    { exact le_antisymm (ψ A t y).prop hV, },
    { refine le_antisymm _ (φ ℋ ℰ A t y).prop,
      exact Vψ_subset_U crash hψ ih t hV, }, },
  { exact ψ_eq_φ_on_compl_Vψ hψ ih hV, },
end

end ind

lemma unique_soln : ∀ ψ, survivors_fn ℋ ℰ ψ → ψ = φ ℋ ℰ :=
fun ψ hψ, funext (finset.strong_induction (ψ_eq_φ_of_eq_on_ssubsets crash hψ))

theorem exists_unique_soln : ∃! ψ, survivors_fn ℋ ℰ ψ :=
⟨φ ℋ ℰ, exists_soln, unique_soln crash⟩
