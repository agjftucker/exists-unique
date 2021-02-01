import u_prop

local prefix `𝒫`:100 := fun {α : Type} (s : finset α), {t // t ≤ s}

variables {𝒩 : Type} [decidable_eq 𝒩] {T : with_top ℝ}
variables {ℋ : well_behaved_soln 𝒩 T} {ℰ : equity_function 𝒩 T}

namespace mo

variables {A : finset 𝒩}

lemma ssubsets_sup'_le {hA : A.ssubsets.nonempty} : A.ssubsets.sup' hA (u ℋ ℰ) ≤ u ℋ ℰ A :=
begin
  apply finset.sup'_le _ (u ℋ ℰ),
  intros B hB,
  rw finset.mem_ssubsets_iff at hB,
  apply u_mono,
  exact hB.1,
end

variable (p_ : ∀ B < A, mono_wrt_assets (u ℋ ℰ B))
include p_

lemma ssubsets_sup'_mono {hA : A.ssubsets.nonempty} {η : ℝ} (hη : 0 ≤ η) {t : Tt T} {y : X 𝒩} :
  A.ssubsets.sup' hA (u ℋ ℰ) t y ≤ A.ssubsets.sup' hA (u ℋ ℰ) t (y + η) :=
begin
  conv_lhs { rw [finset.sup'_apply, finset.sup'_apply], },
  apply finset.sup'_le _ (fun B, u ℋ ℰ B t y),
  intros B hB,
  transitivity' u ℋ ℰ B t (y + η),
  { rw finset.mem_ssubsets_iff at hB,
    apply p_ B hB hη, },
  { apply finset.le_sup' (u ℋ ℰ) hB, },
end

lemma u_mono_wrt_assets_on_compl {η : ℝ} (hη : 0 ≤ η) {t : Tt T} {y : X 𝒩} :
  y ∉ U ℋ ℰ A t → u ℋ ℰ A t y ≤ u ℋ ℰ A t (y + η) :=
fun hU,
calc u ℋ ℰ A t y = A.ssubsets.sup' _ (u ℋ ℰ) t y         : u_eq_sup' hU
             ... ≤ A.ssubsets.sup' _ (u ℋ ℰ) t (y + η)   : ssubsets_sup'_mono p_ hη
             ... ≤ u ℋ ℰ A t (y + η)                     : ssubsets_sup'_le t (y + η)

end mo
