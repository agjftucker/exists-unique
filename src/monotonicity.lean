import u_prop

variables {𝒩 : Type} [decidable_eq 𝒩] {T : with_top ℝ}
variables {ℋ : well_behaved_soln 𝒩 T} {ℰ : equity_function 𝒩 T}

namespace mo
variable {A : finset 𝒩}

lemma ssubsets_sup'_le {hA : A.ssubsets.nonempty} : A.ssubsets.sup' hA (u ℋ ℰ) ≤ u ℋ ℰ A :=
begin
  apply finset.sup'_le _ (u ℋ ℰ),
  intros B hB,
  rw finset.mem_ssubsets at hB,
  apply u_mono,
  exact hB.1,
end

variable (ih : ∀ B < A, mono_wrt_assets (u ℋ ℰ B))
include ih

lemma ssubsets_sup'_mono {hA : A.ssubsets.nonempty} {η : ℝ} (hη : 0 ≤ η) {t : Tt T} {y : X 𝒩} :
  A.ssubsets.sup' hA (u ℋ ℰ) t y ≤ A.ssubsets.sup' hA (u ℋ ℰ) t (y + η) :=
begin
  conv_lhs { rw [finset.sup'_apply, finset.sup'_apply], },
  apply finset.sup'_le _ (fun B, u ℋ ℰ B t y),
  intros B hB,
  transitivity' u ℋ ℰ B t (y + η),
  { rw finset.mem_ssubsets at hB,
    apply ih B hB η hη, },
  { apply finset.le_sup' (u ℋ ℰ) hB, },
end

lemma u_mono_wrt_assets_on_compl {η : ℝ} (hη : 0 ≤ η) {t : Tt T} {y : X 𝒩} :
  y ∉ U ℋ ℰ A t → u ℋ ℰ A t y ≤ u ℋ ℰ A t (y + η) :=
fun hU,
calc u ℋ ℰ A t y = A.ssubsets.sup' _ (u ℋ ℰ) t y         : u_eq_sup' hU
             ... ≤ A.ssubsets.sup' _ (u ℋ ℰ) t (y + η)   : ssubsets_sup'_mono ih hη
             ... ≤ u ℋ ℰ A t (y + η)                     : ssubsets_sup'_le t (y + η)

lemma subset_shifted {η : ℝ} (hη : 0 ≤ η) (t : Tt T) (y : X 𝒩) :
  y ∈ U ℋ ℰ A t → y + η ∈ U ℋ ℰ A t :=
begin
  rw [mem_U_iff_q, mem_U_iff_q],
  intro h,
  induction h with B C hlt hr hC hC',
  { apply q.base, },
  { have hr' : r ℋ ℰ t (y + η) C B,
    { intros i hi,
      apply lt_of_lt_of_le (hr i hi),
      refine mono_of_strict_mono_wrt_assets _ η hη t y i,
      apply ℰ.mono_preserving_wrt_assets,
      exact ih C hlt, },
    apply q.succ hlt hr',
    apply hC',
    intros D hlt',
    apply ih,
    exact trans hlt' hlt, },
end

lemma eq_shifted {η : ℝ} (hη : 0 ≤ η) {t : Tt T} {y : X 𝒩} {i : 𝒩} (hi : i ∈ A) :
  ℋ (fun s x (h : x ∉ U ℋ ℰ A s), u ℋ ℰ A s x i) t (y + η) =
  ℋ (fun s x (h : x ∉ U ℋ ℰ A s), u ℋ ℰ A s (x + η) i) t y :=
begin
  apply trans (ℋ.translation_invariant _ η t y),
  apply congr_fun,
  apply congr_fun,
  rw ℋ.compatible_on_subsets (subset_shifted ih hη),
  apply congr_arg,
  funext s x h,
  rw [u_eq_ite, if_pos hi],
  symmetry,
  apply ℋ.translation_invariant,
end

variable (A)

lemma u_mono_wrt_assets : mono_wrt_assets (u ℋ ℰ A) :=
begin
  intros η hη t y i,
  rw [u_eq_ite, u_eq_ite],
  split_ifs with hi,
  { rw eq_shifted ih hη hi,
    apply ℋ.mono_wrt_val_on_compl,
    intros s x hx,
    apply u_mono_wrt_assets_on_compl ih hη hx, },
  { exact refl 0, },
end

end mo

lemma u_mono_wrt_assets : ∀ A, mono_wrt_assets (u ℋ ℰ A) :=
finset.strong_induction mo.u_mono_wrt_assets

lemma E_strict_mono_wrt_assets : ∀ A, strict_mono_wrt_assets (E_star ℰ (u ℋ ℰ A)) :=
fun A, ℰ.mono_preserving_wrt_assets (u_mono_wrt_assets A)

