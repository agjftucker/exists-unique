import missing_mathlib.topology.algebra.ordered
import existence continuity monotonicity

local prefix `𝒫`:100 := fun {α : Type} (s : finset α), {t // t ≤ s}

variables {𝒩 : Type} [decidable_eq 𝒩] {T : with_top ℝ}
variables {ℋ : well_behaved_soln 𝒩 T} {ℰ : equity_function 𝒩 T}

section

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

end

