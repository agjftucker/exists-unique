import v_def q_def

local prefix `𝒫`:100 := fun {α : Type} (s : finset α), {t // t ≤ s}

variables {𝒩 : Type} [decidable_eq 𝒩] [inner_product_space ℝ (X 𝒩)]
variables {T : with_top ℝ} (ℋ : well_behaved_soln 𝒩 T)

def mono_wrt_assets (υ : debt_fn 𝒩 T) : Prop :=
∀ (η : ℝ) (hr : 0 ≤ η) (t : Tt T) (y : X 𝒩), υ t (y - η) ≤ υ t y

def strict_mono_wrt_assets (E : Tt T → X 𝒩 → 𝒩 → ℝ) : Prop :=
∀ (η : ℝ) (hr : 0 < η) (t : Tt T) (y : X 𝒩) (i : 𝒩), E t (y - η) i < E t y i

def E_star (ℰ : ∀ (t : Tt T), X 𝒩 → (𝒩 → Tτ t → ℝ) → 𝒩 → ℝ) : debt_fn 𝒩 T → Tt T → X 𝒩 → 𝒩 → ℝ :=
fun υ t y, ℰ t y (υ t y)

section
variables (𝒩) (T)

structure equity_function :=
(ℰ : ∀ (t : Tt T), X 𝒩 → (𝒩 → Tτ t → ℝ) → 𝒩 → ℝ)
(mono_wrt_debt_valuation {t : Tt T} {y : X 𝒩} {υ₁ υ₂ : 𝒩 → Tτ t → ℝ} : υ₁ ≤ υ₂ → ℰ t y υ₁ ≤ ℰ t y υ₂)
(continuity_preserving (υ : debt_fn 𝒩 T) : ∀ t, continuous (υ t) → continuous (E_star ℰ υ t))
(mono_preserving_wrt_assets {υ : debt_fn 𝒩 T} : mono_wrt_assets υ → strict_mono_wrt_assets (E_star ℰ υ))

end

instance : has_coe_to_fun (equity_function 𝒩 T) :=
{ F := fun _, ∀ (t : Tt T), X 𝒩 → (𝒩 → Tτ t → ℝ) → 𝒩 → ℝ,
  coe := equity_function.ℰ }

variable (ℰ : equity_function 𝒩 T)

def v_ {A : finset 𝒩} (ψ : ∀ B < A, Tt T → X 𝒩 → 𝒫 B) : ∀ B < A, debt_fn 𝒩 T :=
finset.strong_induction (fun B υ hB, v_mk ℋ (ψ B hB) (fun C hC, υ C hC (trans hC hB)))

lemma v_eq_v_ {ψ : ∀ B, Tt T → X 𝒩 → 𝒫 B} :
  ∀ A B (hB : B < A), v ℋ ψ B = v_ ℋ (fun C _, ψ C) B hB :=
λ A, finset.strong_induction
begin
  intros B ih hB,
  conv_lhs { rw [v, finset.strong_induction_eq, ←v], },
  conv_rhs { rw [v_, finset.strong_induction_eq, ←v_], },
  congr,
  funext C hC,
  exact ih C hC (trans hC hB),
end

section construct_φ

variables {A : finset 𝒩} (φ_ : ∀ B < A, Tt T → X 𝒩 → 𝒫 B)

def u_ :  ∀ B < A, debt_fn 𝒩 T := v_ ℋ φ_

def r_ (t : Tt T) (y : X 𝒩) (C B : 𝒫 A) : Prop := 
∃ (hC : ↑C < A), ∀ i ∈ (B : finset 𝒩), 0 < E_star ℰ (u_ ℋ φ_ C hC) t y i

noncomputable instance (t : Tt T) (y : X 𝒩) : decidable_rel (r_ ℋ ℰ φ_ t y) :=
fun _ _, exists_prop_decidable _

variable (A)

noncomputable def φ_mk : Tt T → X 𝒩 → 𝒫 A :=
λ t y, si.φ (r_ ℋ ℰ φ_ t y)

end construct_φ

noncomputable def φ : ∀ (A : finset 𝒩), Tt T → X 𝒩 → 𝒫 A :=
finset.strong_induction (φ_mk ℋ ℰ)

noncomputable def u : finset 𝒩 → debt_fn 𝒩 T := v ℋ (φ ℋ ℰ)

def r (t : Tt T) (y : X 𝒩) (C B : finset 𝒩) : Prop :=
∀ i ∈ B, 0 < E_star ℰ (u ℋ ℰ C) t y i

noncomputable instance (t : Tt T) (y : X 𝒩) : decidable_rel (r ℋ ℰ t y) :=
fun _ _, finset.decidable_dforall_finset

lemma r_iff {t : Tt T} {y : X 𝒩} (A : finset 𝒩) :
  ∀ (B C : 𝒫 A), C < B → (r ℋ ℰ t y C B ↔ r_ ℋ ℰ (fun D < A, φ ℋ ℰ D) t y C B) :=
begin
  rintros ⟨B, hB⟩ ⟨C, hC⟩ hlt,
  split,
  { intro hr,
    use lt_of_lt_of_le hlt hB,
    rwa [u_, ←v_eq_v_], },
  { rintros ⟨hC, hr_⟩,
    rwa [u_, ←v_eq_v_] at hr_, },
end

def U : finset 𝒩 → Tt T → set (X 𝒩) := V (φ ℋ ℰ)

lemma mem_U_of_q (A : finset 𝒩) {t : Tt T} (y : X 𝒩) : q (r ℋ ℰ t y) A → y ∈ U ℋ ℰ A t :=
begin
  intro hq,
  rw [U, V, φ, finset.strong_induction_eq, ←φ],
  apply si.le_φ_of_q (r_iff ℋ ℰ A) ⟨A, refl _⟩,
  exact hq,
  apply_instance,
end

lemma φ_mono {A B : finset 𝒩} : B ≤ A → ∀ t y, (φ ℋ ℰ B t y : finset 𝒩) ≤ φ ℋ ℰ A t y :=
begin
  intros hB t y,
  conv_lhs { rw [φ, finset.strong_induction_eq, ←φ], },
  conv_rhs { rw [φ, finset.strong_induction_eq, ←φ], },
  apply si.φ_mono (r_iff ℋ ℰ A) (r_iff ℋ ℰ B) hB,
  apply_instance,
end
