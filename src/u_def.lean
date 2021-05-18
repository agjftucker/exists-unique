import v_def q_def

local prefix `𝒫`:100 := fun {α : Type} (s : finset α), {t // t ≤ s}

variables {𝒩 : Type} {T : with_top ℝ}

def mono_wrt_assets {β : Tt T → Type*} [∀ t, has_le (β t)] (f : ∀ (t : Tt T), X 𝒩 → β t) : Prop :=
∀ (η : ℝ) (hη : 0 ≤ η) (t : Tt T) (y : X 𝒩), f t y ≤ f t (y + η)

def strict_mono_wrt_assets (E : Tt T → X 𝒩 → 𝒩 → ℝ) : Prop :=
∀ (η : ℝ) (hη : 0 < η) (t : Tt T) (y : X 𝒩) (i : 𝒩), E t y i < E t (y + η) i

lemma mono_of_strict_mono_wrt_assets {E : Tt T → X 𝒩 → 𝒩 → ℝ} :
  strict_mono_wrt_assets E → mono_wrt_assets E :=
begin
  intros h η hη t y i,
  cases lt_or_eq_of_le hη with hlt he,
  { apply le_of_lt,
    apply h η hlt, },
  { apply le_of_eq,
    congr,
    rw ← he,
    symmetry,
    apply add_zero, },
end

def E_star (ℰ : ∀ (t : Tt T), X 𝒩 → (𝒩 → Tτ t → ℝ) → 𝒩 → ℝ) : debt_fn 𝒩 T → Tt T → X 𝒩 → 𝒩 → ℝ :=
fun υ t y, ℰ t y (υ t y)

section
variables (𝒩) (T)

structure equity_function :=
(ℰ : ∀ (t : Tt T), X 𝒩 → (𝒩 → Tτ t → ℝ) → 𝒩 → ℝ)
(mono_wrt_debt_valuation {t : Tt T} {y : X 𝒩} {υ₁ υ₂ : 𝒩 → Tτ t → ℝ} : υ₁ ≤ υ₂ → ℰ t y υ₁ ≤ ℰ t y υ₂)
(continuity_preserving {υ : debt_fn 𝒩 T} {t : Tt T} : continuous (υ t) → continuous (E_star ℰ υ t))
(mono_preserving_wrt_assets {υ : debt_fn 𝒩 T} : mono_wrt_assets υ → strict_mono_wrt_assets (E_star ℰ υ))

end

instance : has_coe_to_fun (equity_function 𝒩 T) :=
{ F := fun _, ∀ (t : Tt T), X 𝒩 → (𝒩 → Tτ t → ℝ) → 𝒩 → ℝ,
  coe := equity_function.ℰ }

variables [decidable_eq 𝒩] (ℋ : well_behaved_soln 𝒩 T) (ℰ : equity_function 𝒩 T)

def v_ {A : finset 𝒩} (ψ : ∀ B < A, Tt T → X 𝒩 → 𝒫 B) : ∀ B < A, debt_fn 𝒩 T :=
finset.strong_induction (fun B υ hB, v_mk ℋ (ψ B hB) (fun C hC, υ C hC (trans hC hB)))

lemma v_eq {ψ : ∀ B, Tt T → X 𝒩 → 𝒫 B} :
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

section φc

variables {A : finset 𝒩} (φ_ : ∀ B < A, Tt T → X 𝒩 → 𝒫 B)

def u_ :  ∀ B < A, debt_fn 𝒩 T := v_ ℋ φ_

def r_ (t : Tt T) (y : X 𝒩) (C B : 𝒫 A) : Prop := 
∃ (hC : ↑C < A), ∀ i ∈ (B : finset 𝒩), 0 < E_star ℰ (u_ ℋ φ_ C hC) t y i

noncomputable instance (t : Tt T) (y : X 𝒩) : decidable_rel (r_ ℋ ℰ φ_ t y) :=
by { delta r_, apply_instance, }

variable (A)

noncomputable def φ_mk : Tt T → X 𝒩 → 𝒫 A :=
λ t y, si.φ (r_ ℋ ℰ φ_ t y)

end φc

noncomputable def φ : ∀ (A : finset 𝒩), Tt T → X 𝒩 → 𝒫 A :=
finset.strong_induction (φ_mk ℋ ℰ)

def U : finset 𝒩 → Tt T → set (X 𝒩) := V (φ ℋ ℰ)

noncomputable def u : finset 𝒩 → debt_fn 𝒩 T := v ℋ (φ ℋ ℰ)

def r (t : Tt T) (y : X 𝒩) (C B : finset 𝒩) : Prop :=
∀ i ∈ B, 0 < E_star ℰ (u ℋ ℰ C) t y i

def r' (A : finset 𝒩) (t : Tt T) (y : X 𝒩) (C B : 𝒫 A) : Prop :=
r ℋ ℰ t y ↑C ↑B

noncomputable instance dec_mem_U (A : finset 𝒩) (t : Tt T) : ∀ y, decidable (y ∈ U ℋ ℰ A t) :=
by { delta U, apply_instance, }

noncomputable instance (t : Tt T) (y : X 𝒩) : decidable_rel (r ℋ ℰ t y) :=
by { delta r, apply_instance, }

noncomputable instance (A : finset 𝒩) (t : Tt T) (y : X 𝒩) : decidable_rel (r' ℋ ℰ A t y) :=
by { delta r', apply_instance, }

variables {ℋ} {ℰ}

lemma r_iff' {t : Tt T} {y : X 𝒩} (A : finset 𝒩) :
  ∀ (B C : 𝒫 A), C < B → (r ℋ ℰ t y ↑C ↑B ↔ r' ℋ ℰ A t y C B) :=
fun B C hlt, by refl

lemma r_iff_ (A : finset 𝒩) {t : Tt T} {y : X 𝒩} :
  ∀ (B C : 𝒫 A), C < B → (r ℋ ℰ t y ↑C ↑B ↔ r_ ℋ ℰ (fun D _, φ ℋ ℰ D) t y C B) :=
begin
  rintros ⟨B, hB⟩ ⟨C, hC⟩ hlt,
  split,
  { intro hr,
    use lt_of_lt_of_le hlt hB,
    rwa [u_, ←v_eq], },
  { rintros ⟨hC, hr_⟩,
    rwa [u_, ←v_eq] at hr_, },
end

lemma φ_eq {t : Tt T} {y : X 𝒩} (A : finset 𝒩) :
  φ ℋ ℰ A t y = si.φ (r' ℋ ℰ A t y) :=
begin
  conv_lhs
  { rw [φ, finset.strong_induction_eq, ←φ],
    change si.φ (r_ ℋ ℰ (fun B < A, φ ℋ ℰ B) t y), },
  rw [si.φ, si.φ],
  congr' 2,
  ext C,
  rw ←q_iff (r_iff_ A),
  rw q_iff (r_iff' A),
end

lemma mem_U_of_q {A : finset 𝒩} {t : Tt T} {y : X 𝒩} : q (r ℋ ℰ t y) A → y ∈ U ℋ ℰ A t :=
begin
  intro hq,
  rw [U, V, φ, finset.strong_induction_eq, ←φ],
  apply si.le_φ_of_q (r_iff_ A) ⟨A, refl _⟩,
  exact hq,
  apply_instance,
end

lemma φ_mono {A B : finset 𝒩} : B ≤ A → ∀ t y, (φ ℋ ℰ B t y : finset 𝒩) ≤ φ ℋ ℰ A t y :=
begin
  intros hB t y,
  conv_lhs { rw [φ, finset.strong_induction_eq, ←φ], },
  conv_rhs { rw [φ, finset.strong_induction_eq, ←φ], },
  apply si.φ_mono (r_iff_ A) (r_iff_ B) hB,
  apply_instance,
end
