import finset.basic
import analysis.normed_space.inner_product

def Tt (T : with_top ℝ) : set ℝ := {t : ℝ | 0 ≤ t ∧ (t : with_top ℝ) < T}
def Tτ {T : with_top ℝ} (t : Tt T) : set ℝ := {τ : ℝ | t.1 < τ ∧ (τ : with_top ℝ) ≤ T}

def X (𝒩 : Type) := 𝒩 → ℝ
instance (𝒩 : Type) : has_coe ℝ (X 𝒩) := ⟨λ r i, r⟩

def debt_fn (𝒩 : Type) (T : with_top ℝ) := Π (t : Tt T), X 𝒩 → 𝒩 → Tτ t → ℝ

variables {𝒩 : Type} [fintype 𝒩] [decidable_eq 𝒩] [inner_product_space ℝ (X 𝒩)] {T : with_top ℝ}

instance : has_subset (Tt T → set (X 𝒩)) := ⟨λ V₁ V₂, (∀ t, V₁ t ⊆ V₂ t)⟩

instance : has_zero (debt_fn 𝒩 T) := pi.has_zero
instance : partial_order (debt_fn 𝒩 T) := pi.partial_order

def continuous_wrt_assets {α : Tt T → Type*} [∀ t, topological_space (α t)]
  (v : Π (t : Tt T), X 𝒩 → α t) : Prop :=
∀ t, continuous (v t)

def continuous_off_wrt_assets {α : Tt T → Type*} [∀ t, topological_space (α t)]
  {V : Tt T → set (X 𝒩)} (v' : Π t y, y ∉ V t → α t) : Prop :=
∀ t, continuous (λ y : (V t)ᶜ, v' t y y.prop)

section
variables (𝒩) (T)

structure well_behaved_soln :=
(ℋ : Π {V : Tt T → set (X 𝒩)} (v' : Π t y, y ∉ V t → Tτ t → ℝ), (Π (t : Tt T), X 𝒩 → Tτ t → ℝ))
(matches_on_complement {V : Tt T → set (X 𝒩)} (v' : Π t y, y ∉ V t → Tτ t → ℝ) :
  ∀ t y h, ℋ v' t y = v' t y h)
(positivity_preserving {V : Tt T → set (X 𝒩)} (v' : Π t y, y ∉ V t → Tτ t → ℝ) :
  (∀ t y h, 0 ≤ v' t y h) → 0 ≤ ℋ v')
(continuity_preserving {V : Tt T → set (X 𝒩)} (v' : Π t y, y ∉ V t → Tτ t → ℝ) :
  continuous_off_wrt_assets v' → continuous_wrt_assets (ℋ v'))
(translation_invariant {V : Tt T → set (X 𝒩)} (v' : Π t y, y ∉ V t → Tτ t → ℝ) :
  ∀ η t y, ℋ v' t (y + η) = ℋ (λ s x (h : x + η ∉ V s), v' s (x + η) h) t y)
(compatible_on_subsets {V V' : Tt T → set (X 𝒩)} {v' : Π t y, y ∉ V t → Tτ t → ℝ} :
  V' ⊆ V → ℋ v' = ℋ (λ t y (h : y ∉ V' t), ℋ v' t y))
(mono_wrt_val_on_compl {V : Tt T → set (X 𝒩)} {v₁ v₂ : Π t y, y ∉ V t → Tτ t → ℝ} :
  (∀ t y h, v₁ t y h ≤ v₂ t y h) → ℋ v₁ ≤ ℋ v₂)

end

instance : has_coe_to_fun (well_behaved_soln 𝒩 T) :=
{ F := λ _, Π {V : Tt T → set (X 𝒩)} (v' : Π t y, y ∉ V t → Tτ t → ℝ), (Π t, X 𝒩 → Tτ t → ℝ),
  coe := well_behaved_soln.ℋ }

variable (ℋ : well_behaved_soln 𝒩 T)

instance : has_coe (finset 𝒩) (Tt T → X 𝒩 → finset 𝒩) := ⟨λ B t y, B⟩

def V (ψ : finset 𝒩 → Tt T → X 𝒩 → finset 𝒩) (B : finset 𝒩) : Tt T → set (X 𝒩) :=
λ t y, ψ B t y = B

def v_mk {B : finset 𝒩} {ψB : Tt T → X 𝒩 → finset 𝒩} (hψ : ψB ≤ B) :
  (Π C < B, debt_fn 𝒩 T) → debt_fn 𝒩 T :=
λ v t y i, if i ∈ B then ℋ (λ s x h, v (ψB s x) (lt_of_le_of_ne (hψ s x) h) s x i) t y else 0

def v {ψ : finset 𝒩 → Tt T → X 𝒩 → finset 𝒩} (hψ : ∀ B, ψ B ≤ B) : finset 𝒩 → debt_fn 𝒩 T :=
finset.strong_induction (λ B, v_mk ℋ (hψ B))
