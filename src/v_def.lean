import analysis.normed_space.inner_product
import missing_mathlib.data.finset.basic

local prefix `𝒫`:100 := λ {α : Type} (s : finset α), {t // t ≤ s}

def Tt (T : with_top ℝ) : set ℝ := {t : ℝ | 0 ≤ t ∧ (t : with_top ℝ) < T}
def Tτ {T : with_top ℝ} (t : Tt T) : set ℝ := {τ : ℝ | t.1 < τ ∧ (τ : with_top ℝ) ≤ T}

def X (𝒩 : Type) := 𝒩 → ℝ

def debt_fn (𝒩 : Type) (T : with_top ℝ) := ∀ (t : Tt T), X 𝒩 → 𝒩 → Tτ t → ℝ

variables {𝒩 : Type} [decidable_eq 𝒩] {T : with_top ℝ}

instance : has_coe ℝ (X 𝒩) := ⟨fun r i, r⟩
instance : has_subset (Tt T → set (X 𝒩)) := ⟨fun V₁ V₂, (∀ t, V₁ t ⊆ V₂ t)⟩

instance : add_comm_group (X 𝒩) := pi.add_comm_group
noncomputable instance : topological_space (X 𝒩) := Pi.topological_space

instance : has_zero (debt_fn 𝒩 T) := pi.has_zero
noncomputable instance : semilattice_sup (debt_fn 𝒩 T) := pi.semilattice_sup

def continuous_wrt_assets {α : Tt T → Type*} [∀ t, topological_space (α t)]
  (v : ∀ (t : Tt T), X 𝒩 → α t) : Prop :=
∀ t, continuous (v t)

def continuous_wrt_assets_on_compl {α : Tt T → Type*} [∀ t, topological_space (α t)]
  {V : Tt T → set (X 𝒩)} (v' : ∀ t y, y ∉ V t → α t) : Prop :=
∀ t, continuous (fun y : (V t)ᶜ, v' t y y.prop)

section
variables (𝒩) (T)

structure well_behaved_soln :=
(ℋ : ∀ {V : Tt T → set (X 𝒩)} (v' : ∀ t y, y ∉ V t → Tτ t → ℝ), (∀ (t : Tt T), X 𝒩 → Tτ t → ℝ))
(matching_on_complement {V : Tt T → set (X 𝒩)} (v' : ∀ t y, y ∉ V t → Tτ t → ℝ) :
  ∀ t y h, ℋ v' t y = v' t y h)
(positivity_preserving {V : Tt T → set (X 𝒩)} (v' : ∀ t y, y ∉ V t → Tτ t → ℝ) :
  (∀ t y h, 0 ≤ v' t y h) → 0 ≤ ℋ v')
(continuity_preserving {V : Tt T → set (X 𝒩)} (v' : ∀ t y, y ∉ V t → Tτ t → ℝ) :
  continuous_wrt_assets_on_compl v' → continuous_wrt_assets (ℋ v'))
(translation_invariant {V : Tt T → set (X 𝒩)} (v' : ∀ t y, y ∉ V t → Tτ t → ℝ) :
  ∀ η t y, ℋ v' t (y + η) = ℋ (fun s x (h : x + η ∉ V s), v' s (x + η) h) t y)
(compatible_on_subsets {V V' : Tt T → set (X 𝒩)} {v' : ∀ t y, y ∉ V t → Tτ t → ℝ} :
  V' ⊆ V → ℋ v' = ℋ (fun t y (h : y ∉ V' t), ℋ v' t y))
(mono_wrt_val_on_compl {V : Tt T → set (X 𝒩)} {v₁ v₂ : ∀ t y, y ∉ V t → Tτ t → ℝ} :
  (∀ t y h, v₁ t y h ≤ v₂ t y h) → ℋ v₁ ≤ ℋ v₂)

end

instance : has_coe_to_fun (well_behaved_soln 𝒩 T) :=
{ F := fun _, ∀ {V : Tt T → set (X 𝒩)} (v' : ∀ t y, y ∉ V t → Tτ t → ℝ), (∀ t, X 𝒩 → Tτ t → ℝ),
  coe := well_behaved_soln.ℋ }

variable (ℋ : well_behaved_soln 𝒩 T)

def V (ψ : ∀ (B : finset 𝒩), Tt T → X 𝒩 → 𝒫 B) (A : finset 𝒩) : Tt T → set (X 𝒩) :=
fun t y, A ≤ ψ A t y

instance (ψ : ∀ B, Tt T → X 𝒩 → 𝒫 B) (A : finset 𝒩) (t : Tt T) : ∀ y, decidable (y ∈ V ψ A t) :=
by { delta V, apply_instance, }

def v_mk {B : finset 𝒩} (ψB : Tt T → X 𝒩 → 𝒫 B) :
  (∀ C < B, debt_fn 𝒩 T) → debt_fn 𝒩 T :=
fun υ t y i, if i ∈ B then ℋ (fun s x h, υ (ψB s x) ⟨(ψB s x).prop, h⟩ s x i) t y else 0

def v (ψ : ∀ (B : finset 𝒩), Tt T → X 𝒩 → 𝒫 B) : finset 𝒩 → debt_fn 𝒩 T :=
finset.strong_induction (fun B, v_mk ℋ (ψ B))
