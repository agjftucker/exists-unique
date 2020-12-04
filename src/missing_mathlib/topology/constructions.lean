import topology.constructions

noncomputable theory

open topological_space set filter
open_locale classical topological_space filter

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

section pi
variables {ι : Type*} {π : ι → Type*}

lemma continuous_iff_continuous_forall [topological_space α] [∀ i, topological_space (π i)]
  {f : α → ∀ i, π i} : continuous f ↔ ∀ i, continuous (fun y, f y i) :=
iff.intro (fun h i, continuous.comp (continuous_apply i) h) continuous_pi

end pi