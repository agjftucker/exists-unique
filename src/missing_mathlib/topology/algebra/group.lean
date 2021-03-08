import topology.algebra.group

open classical set filter topological_space function
open_locale classical topological_space filter

universes u v w x
variables {α : Type u} {β : Type v} {G : Type w} {H : Type x}

section topological_group

variables [topological_space G] [group G] [topological_group G]

variables [topological_space α] {f : α → G} {s : set α} {x : α}

instance Pi.topological_add_group {C : β → Type*}
    [Π b, topological_space (C b)] [Π b, add_group (C b)] [Π b, topological_add_group (C b)] :
  topological_add_group (Π b, C b) :=
{ continuous_add := continuous_pi (fun i, continuous.add
    ((continuous_apply i).comp continuous_fst) ((continuous_apply i).comp continuous_snd)),
  continuous_neg := continuous_pi (fun i, continuous.neg (continuous_apply i)) }

end topological_group