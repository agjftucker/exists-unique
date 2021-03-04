import data.finset.lattice
import missing_mathlib.data.finset.fold
import missing_mathlib.order.bounded_lattice

variables {α β γ : Type*}

namespace finset
open multiset order_dual

section sup
variables [semilattice_sup_bot α]

variables {s s₁ s₂ : finset β} {f : β → α}

@[simp] lemma sup_cons {b : β} (h : b ∉ s) : (cons b s h).sup f = f b ⊔ s.sup f :=
fold_cons h

lemma of_sup_of_forall {p : α → Prop} (h0 : p ⊥)
  (hp : ∀ (a₁ a₂ : α), p a₁ → p a₂ → p (a₁ ⊔ a₂)) (hs : ∀ b ∈ s, p (f b)) : p (s.sup f) :=
begin
  induction s using finset.induction' with c s hc ih,
  { exact h0, },
  { rw sup_cons,
    apply hp,
    { apply hs,
      rw mem_cons,
      exact or.inl rfl, },
    { apply ih,
      intros b hb,
      apply hs,
      rw mem_cons,
      exact or.inr hb, }, },
end

end sup

section inf
variables [semilattice_inf_top α]

variables {s s₁ s₂ : finset β} {f : β → α}

@[simp] lemma inf_cons {b : β} (h : b ∉ s) : (cons b s h).inf f = f b ⊓ s.inf f :=
@sup_cons (order_dual α) _ _ _ _ _ h

lemma of_inf_of_forall {p : α → Prop} (h0 : p ⊤)
  (hp : ∀ (a₁ a₂ : α), p a₁ → p a₂ → p (a₁ ⊓ a₂)) (hs : ∀ b ∈ s, p (f b)) : p (s.inf f) :=
@of_sup_of_forall (order_dual α) _ _ _ _ _ h0 hp hs

end inf

section sup'
variables [semilattice_sup α]

lemma sup_of_mem {s : finset β} (f : β → α) {b : β} (h : b ∈ s) :
  ∃ (a : α), @sup (with_bot α) _ _ s (coe ∘ f) = ↑a :=
(@le_sup (with_bot α) _ _ _ _ _ h (f b) rfl).imp (fun b, Exists.fst)

lemma le_sup_of_mem {s : finset β} (f : β → α) {b : β} (h₁ : b ∈ s) {a : α}
  (h₂ : @sup (with_bot α) _ _ s (coe ∘ f) = ↑a) : f b ≤ a :=
begin
  rcases @le_sup (with_bot α) _ _ _ _ _ h₁ (f b) rfl with ⟨c, hb, ab⟩,
  cases h₂.symm.trans hb,
  assumption,
end

def sup' (s : finset β) (H : s.nonempty) (f : β → α) : α :=
option.get $ let ⟨k, hk⟩ := H in option.is_some_iff_exists.2 (sup_of_mem f hk)

@[simp] lemma coe_sup'_eq_sup_coe {s : finset β} (H : s.nonempty) (f : β → α) :
  ((s.sup' H f : α) : with_bot α) = s.sup (coe ∘ f) :=
by rw [sup', ←with_bot.some_eq_coe, option.some_get]

lemma le_sup' {s : finset β} (f : β → α) {b : β} (H2 : b ∈ s) : f b ≤ s.sup' ⟨b, H2⟩ f :=
le_sup_of_mem f H2 $ option.get_mem _

lemma sup'_le {s : finset β} (H : s.nonempty) (f : β → α) {a : α} (H2 : ∀ b ∈ s, f b ≤ a) :
  s.sup' H f ≤ a :=
begin
  rw [←with_bot.coe_le_coe, coe_sup'_eq_sup_coe],
  apply @sup_le (with_bot α) β _,
  intros b hb,
  rw with_bot.coe_le_coe,
  exact H2 b hb,
end

variables {s : finset β} (H : s.nonempty) (f : β → α)

lemma sup'_cons {b : β} (hb : b ∉ s) :
  (cons b s hb).sup' (nonempty_cons hb) f = f b ⊔ s.sup' H f :=
by { rw ←with_bot.coe_eq_coe, simp }

lemma sup'_insert [decidable_eq β] {b : β} (h : (insert b s).nonempty) :
  (insert b s).sup' h f = f b ⊔ s.sup' H f :=
by { rw ←with_bot.coe_eq_coe, simp }

end sup'

section inf'
variable [semilattice_inf α]

lemma inf_of_mem {s : finset β} (f : β → α) {b : β} (h : b ∈ s) :
  ∃ (a : α), @inf (with_top α) _ _ s (coe ∘ f) = ↑a :=
@sup_of_mem (order_dual α) _ _ _ _ _ h

lemma inf_le_of_mem {s : finset β} (f : β → α) {b : β} (h₁ : b ∈ s) {a : α}
  (h₂ : @inf (with_top α) _ _ s (coe ∘ f) = ↑a) : a ≤ f b :=
@le_sup_of_mem (order_dual α) _ _ _ _ _ h₁ _ h₂

def inf' (s : finset β) (H : s.nonempty) (f : β → α) : α :=
@sup' (order_dual α) _ _ s H f

@[simp] lemma coe_inf'_eq_inf_coe {s : finset β} (H : s.nonempty) (f : β → α) :
  ((s.inf' H f : α) : with_top α) = s.inf (coe ∘ f) :=
@coe_sup'_eq_sup_coe (order_dual α) _ _ _ H f

end inf'

section sup
variables {C : β → Type*} [Π (b : β), semilattice_sup_bot (C b)]

protected lemma sup_apply (s : finset α) (f : α → Π (b : β), C b) (b : β) :
  s.sup f b = s.sup (fun a, f a b) :=
begin
  induction s using finset.induction' with c s hc ih,
  { refl, },
  { rw [sup_cons, sup_cons, sup_apply, ih], },
end

end sup

section inf
variables {C : β → Type*} [Π (b : β), semilattice_inf_top (C b)]

protected lemma inf_apply (s : finset α) (f : α → Π (b : β), C b) (b : β) :
  s.inf f b = s.inf (fun a, f a b) :=
@finset.sup_apply _ _ (fun b, order_dual (C b)) _ _ _ _

end inf

section sup'
variables [decidable_eq α] {C : β → Type*} [Π (b : β), semilattice_sup (C b)]

lemma sup'_apply {s : finset α} (h : s.nonempty) (f : α → Π (b : β), C b) (b : β) :
  s.sup' h f b = s.sup' h (fun a, f a b) :=
begin
  induction s using finset.induction_on with c s hc ih,
  { exfalso,
    exact not_nonempty_empty h, },
  { cases dec_em (s = ∅) with he hne,
    { subst he,
      refl, },
    { repeat { rw sup'_insert (nonempty_of_ne_empty hne), },
      rw [sup_apply, ih], }, },
end

end sup'

section inf'
variables [decidable_eq α] {C : β → Type*} [Π (b : β), semilattice_inf (C b)]

lemma inf'_apply {s : finset α} (h : s.nonempty) (f : α → Π (b : β), C b) (b : β) :
  s.inf' h f b = s.inf' h (fun a, f a b) :=
@sup'_apply _ _ _ (fun b, order_dual (C b)) _ _ _ _ _

end inf'

section sup'
variable [semilattice_sup α]

lemma of_sup'_of_forall {s : finset β} (hne : s.nonempty) {f : β → α} {p : α → Prop}
  (hp : ∀ (a₁ a₂ : α), p a₁ → p a₂ → p (a₁ ⊔ a₂)) (hs : ∀ b ∈ s, p (f b)) : p (s.sup' hne f) :=
begin
  cases hne with k hk,
  cases sup_of_mem f hk with m hm,
  rw show s.sup' ⟨k, hk⟩ f = m,
  { rwa [←with_bot.coe_eq_coe, coe_sup'_eq_sup_coe], },
  change @option.rec α (fun _, Prop) true p ↑m,
  rw ←hm,
  refine of_sup_of_forall trivial _ hs,
  intros a₁ a₂ h₁ h₂,
  cases a₁,
  { rwa [with_bot.none_eq_bot, bot_sup_eq], },
  cases a₂,
  { rwa [with_bot.none_eq_bot, sup_bot_eq], },
  exact hp a₁ a₂ h₁ h₂,
end

end sup'

section inf'
variable [semilattice_inf α]

lemma of_inf'_of_forall {s : finset β} (hne : s.nonempty) {f : β → α} {p : α → Prop}
  (hp : ∀ (a₁ a₂ : α), p a₁ → p a₂ → p (a₁ ⊓ a₂)) (hs : ∀ b ∈ s, p (f b)) : p (s.inf' hne f) :=
@of_sup'_of_forall (order_dual α) _ _ _ _ _ _ hp hs

end inf'

end finset
