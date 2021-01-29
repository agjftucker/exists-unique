import data.finset.lattice
import missing_mathlib.data.finset.fold

variables {α β γ : Type*}

namespace finset
open multiset order_dual

section sup
variables [semilattice_sup_bot α]

variables {s s₁ s₂ : finset β} {f : β → α}

@[simp] lemma sup_cons {b : β} (h : b ∉ s) : (cons b s h).sup f = f b ⊔ s.sup f :=
fold_cons h

end sup

section sup'
variables [semilattice_sup α]

theorem sup_of_mem {s : finset β} (f : β → α) {b : β} (h : b ∈ s) :
  ∃ a, @sup (with_bot α) β _ s (some ∘ f) = some a :=
(@le_sup (with_bot α) β _ s (some ∘ f) b h (f b) rfl).imp (fun b, Exists.fst)

theorem le_sup_of_mem {s : finset β} (f : β → α) {b : β} (h : b ∈ s) {a : α}
  (h₂ : @sup (with_bot α) β _ s (some ∘ f) = a) : f b ≤ a :=
begin
  rcases @le_sup (with_bot α) β _ s (some ∘ f) b h _ rfl with ⟨c, hb, ab⟩,
  cases h₂.symm.trans hb,
  assumption,
end

def sup' (s : finset β) (H : s.nonempty) (f : β → α) : α :=
option.get $ let ⟨k, hk⟩ := H in option.is_some_iff_exists.2 (sup_of_mem f hk)

theorem le_sup' {s : finset β} (f : β → α) {b : β} (H2 : b ∈ s) : f b ≤ s.sup' ⟨b, H2⟩ f :=
le_sup_of_mem f H2 $ option.get_mem _

theorem sup'_le {s : finset β} (H : s.nonempty) (f : β → α) (a : α) (H2 : ∀ b ∈ s, f b ≤ a) :
  s.sup' H f ≤ a :=
begin
  rw [←with_bot.some_le_some, sup', option.some_get],
  apply @sup_le (with_bot α) β _,
  intros b hb,
  rw with_bot.some_le_some,
  exact H2 b hb,
end

variables {s : finset β} (H : s.nonempty) (f : β → α)

@[simp] lemma coe_sup'_eq_sup : ((s.sup' H f : α) : with_bot α) = s.sup (coe ∘ f) :=
by { rw [sup', ←with_bot.some_eq_coe, option.some_get], refl }

lemma sup'_insert [decidable_eq β] {b : β} (h : (insert b s).nonempty) :
  (insert b s).sup' h f = f b ⊔ s.sup' H f :=
by { rw ←with_bot.coe_eq_coe, simp }

end sup'

section sup
variables {C : β → Type*} [∀ (b : β), semilattice_sup_bot (C b)]

protected lemma sup_apply (s : finset α) (f : α → ∀ (b : β), C b) (b : β) :
  s.sup f b = s.sup (fun a, f a b) :=
begin
  induction s using finset.induction' with c s hc ih,
  { refl, },
  { rw [sup_cons, sup_cons, sup_apply, ih], },
end

end sup

section sup'
variables [decidable_eq α] {C : β → Type*} [∀ (b : β), semilattice_sup (C b)]

lemma sup'_apply {s : finset α} (h : s.nonempty) (f : α → ∀ (b : β), C b) (b : β) :
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

section sup
variables [semilattice_sup_bot α]

lemma of_sup_of_forall {s : finset β} (f : β → α) {p : α → Prop} (h0 : p ⊥)
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

section sup'
variable [semilattice_sup α]

lemma of_sup'_of_forall {s : finset β} (hne : s.nonempty) (f : β → α) {p : α → Prop}
  (hp : ∀ (a₁ a₂ : α), p a₁ → p a₂ → p (a₁ ⊔ a₂)) (hs : ∀ b ∈ s, p (f b)) : p (s.sup' hne f) :=
begin
  cases hne with k hk,
  cases sup_of_mem f hk with m hm,
  have : s.sup' ⟨k, hk⟩ f = m,
  { dunfold sup',
    apply option.some_injective,
    rwa option.some_get, },
  rw this,
  let p' := @option.rec α (fun _, Prop) true p,
  change p' (some m),
  rw ←hm,
  refine of_sup_of_forall (some ∘ f) trivial _ hs,
  intros a₁ a₂ h₁ h₂,
  cases a₁,
  { rwa [with_bot.none_eq_bot, bot_sup_eq], },
  cases a₂,
  { rwa [with_bot.none_eq_bot, sup_bot_eq], },
  exact hp a₁ a₂ h₁ h₂,
end

end sup'

end finset
