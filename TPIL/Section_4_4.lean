-- ## 4.4 The Existential Quantifier

-- What follows are some common identities involving the existential quantifier.
-- In the exercises below, we encourage you to prove as many as you can.
-- We also leave it to you to determine which are nonconstructive, and hence
-- require some form of *classical reasoning*.

open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ _x : α, r) → r :=
  λ ⟨(_t : α), (hr : r)⟩ => hr

example (a : α) : r → (∃ _x : α, r) :=
  λ (hr : r) => ⟨a, hr⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
    (λ ⟨t, ⟨hp, hr⟩⟩ => ⟨⟨t, hp⟩, hr⟩)
    (λ ⟨⟨t, hp⟩, hr⟩ => ⟨t, ⟨hp, hr⟩⟩)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (λ ⟨t, h⟩ => h.elim
      (λ hp => Or.inl ⟨t, hp⟩)
      (λ hq => Or.inr ⟨t, hq⟩))
    (λ h => h.elim
      (λ ⟨t, hp⟩ => ⟨t, Or.inl hp⟩)
      (λ ⟨t, hq⟩ => ⟨t, Or.inr hq⟩))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
    (λ (h₀ : (x : α) → p x) => λ ⟨t, h₁⟩ => h₁ (h₀ t))
    (λ h₀ => λ (x : α) => -- classical reasoning
      byCases
        (λ (hp : p x) => hp)
        (λ (hnp : ¬ p x) => absurd ⟨x, hnp⟩ h₀))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro
    (λ ⟨x, hp⟩ => λ (h : ∀ x, ¬ p x) => absurd hp (h x))
    (λ h : ¬ ∀ x, ¬ p x => -- classical reasoning
      byContradiction
        (λ h₁ : ¬ ∃ x, p x =>
          have h₂ : ∀ x, ¬ p x :=
            λ (x : α) => λ (hp : p x) => absurd ⟨x, hp⟩ h₁
          show False from h h₂))

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
    (λ h : ¬ ∃ x, p x => λ (x : α) => λ (hp : p x) => h (⟨x, hp⟩))
    (λ h : ∀ x, ¬ p x => λ (⟨hx, hp⟩ : ∃ _x, p _x) => h hx hp)

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  Iff.intro
    (λ h : ¬ ∀ x, p x => -- classical reasoning
      byContradiction
        (λ h₁ : ¬ ∃ x, ¬ p x =>
          have h₂ : ∀ x, p x :=
            λ (x : α) =>
              byContradiction
                (λ h₃ : ¬ p x =>
                  show False from h₁ ⟨x, h₃⟩)
          show False from h h₂))
    (λ ⟨t, hnp⟩ => λ (hp : ∀ x, p x) => show False from hnp (hp t))

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  Iff.intro
    (λ (h : ∀ x, p x → r) => λ ⟨t, hp⟩ => (h t) hp)
    (λ (h : (∃ x, p x) → r) => λ (x : α) => λ (hp : p x) => h ⟨x, hp⟩)

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (λ ⟨t, h₀⟩ => λ (h₁ : (x : α) → p x) => h₀ (h₁ t))
    (λ (h₀ : (∀ x, p x) → r) => -- classical reasoning
      byCases
        (λ (h₁ : ∀ x, p x) => ⟨a, λ _ => h₀ h₁⟩)
        (λ (h₁ : ¬ ∀ x, p x) =>
          byContradiction
            (λ h₂ : ¬ ∃ x, p x → r =>
              have h₃ : ∀ x, p x :=
                λ (x : α) =>
                  byContradiction
                    (λ h₄ : ¬ p x =>
                      have h₅ : ∃ x, p x → r :=
                        ⟨x, λ (h₆ : p x) => absurd h₆ h₄⟩
                      show False from h₂ h₅)
              show False from h₁ h₃)))

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  Iff.intro
    (λ ⟨t, h⟩ => λ r => ⟨t, h r⟩)
    (λ h₀ : r → ∃ x, p x => -- classical reasoning
      byCases
        (λ hr : r =>
          match (h₀ hr) with
          | ⟨t, hp⟩ => ⟨t, λ _ => hp⟩)
        (λ hnr : ¬ r =>
          ⟨a, λ hr => absurd hr hnr⟩))
