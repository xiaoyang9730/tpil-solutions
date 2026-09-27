-- ## 4.6 Exercises

section q1

-- Prove these equivalences

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
    (λ h : (x : α) → p x ∧ q x => ⟨λ x : α => (h x).left, λ x : α => (h x).right⟩)
    (λ h : (∀ x, p x) ∧ (∀ x, q x) => λ x : α => ⟨h.left x, h.right x⟩)

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  λ h₀ : ∀ x, p x → q x => λ h₁ : ∀ x, p x => λ (x : α) => h₀ x (h₁ x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  λ h₀ : (∀ x, p x) ∨ (∀ x, q x) =>
    λ (x : α) =>
      Or.elim h₀
        (λ hp : ∀ x, p x => Or.inl (hp x))
        (λ hq : ∀ x, q x => Or.inr (hq x))

-- You should also try to understand why the reverse implication is not derivable in the last example.

end q1

section q2

-- It is often possible to bring a component of a formula outside a universal quantifier, when it does not depend on the quantified variable.
-- Try proving these (one direction of the second of these requires *classical logic*)

open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ _x : α, r) ↔ r) :=
  λ x : α =>
    Iff.intro
      (λ h : ∀ _x : α, r => h x)
      (λ h : r => λ _ => h)

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
    (λ h : ∀ x, p x ∨ r => -- classical logic
      byCases
        (λ hr : r => Or.inr hr)
        (λ hnr : ¬ r => Or.inl
          λ (x : α) => (h x).elim
            (λ hp : p x => hp)
            (λ hr => absurd hr hnr)))
    (λ h : (∀ x, p x) ∨ r =>
      λ x : α => h.elim
        (λ hp : ∀ x, p x => Or.inl (hp x))
        (λ hr : r => Or.inr hr))

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
    (λ h : ∀ x, r → p x =>
      λ hr : r => λ x : α => h x hr)
    (λ h : r → ∀ x, p x =>
      λ x : α => λ hr : r => h hr x)

end q2

section q3

-- Consider the "barber paradox", that is, the claim that in a certain town there is a (male) barber that shaves all and only the men who do not shave themselves.
-- Prove that this is a contradiction

open Classical

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := -- classical logic
  (em (shaves barber barber)).elim
    (λ hp => absurd hp ((h barber).mp hp))
    (λ hnp => absurd ((h barber).mpr hnp) hnp)

end q3

section q4

-- Remember that, without any parameters, an expression of type Prop is just an assertion.
-- Fill in the definitions of prime and Fermat_prime below, and construct each of the given assertions.

-- def even (n : Nat) : Prop := sorry

-- def prime (n : Nat) : Prop := sorry

-- def infinitely_many_primes : Prop := sorry

-- def Fermat_prime (n : Nat) : Prop := sorry

-- def infinitely_many_Fermat_primes : Prop := sorry

-- def goldbach_conjecture : Prop := sorry

-- def Goldbach's_weak_conjecture : Prop := sorry

-- def Fermat's_last_theorem : Prop := sorry

end q4
