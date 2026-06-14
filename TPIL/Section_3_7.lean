-- ## 3.7. Exercises

-- Prove the following identities, replacing the sorry placeholders with actual proofs.

variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
    Iff.intro
        (fun hpq : p ∧ q =>
            have hp : p := And.left hpq
            have hq : q := And.right hpq
            show q ∧ p from And.intro hq hp)
        (fun hqp : q ∧ p =>
            have hq : q := And.left hqp
            have hp : p := And.right hqp
            show p ∧ q from And.intro hp hq)

example : p ∨ q ↔ q ∨ p :=
    Iff.intro
        (fun hpq : p ∨ q =>
            Or.elim hpq
                (fun hp: p => Or.intro_right q hp)
                (fun hq: q => Or.intro_left p hq))
        (fun hqp : q ∨ p =>
            Or.elim hqp
                (fun hq: q => Or.intro_right p hq)
                (fun hp: p => Or.intro_left q hp))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
    Iff.intro
        (fun hpqr : (p ∧ q) ∧ r =>
            have hpq : p ∧ q := And.left  hpqr
            have hp  : p      := And.left  hpq
            have hq  : q      := And.right hpq
            have hr  : r      := And.right hpqr
            show p ∧ (q ∧ r) from ⟨hp, ⟨hq, hr⟩⟩)
        (fun hpqr : p ∧ (q ∧ r) =>
            have hp  : p      := And.left  hpqr
            have hqr : q ∧ r := And.right hpqr
            have hq  : q      := And.left  hqr
            have hr  : r      := And.right hqr
            show (p ∧ q) ∧ r from ⟨⟨hp, hq⟩, hr⟩)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
    Iff.intro
        (fun hpqr : (p ∨ q) ∨ r =>
            Or.elim hpqr
                (fun hpq : p ∨ q =>
                    Or.elim hpq
                        (fun hp : p =>
                            show p ∨ (q ∨ r) from Or.inl hp)
                        (fun hq : q =>
                            show p ∨ (q ∨ r) from Or.inr (Or.inl hq)))
                (fun hr : r =>
                    show p ∨ (q ∨ r) from Or.inr (Or.inr hr)))
        (fun hpqr : p ∨ (q ∨ r) =>
            Or.elim hpqr
                (fun hp : p =>
                    show (p ∨ q) ∨ r from Or.inl (Or.inl hp))
                (fun hqr : q ∨ r =>
                    Or.elim hqr
                        (fun hq : q =>
                            show (p ∨ q) ∨ r from Or.inl (Or.inr hq))
                        (fun hr : r =>
                            show (p ∨ q) ∨ r from Or.inr hr)))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
    Iff.intro
        (fun h : p ∧ (q ∨ r) =>
            have hp : p := h.left
            have hqr : q ∨ r := h.right
            show (p ∧ q) ∨ (p ∧ r) from Or.elim hqr
                (fun hq : q => Or.inl ⟨hp, hq⟩)
                (fun hr : r => Or.inr ⟨hp, hr⟩))
        (fun h : (p ∧ q) ∨ (p ∧ r) =>
            show p ∧ (q ∨ r) from Or.elim h
                (fun hpq : p ∧ q => ⟨hpq.left, Or.inl hpq.right⟩)
                (fun hpr : p ∧ r => ⟨hpr.left, Or.inr hpr.right⟩))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
    Iff.intro
        (fun h : p ∨ (q ∧ r) =>
            Or.elim h
                (fun hp : p => ⟨Or.inl hp, Or.inl hp⟩)
                (fun hqr : q ∧ r => ⟨Or.inr hqr.left, Or.inr hqr.right⟩))
        (fun h : (p ∨ q) ∧ (p ∨ r) =>
            have hpq : p ∨ q := h.left
            have hpr : p ∨ r := h.right
            Or.elim hpq
                (fun hp : p => Or.inl hp)
                (fun hq : q =>
                    Or.elim hpr
                        (fun hp : p => Or.inl hp) -- unreachable
                        (fun hr : r => Or.inr ⟨hq, hr⟩)))

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
    Iff.intro
        (fun h₀ : p → (q → r) =>
            fun h₁ : p ∧ q => h₀ h₁.left h₁.right)
        (fun h : p ∧ q → r =>
            fun hp : p => fun hq : q => h ⟨hp, hq⟩)

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
    Iff.intro
        (fun h : (p ∨ q) → r =>
            And.intro
                (fun hp : p => h (Or.inl hp))
                (fun hq : q => h (Or.inr hq)))
        (fun h : (p → r) ∧ (q → r) =>
            fun hpq : p ∨ q =>
                Or.elim hpq
                    (fun hp : p => h.left  hp)
                    (fun hq : q => h.right hq))

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
    Iff.intro
        (fun h : ¬(p ∨ q) =>
            have hnp : ¬p := fun hp : p => show False from h (Or.inl hp)
            have hnq : ¬q := fun hq : q => show False from h (Or.inr hq)
            ⟨hnp, hnq⟩)
        (fun h : ¬p ∧ ¬q =>
            fun hpq : p ∨ q => show False from
                Or.elim hpq
                    (fun hp : p => h.left  hp)
                    (fun hq : q => h.right hq))

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
    fun h : ¬p ∨ ¬q =>
        fun hpq : p ∧ q => show False from
            have hp : p := hpq.left
            have hq : q := hpq.right
            Or.elim h
                (fun hnp : ¬p => hnp hp)
                (fun hnq : ¬q => hnq hq)

example : ¬(p ∧ ¬p) :=
    fun h : p ∧ ¬p => show False from
        h.right h.left

example : p ∧ ¬q → ¬(p → q) :=
    fun h₀ : p ∧ ¬q =>
        fun h₁ : p → q => show False from
            h₀.right (h₁ h₀.left)

example : ¬p → (p → q) :=
    fun hnp : ¬p =>
        fun hp : p => absurd hp hnp

example : (¬p ∨ q) → (p → q) :=
    fun h : ¬p ∨ q =>
        fun hp : p =>
            Or.elim h
                (fun hnp : ¬p => absurd hp hnp)
                (fun hq : q => hq)

example : p ∨ False ↔ p :=
    Iff.intro
        (fun h : p ∨ False =>
            Or.elim h
                (fun hp : p => hp)
                (False.elim))
        (fun hp : p => Or.inl hp)

example : p ∧ False ↔ False :=
    Iff.intro
        (fun h : p ∧ False => h.right)
        (False.elim)

example : (p → q) → (¬q → ¬p) :=
    fun hpq : p → q =>
        fun hnq : ¬q =>
            fun hp => show False from hnq (hpq hp)

-- Prove the following identities, replacing the sorry placeholders with actual proofs.
-- These require classical reasoning.

-- open Classical

-- variable (p q r : Prop)

-- example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := sorry
-- example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
-- example : ¬(p → q) → p ∧ ¬q := sorry
-- example : (p → q) → (¬p ∨ q) := sorry
-- example : (¬q → ¬p) → (p → q) := sorry
-- example : p ∨ ¬p := sorry
-- example : (((p → q) → p) → p) := sorry

-- Prove ¬(p ↔ ¬p) without using classical logic.
