-- ## 3.6. Examples of Propositional Validities

variable (p q : Prop)

-- Other properties:

-- 10. ¬p ∨ ¬q → ¬(p ∧ q)
example : ¬p ∨ ¬q → ¬(p ∧ q) :=
    fun h₀ : ¬p ∨ ¬q =>
        fun h₁ : p ∧ q =>
            Or.elim h₀
                (fun hnp : ¬p => show False from hnp h₁.left)
                (fun hnq : ¬q => show False from hnq h₁.right)
