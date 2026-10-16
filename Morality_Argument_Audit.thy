theory Morality_Argument_Audit
  imports "CondNormReasHOL.DDLcube"
begin

theorem purpose_of_life_by_cases:
  fixes no_known_should should_to_be_found investigate :: σ
  shows
    "(
       (∀x y.
          no_known_should x ⟶ no_known_should y ⟶
          (x \<^bold>r y ∧ y \<^bold>r x))
       ∧
       (∃x. no_known_should x ∧ investigate x)
       ∧
       (∀x. should_to_be_found x ⟶ investigate x)
     )
     ⟶
     (
       (∃x. opt<no_known_should> x ∧ investigate x)
       ∧ P<investigate|no_known_should> aw
       ∧ (∀x. opt<should_to_be_found> x ⟶ investigate x)
       ∧ \<circle><investigate|should_to_be_found> aw
     )"
proof (intro impI)
  assume case_semantics:
    "(
       (∀x y.
          no_known_should x ⟶ no_known_should y ⟶
          (x \<^bold>r y ∧ y \<^bold>r x))
       ∧
       (∃x. no_known_should x ∧ investigate x)
       ∧
       (∀x. should_to_be_found x ⟶ investigate x)
     )"

  show ?thesis
  proof (cases "∃x. should_to_be_found x")
    case True
    with case_semantics show ?thesis by auto
  next
    case False
    with case_semantics show ?thesis by auto
  qed
qed

end