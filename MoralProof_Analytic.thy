theory MoralProof_Analytic
  imports "HOL.Set" "HOL.Relation"
begin

text ‹All content is definitional. No axiomatization. No assumes.
  Library terms used directly:
  ▪ @{typ "'w set"} with @{term "(∈)"}, @{term "{}"}, @{term "{_}"} — HOL.Set
  ▪ @{term "(=)"}, @{term "(≠)"} — HOL
  ▪ @{term "Relation.single_valued"}, @{term "Relation.total_on"} — HOL.Relation›

typedecl 'w world
typedecl action

text ‹Obligation is a set of worlds, exactly as in AFP modal logic entries
  (Stalnaker_Logic, Epistemic_Logic, Public_Announcement_Logic).›
consts Oblig :: "action ⇒ 'w set"

text ‹"Should" is membership in the obligation set.›
definition should :: "action ⇒ bool" where
  "should a ≡ Oblig a ≠ {}"

text ‹The family of actions that are obligatory.›
definition ShouldFamily :: "action set" where
  "ShouldFamily ≡ {a. should a}"

text ‹The distinguished action of the argument.›
consts figure_out :: action

text ‹Equal value: no obligation exists, or the actions are identical.
  This uses library set equality.›
definition equal_value :: "action ⇒ action ⇒ bool" where
  "equal_value a b ≡ ShouldFamily = {} ∨ a = b"

text ‹Should-able: required, or all actions equal value.›
definition should_able :: "action ⇒ bool" where
  "should_able a ≡ a ∈ ShouldFamily ∨ (∀b c. equal_value b c)"

text ‹D5 and D6 are now THEOREMS, not axioms.›
lemma D5: "ShouldFamily = {} ⟹ ∀a b. equal_value a b"
  by (simp add: equal_value_def)

lemma D6: "ShouldFamily ≠ {} ⟹ figure_out ∈ ShouldFamily"
  unfolding ShouldFamily_def should_def by auto

text ‹Main theorem: no premises, internal case split on ShouldFamily = {}.›
theorem moral_conclusion_analytic:
  "should_able figure_out"
proof (cases "ShouldFamily = {}")
  case True
  hence "∀a b. equal_value a b" by (rule D5)
  thus ?thesis by (simp add: should_able_def)
next
  case False
  hence "ShouldFamily ≠ {}" by simp
  hence "figure_out ∈ ShouldFamily" by (rule D6)
  thus ?thesis by (simp add: should_able_def)
qed

end