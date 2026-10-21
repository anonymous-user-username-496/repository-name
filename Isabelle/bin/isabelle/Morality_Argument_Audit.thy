theory Morality_Argument_Audit
  imports Main
begin

text ‹
  A should is "known" when we know what we should do.
  The two cases are whether a should is known or not.
›

datatype knowledge_case =
    Known_Should
  | No_Known_Should

definition should_known :: "knowledge_case ⇒ bool" where
  "should_known c ⟷ c = Known_Should"

definition investigate_purpose :: "knowledge_case ⇒ bool" where
  "investigate_purpose c ⟷ c = No_Known_Should"

lemma cases_exhaustive:
  "c = Known_Should ∨ c = No_Known_Should"
  by (cases c) simp_all

lemma no_known_should_means_investigate:
  assumes "¬ should_known c"
  shows "investigate_purpose c"
  using assms
  unfolding should_known_def investigate_purpose_def
  by (cases c) simp_all

lemma investigate_when_should_unknown:
  assumes "c = No_Known_Should"
  shows "investigate_purpose c"
  using assms unfolding investigate_purpose_def by simp

theorem should_status_exhaustive:
  "(∃x. should_to_be_found x) ∨
   ¬ (∃x. should_to_be_found x)"
  by blast
end
