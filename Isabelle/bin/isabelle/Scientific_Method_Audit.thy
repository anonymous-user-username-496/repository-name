theory Scientific_Method_Audit
  imports "HOL-Probability.Probability_Measure"
begin

context prob_space
begin

definition likely :: "'a set \<Rightarrow> bool" where
  "likely A \<longleftrightarrow> (1 / 2 :: real) < prob A"

text \<open>
  If the event's probability is greater than one half,
  it is likely according to this definition.
\<close>

lemma probability_implies_likely:
  assumes "1 / 2 < prob A"
  shows "likely A"
  using assms
  unfolding likely_def
  by simp

lemma repeated_occurrence_inference:
  fixes A B :: "'a set"
  assumes inferred_probability: "1 / 2 < p"
    and next_probability: "prob B = p"
  shows "likely B"
  using inferred_probability next_probability
  unfolding likely_def
  by simp

end

end
