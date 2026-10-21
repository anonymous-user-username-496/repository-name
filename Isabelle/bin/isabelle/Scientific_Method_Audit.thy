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

text \<open>
  If the probability of the next occurrence is the same
  as the probability inferred from the past, then a past
  inference of probability greater than one half implies
  the next occurrence is likely.
\<close>

lemma repeated_occurrence_inference:
  assumes inferred_probability: "(1 / 2 :: real) < p"
    and next_probability: "prob B = p"
  shows "likely B"
proof -
  have next_probability_likely: "(1 / 2 :: real) < prob B"
    using inferred_probability next_probability
    by simp
  show "likely B"
    using next_probability_likely
    unfolding likely_def .
qed

end

end
