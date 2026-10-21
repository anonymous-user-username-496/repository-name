theory Scientific_Method_Audit
imports "HOL-Probability.Probability_Measure"
begin

context prob_space
begin

definition likely :: "'a set ⇒ bool" where
  "likely A ⟷ 1 / 2 < prob A"

text ‹
  If the event's probability is greater than one half,
  it is likely according to this definition.
›

lemma probability_implies_likely:
  assumes "1 / 2 < prob A"
  shows "likely A"
  using assms unfolding likely_def .

text ‹
  If the probability of the next occurrence is the same
  as the probability inferred from the past, then a past
  inference of probability greater than one half implies
  the next occurrence is likely.
›

lemma repeated_occurrence_inference:
  assumes inferred_probability: "1 / 2 < p"
    and next_probability: "prob B = p"
  shows "likely B"
  using inferred_probability next_probability
  unfolding likely_def
  by simp

end

end
