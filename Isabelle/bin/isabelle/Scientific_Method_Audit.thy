theory Scientific_Method_Audit
  imports "HOL-Probability.Probability_Measure"
begin

context prob_space
begin

definition likely where
  "likely A = (prob A > 1 / 2)"

definition not_likely where
  "not_likely A = (prob A <= 1 / 2)"

lemma probability_value_unique:
  assumes "prob A = p"
      and "prob A = q"
  shows "p = q"
  using assms by simp

lemma incompatible_probability_values:
  assumes "prob A = p"
      and "prob A = q"
      and "p ~= q"
  shows False
  using assms by simp

lemma eliminate_not_likely:
  assumes cases: "likely A | not_likely A"
      and incompatible:
        "not_likely A --> False"
  shows "likely A"
  using cases incompatible by blast

end

end
