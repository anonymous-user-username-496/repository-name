theory Scientific_Method_Audit
  imports "HOL-Probability.Probability_Measure"
begin

text \<open>
  Scientific induction using observed frequencies.

  The observation history is summarized by:
    occurrences     = number of times the phenomenon occurred
    nonoccurrences = number of times it did not occur

  The predictive model is Bernoulli sampling with a uniform
  Beta(1,1) prior. Its posterior predictive probability after
  observing the history is (occurrences + 1) /
  (occurrences + nonoccurrences + 2).

  "Happened too many times" is defined from the observations,
  not from the conclusion that the phenomenon is likely.
\<close>

definition happened_too_many_times ::
  "nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "happened_too_many_times occurrences nonoccurrences
    \<longleftrightarrow> nonoccurrences < occurrences"

definition posterior_predictive_probability ::
  "nat \<Rightarrow> nat \<Rightarrow> real"
where
  "posterior_predictive_probability occurrences nonoccurrences =
    (real occurrences + 1) /
    (real occurrences + real nonoccurrences + 2)"

definition likely_next ::
  "nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "likely_next occurrences nonoccurrences
    \<longleftrightarrow>
      1 / 2 <
        posterior_predictive_probability occurrences nonoccurrences"

theorem scientific_induction:
  assumes "happened_too_many_times occurrences nonoccurrences"
  shows "likely_next occurrences nonoccurrences"
proof -
  have frequency:
    "real nonoccurrences < real occurrences"
    using assms
    unfolding happened_too_many_times_def
    by simp

  have denominator_positive:
    "0 < real occurrences + real nonoccurrences + 2"
    by positivity

  have denominator_bound:
    "real occurrences + real nonoccurrences + 2
      < 2 * (real occurrences + 1)"
    using frequency
    by linarith

  have half_denominator_bound:
    "1 / 2 *
       (real occurrences + real nonoccurrences + 2)
      < real occurrences + 1"
    using denominator_bound
    by linarith

  have predictive_probability_bound:
    "1 / 2 <
      (real occurrences + 1) /
      (real occurrences + real nonoccurrences + 2)"
    using denominator_positive half_denominator_bound
    by (simp add: pos_less_divide_eq)

  show ?thesis
    unfolding likely_next_def posterior_predictive_probability_def
    using predictive_probability_bound
    by simp
qed

end
