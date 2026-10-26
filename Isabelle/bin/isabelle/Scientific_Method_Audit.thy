theory Scientific_Method_Audit
  imports "HOL-Probability.Probability_Measure"
begin

definition occurrence_count :: "bool list => nat" where
  "occurrence_count observations =
    length (filter id observations)"

definition nonoccurrence_count :: "bool list => nat" where
  "nonoccurrence_count observations =
    length (filter Not observations)"

definition happened_too_many_times :: "bool list => bool" where
  "happened_too_many_times observations =
    (nonoccurrence_count observations <
     occurrence_count observations)"

definition predicted_probability :: "bool list => real" where
  "predicted_probability observations =
    (real (occurrence_count observations) + 1) /
    (real (occurrence_count observations) +
     real (nonoccurrence_count observations) + 2)"

definition likely_next :: "bool list => bool" where
  "likely_next observations =
    (1 / 2 < predicted_probability observations)"

definition not_likely_next :: "bool list => bool" where
  "not_likely_next observations =
    (predicted_probability observations <= 1 / 2)"

lemma probability_has_one_value:
  fixes p q r :: real
  assumes "p = q"
      and "p = r"
  shows "q = r"
  using assms by simp

lemma likelihood_cases:
  "likely_next observations | not_likely_next observations"
  unfolding likely_next_def not_likely_next_def
  by auto

lemma likelihood_cases_exclusive:
  "~ (likely_next observations & not_likely_next observations)"
  unfolding likely_next_def not_likely_next_def
  by auto

lemma repeated_occurrences_exclude_not_likely:
  assumes repeated:
    "happened_too_many_times observations"
  shows "~ not_likely_next observations"
proof -
  let ?s = "real (occurrence_count observations)"
  let ?f = "real (nonoccurrence_count observations)"
  let ?d = "?s + ?f + 2"

  have frequency: "?f < ?s"
    using repeated
    unfolding happened_too_many_times_def
    by simp

  have nonnegative_s: "0 <= ?s"
    by simp

  have nonnegative_f: "0 <= ?f"
    by simp

  have positive_denominator: "0 < ?d"
    using nonnegative_s nonnegative_f
    by linarith

  have arithmetic_bound:
    "?s + ?f + 2 < 2 * (?s + 1)"
    using frequency
    by (simp add: algebra_simps)

  have half_bound:
    "(1 / 2 :: real) * ?d < ?s + 1"
    using arithmetic_bound
    by (simp add: field_simps)

  have prediction:
    "(1 / 2 :: real) < (?s + 1) / ?d"
    using positive_denominator half_bound
    by (simp add: pos_less_divide_eq)

  show ?thesis
    unfolding not_likely_next_def
      predicted_probability_def
    using prediction
    by simp
qed

theorem scientific_induction:
  assumes repeated:
    "happened_too_many_times observations"
  shows "likely_next observations"
proof (cases "likely_next observations")
  case True
  then show ?thesis .
next
  case False

  have excluded:
    "~ not_likely_next observations"
    using repeated
    by (rule repeated_occurrences_exclude_not_likely)

  have exhaustive:
    "likely_next observations | not_likely_next observations"
    by (rule likelihood_cases)

  show ?thesis
    using False excluded exhaustive
    by blast
qed

end
