theory Scientific_Method_Audit
  imports "HOL-Probability.Probability_Mass_Function"
begin

definition empirical_pmf :: "'a list ⇒ 'a pmf" where
  "empirical_pmf xs =
    (if xs = [] then return_pmf undefined
     else pmf_of_list
       (map (λx. (x, 1 / real (length xs))) xs))"

lemma sum_equal_weights:
  fixes xs :: "'a list" and c :: real
  shows
    "sum_list (map snd (map (λx. (x, c)) xs)) =
     real (length xs) * c"
  by (induction xs) (simp_all add: algebra_simps)

lemma weighted_occurrence_count:
  fixes xs :: "'a list" and a :: 'a and c :: real
  shows
    "sum_list
       (map snd
         (filter (λz. fst z = a)
           (map (λx. (x, c)) xs))) =
     real (count_list xs a) * c"
  by (induction xs) (simp_all add: algebra_simps)

lemma empirical_weights_well_formed:
  "xs ≠ [] ⟶
   pmf_of_list_wf
     (map (λx. (x, 1 / real (length xs))) xs)"
proof (cases "xs = []")
  case True
  then show ?thesis by simp
next
  case False
  have positive: "0 < real (length xs)"
    using False by simp
  show ?thesis
    using False positive
    unfolding pmf_of_list_wf_def
    by (auto simp: sum_equal_weights field_simps; positivity)
qed

lemma empirical_pmf_probability:
  "xs ≠ [] ⟶
   pmf (empirical_pmf xs) a =
     real (count_list xs a) / real (length xs)"
proof (cases "xs = []")
  case True
  then show ?thesis by simp
next
  case False
  let ?ws =
    "map (λx. (x, 1 / real (length xs))) xs"

  have wf: "pmf_of_list_wf ?ws"
    using empirical_weights_well_formed[of xs] False
    by blast

  have p:
    "pmf (pmf_of_list ?ws) a =
       sum_list (map snd
         (filter (λz. fst z = a) ?ws))"
    by (rule pmf_pmf_of_list[OF wf])

  have frequency:
    "sum_list (map snd
       (filter (λz. fst z = a) ?ws)) =
       real (count_list xs a) / real (length xs)"
    using weighted_occurrence_count
      [of xs a "1 / real (length xs)"] False
    by (simp add: field_simps)

  show ?thesis
    using False p frequency
    by (simp add: empirical_pmf_def)
qed

lemma majority_frequency_exceeds_half:
  fixes n k :: nat
  shows
    "n > 0 ⟶
     2 * k > n ⟶
     real k / real n > (1 / 2)"
proof (cases "n = 0")
  case True
  then show ?thesis by simp
next
  case False
  have denominator_positive: "0 < real n"
    using False by simp

  show ?thesis
  proof (cases "2 * k > n")
    case False
    then show ?thesis by simp
  next
    case True
    have half_less: "real n / 2 < real k"
      using True by linarith

    have quotient_less:
      "(real n / 2) / real n < real k / real n"
      using half_less denominator_positive
      by (rule divide_strict_right_mono)

    have left:
      "(real n / 2) / real n = (1::real) / 2"
      using denominator_positive by (field_simp)

    from quotient_less left show ?thesis
      using False True by simp
  qed
qed

definition likely_next_time :: "'a list ⇒ 'a ⇒ bool" where
  "likely_next_time xs a ⟷
     pmf (empirical_pmf xs) a > (1 / 2)"

theorem repeated_observation_predicts_repetition:
  fixes xs :: "'a list" and a :: 'a
  shows
    "xs ≠ [] ⟶
     2 * count_list xs a > length xs ⟶
     pmf (empirical_pmf xs) a > (1 / 2)"
proof (cases "xs = []")
  case True
  then show ?thesis by simp
next
  case False
  note nonempty = False

  show ?thesis
  proof (cases "2 * count_list xs a > length xs")
    case False
    then show ?thesis by simp
  next
    case True
    note frequent = True

    show ?thesis
    proof (cases "pmf (empirical_pmf xs) a > (1 / 2)")
      case True
      then show ?thesis by simp
    next
      case False
      note not_likely = False

      have probability_value:
        "pmf (empirical_pmf xs) a =
         real (count_list xs a) / real (length xs)"
        using empirical_pmf_probability[of xs a] nonempty
        by blast

      have frequency_is_high:
        "real (count_list xs a) / real (length xs) > (1 / 2)"
        using majority_frequency_exceeds_half
          [of "length xs" "count_list xs a"]
          nonempty frequent
        by blast

      have contradiction: False
        using not_likely probability_value frequency_is_high
        by linarith

      from contradiction show ?thesis by blast
    qed
  qed
qed

theorem scientific_induction_analytic:
  fixes xs :: "'a list" and a :: 'a
  shows
    "xs ≠ [] ⟶
     2 * count_list xs a > length xs ⟶
     likely_next_time xs a"
  using repeated_observation_predicts_repetition
  by (auto simp: likely_next_time_def)

text ‹A concrete counterexample to the stronger claim that
  a majority of observations makes the event certain.›

lemma majority_does_not_imply_certainty:
  "2 * count_list [True, True, False] True >
       length [True, True, False]
   ∧ pmf (empirical_pmf [True, True, False]) True < 1"
proof -
  have probability:
    "pmf (empirical_pmf [True, True, False]) True =
       (2::real) / 3"
    using empirical_pmf_probability
      [of "[True, True, False]" True]
    by simp
  show ?thesis
    using probability by norm_num
qed

end
