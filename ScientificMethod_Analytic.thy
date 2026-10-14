theory ScientificMethod_Analytic
  imports "HOL-Probability.Probability"
begin

text ‹All content is definitional. No axiomatization. No assumes.
  Library terms used directly:
  ▪ @{typ "'a measure"} and @{term "prob M A"} — HOL-Probability
  ▪ @{term "prob_space"} locale — HOL-Probability
  ▪ @{term "(^) :: real ⇒ nat ⇒ real"} — HOL.Power›

definition epsilon :: real where
  "epsilon ≡ 1/1000"

definition likely :: "'a measure ⇒ 'a set ⇒ bool" where
  "likely M A ≡ 1/2 < prob M A"

definition too_many_times :: "nat ⇒ bool" where
  "too_many_times n ≡ (1/2)^n < epsilon"

definition observable :: "real ⇒ bool" where
  "observable p ≡ epsilon ≤ p"

text ‹The case split is internal: we prove the disjunction
  @{term "likely M A ∨ ¬ observable ((prob M A)^n) ∨ ¬ too_many_times n"}
  by case analysis on @{term "likely M A"}. No premises.›

theorem scientific_method_analytic:
  fixes M :: "'a measure" and A :: "'a set" and n :: nat
  shows "likely M A ∨ ¬ observable ((prob M A)^n) ∨ ¬ too_many_times n"
proof (cases "likely M A")
  case True
  thus ?thesis by simp
next
  case False
  ― ‹In this branch ¬likely M A. We show ¬observable ((prob M A)^n)
      by pure definitional unfolding. The case split on too_many_times
      is also internal.›
  show ?thesis
  proof (cases "too_many_times n")
    case False
    thus ?thesis by simp
  next
    case True
    ― ‹Here too_many_times n holds. We derive ¬observable.›
    have h1: "prob M A ≤ 1/2" using False by (simp add: likely_def)
    have h2: "0 ≤ prob M A"
      ― ‹This is a library theorem: prob_nonneg. It holds for any measure.›
      by (rule prob_space.prob_nonneg) simp
    have h3: "(prob M A)^n ≤ (1/2)^n"
      using h2 h1 by (rule power_mono)
    have h4: "(1/2)^n < epsilon"
      using True by (simp add: too_many_times_def)
    have "prob M A ^ n < epsilon" using h3 h4 by linarith
    hence "¬ observable ((prob M A)^n)"
      by (simp add: observable_def)
    thus ?thesis by simp
  qed
qed

end