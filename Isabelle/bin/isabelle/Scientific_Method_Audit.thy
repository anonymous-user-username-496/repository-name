
theory Scientific_Method_Audit
  imports Main
begin

(* A probability is called likely when it is greater than one half. *)
definition likely :: "real => bool" where
  "likely p <-> p > 1 / 2"

(* A probability is called not likely when it is at most one half. *)
definition not_likely :: "real => bool" where
  "not_likely p <-> p <= 1 / 2"

(* An event has happened often when its count reaches a chosen threshold. *)
definition happened_often :: "nat => bool" where
  "happened_often n <-> n >= 100"


(* PART 1:
   Case elimination.
   If the not-likely case is ruled out, the probability is likely.
   No separate law-of-non-contradiction assumption is needed. *)

lemma eliminate_not_likely:
  fixes p :: real
  assumes "not_likely p --> False"
  shows "likely p"
  using assms
  unfolding not_likely_def likely_def
  by auto


(* PART 2:
   The two cases cover every real probability under this definition. *)

lemma likely_or_not_likely:
  fixes p :: real
  shows "likely p | not_likely p"
  unfolding likely_def not_likely_def
  by auto


(* PART 3:
   A probability value is equal to itself.
   Uniqueness of a fixed value does not establish which value it is. *)

lemma probability_value_equals_itself:
  fixes p :: real
  shows "p = p"
  by simp


(* PART 4:
   Counterexample to the claim that a high past count alone
   establishes that the next event is likely.

   The count reaches the chosen threshold, while a proposed next-event
   probability of zero is not likely under the definition above. *)

lemma repetition_alone_does_not_imply_likelihood:
  "happened_often 100 & ~ likely (0::real)"
  unfolding happened_often_def likely_def
  by simp


(* PART 5:
   The precise conditional form of the proposed case-elimination
   argument: if the not-likely case for p is ruled out, then p is likely.
   The past count is deliberately not used to rule out that case. *)

lemma case_elimination_for_next_probability:
  fixes p :: real
  assumes "not_likely p --> False"
  shows "likely p"
  using assms
  by (rule eliminate_not_likely)


end
