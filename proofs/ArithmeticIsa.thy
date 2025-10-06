theory ArithmeticIsa
  imports "$ISABELLE_HOME/src/HOL/HOL"
begin

(* Arithmetic lemmas for Solana Alpenglow consensus protocol verification *)

(* Lemma 1: Subtraction inequality *)
lemma arithmetic_subtraction:
  fixes a b c :: nat
  assumes "a + b \<ge> c"
  shows "a \<ge> c - b \<or> b \<ge> c - a"
  using assms by auto

(* Lemma 2: Doubling inequality *)
lemma arithmetic_doubling:
  fixes a c :: nat
  assumes "a \<ge> c" "a \<ge> c"
  shows "a + a \<ge> 2 * c"
  using assms by auto

(* Lemma 3: Strict inequality from addition *)
lemma arithmetic_inequality:
  fixes a b c :: nat
  assumes "a \<ge> b + c" "c > 0"
  shows "a > b"
  using assms by auto

(* Lemma 4: Transitivity of \<ge> *)
lemma arithmetic_transitivity:
  fixes a b c :: nat
  assumes "a \<ge> b" "b \<ge> c"
  shows "a \<ge> c"
  using assms by auto

end
