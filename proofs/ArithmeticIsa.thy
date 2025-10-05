theory ArithmeticIsa
  imports Main
begin

(* Arithmetic lemmas for TLAPS obligations *)

lemma NatSubtraction:
  fixes a b c :: nat
  assumes "a + b >= c"
  shows "a >= c - b"
  using assms by arith

lemma NatSubtraction2:
  fixes a b c :: nat
  assumes "a >= b + c" "c > 0"
  shows "a > b"
  using assms by arith

lemma NatDouble:
  fixes a b c :: nat
  assumes "a >= c" "b >= c"
  shows "a + b >= 2 * c"
  using assms by arith

lemma NatTransitivity:
  fixes a b c :: nat
  assumes "a >= b" "b >= c"
  shows "a >= c"
  using assms by arith

lemma NatContradiction:
  fixes a :: nat
  assumes "0 >= a" "a > 0"
  shows "False"
  using assms by arith

end
