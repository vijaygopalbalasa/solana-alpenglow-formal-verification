(*  Alpenglow Arithmetic Lemmas for TLAPS
    Additional arithmetic lemmas needed for Solana Alpenglow consensus proofs
*)

theory AlpenglowArithmetic
imports IntegerArithmetic
begin

(* These lemmas are declared as axioms for now, to be proven separately *)
(* They represent arithmetic facts that should be provable from TLA+ integer properties *)

axiomatization where
AlpenglowNatSubtraction:
  "\<lbrakk>a \<in> Nat; b \<in> Nat; c \<in> Nat; a + b >= c\<rbrakk>
   \<Longrightarrow> a >= c - b \<or> b >= c - a" and

AlpenglowDoubling:
  "\<lbrakk>a \<in> Nat; c \<in> Nat; a >= c; a >= c\<rbrakk>
   \<Longrightarrow> a + a >= 2 * c" and

AlpenglowInequality:
  "\<lbrakk>a \<in> Nat; b \<in> Nat; c \<in> Nat; a >= b + c; c > 0\<rbrakk>
   \<Longrightarrow> a > b" and

AlpenglowTransitivity:
  "\<lbrakk>a \<in> Nat; b \<in> Nat; c \<in> Nat; a >= b; b >= c\<rbrakk>
   \<Longrightarrow> a >= c"

end
