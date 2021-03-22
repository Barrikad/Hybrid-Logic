theory HybridFOL imports Main
begin

datatype ('a, 'b) hybr_form 
  =  Pro 'a 
  | Nom \<open>'b\<close>
  | Neg \<open>('a,'b) hybr_form\<close> 
  | Con \<open>('a,'b) hybr_form\<close> \<open>('a,'b) hybr_form\<close>
  | Sat \<open>'b\<close> \<open>('a,'b) hybr_form\<close> 
  | Pos \<open>('a,'b) hybr_form\<close>

fun semantics :: \<open>('c \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
                  ('b \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> ('a, 'b) hybr_form \<Rightarrow> bool\<close> where
  \<open>semantics R V G w (Pro a) = V w a\<close> |
  \<open>semantics R V G w (Nom n) = ((G n) = w)\<close> |
  \<open>semantics R V G w (Neg p) = (\<not> semantics R V G w p)\<close> |
  \<open>semantics R V G w (Con p1 p2) = (semantics R V G w p1 \<and> semantics R V G w p2)\<close> |
  \<open>semantics R V G w (Sat n p) = semantics R V G (G n) p\<close> |
  \<open>semantics R V G w (Pos p) = (\<exists>v. (R w v) \<and> (semantics R V G v p))\<close>
 
primrec member where
  \<open>member _ [] = False\<close> |
  \<open>member m (n # A) = (m = n \<or> member m A)\<close>

lemma member_iff [iff]: \<open>member m A \<longleftrightarrow> m \<in> set A\<close>
  by (induct A) simp_all

fun hv where
  \<open>hv n (Pro a) = (a,n)\<close>|
  \<open>\<close>
end