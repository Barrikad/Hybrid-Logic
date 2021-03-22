theory HybridFOL imports Main
begin

datatype 'a hybr_form 
  =  Pro 'a 
  | Nom nat
  | HNeg \<open>'a hybr_form \<close> 
  | HCon \<open>'a hybr_form \<close> \<open>'a hybr_form \<close>
  | Sat nat \<open>'a hybr_form \<close> 
  | Pos \<open>'a hybr_form \<close>

fun hybr_semantics :: \<open>('c \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
                  (nat \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> 'a hybr_form \<Rightarrow> bool\<close> where
  \<open>hybr_semantics R V G w (Pro a) = V w a\<close> |
  \<open>hybr_semantics R V G w (Nom n) = ((G n) = w)\<close> |
  \<open>hybr_semantics R V G w (HNeg p) = (\<not> hybr_semantics R V G w p)\<close> |
  \<open>hybr_semantics R V G w (HCon p1 p2) = (hybr_semantics R V G w p1 \<and> hybr_semantics R V G w p2)\<close> |
  \<open>hybr_semantics R V G w (Sat n p) = hybr_semantics R V G (G n) p\<close> |
  \<open>hybr_semantics R V G w (Pos p) = (\<exists>v. (R w v) \<and> (hybr_semantics R V G v p))\<close>

datatype 'a fol_form
  = Apply 'a nat
  | R nat nat
  | Eq nat nat 
  | FNeg \<open>'a fol_form\<close>
  | FCon \<open>'a fol_form\<close> \<open>'a fol_form\<close>
  | Ex nat \<open>'a fol_form\<close>
 
primrec member where
  \<open>member _ [] = False\<close> |
  \<open>member m (n # A) = (m = n \<or> member m A)\<close>

lemma member_iff [iff]: \<open>member m A \<longleftrightarrow> m \<in> set A\<close>
  by (induct A) simp_all

fun fol_semantics where
  \<open>\<close>

fun ST where
  \<open>ST n (Pro a) nxt = Apply a n\<close> |
  \<open>ST n1 (Nom n2) nxt = Eq n1 n2\<close> |
  \<open>ST n (HNeg p) nxt = FNeg (ST n p nxt)\<close> |
  \<open>ST n (HCon p1 p2) nxt = FCon (ST n p1 nxt) (ST n p2 nxt)\<close> |
  \<open>ST n1 (Sat n2 p) nxt = ST n2 p nxt\<close> |
  \<open>ST n (Pos p) nxt = Ex nxt (FCon (R n nxt) (ST nxt p (Suc nxt)))\<close>




end