theory HybridFOL imports Main
begin

primrec member where
  \<open>member _ [] = False\<close> |
  \<open>member m (n # A) = (m = n \<or> member m A)\<close>

lemma member_iff [iff]: \<open>member m A \<longleftrightarrow> m \<in> set A\<close>
  by (induct A) simp_all

definition almostAgree where \<open>almostAgree G n w n' = (if n' = n then w else G n')\<close>

datatype 'a hybr_form 
  =  Pro 'a 
  | Nom nat
  | HNeg \<open>'a hybr_form \<close> 
  | HCon \<open>'a hybr_form \<close> \<open>'a hybr_form \<close>
  | Sat nat \<open>'a hybr_form \<close> 
  | Pos \<open>'a hybr_form \<close>

primrec maxNom where
  \<open>maxNom (Pro a) n = n\<close> |
  \<open>maxNom (Nom n1) n2 = max n1 n2\<close> |
  \<open>maxNom (HNeg p) n = maxNom p n\<close> |
  \<open>maxNom (HCon p1 p2) n = maxNom p1 (maxNom p2 n)\<close> |
  \<open>maxNom (Sat n1 p) n2 = maxNom p (max n1 n2)\<close> |
  \<open>maxNom (Pos p) n = maxNom p n\<close>

primrec hybr_semantics :: \<open>'c set \<Rightarrow> ('c \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
                  (nat \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> 'a hybr_form \<Rightarrow> bool\<close> where
  \<open>hybr_semantics W R V G w (Pro a) = V w a\<close> |
  \<open>hybr_semantics W R V G w (Nom n) = ((G n) = w)\<close> |
  \<open>hybr_semantics W R V G w (HNeg p) = (\<not> hybr_semantics W R V G w p)\<close> |
  \<open>hybr_semantics W R V G w (HCon p1 p2) = (hybr_semantics W R V G w p1 
                                         \<and>  hybr_semantics W R V G w p2)\<close> |
  \<open>hybr_semantics W R V G w (Sat n p) = hybr_semantics W R V G (G n) p\<close> |
  \<open>hybr_semantics W R V G w (Pos p) = (\<exists> v \<in> W. (R w v) \<and> (hybr_semantics W R V G v p))\<close>

datatype 'a fol_form
  = Apply 'a nat
  | Eq nat nat 
  | FNeg \<open>'a fol_form\<close>
  | FCon \<open>'a fol_form\<close> \<open>'a fol_form\<close>
  | ExRel nat nat \<open>'a fol_form\<close>

primrec fol_semantics where
  \<open>fol_semantics W R V G (Apply a n) = V (G n) a\<close> |
  \<open>fol_semantics W R V G (Eq n1 n2) = ((G n1) = (G n2))\<close> |
  \<open>fol_semantics W R V G (FNeg p) = (\<not> fol_semantics W R V G p)\<close> |
  \<open>fol_semantics W R V G (FCon p1 p2) = (fol_semantics W R V G p1 \<and> fol_semantics W R V G p2)\<close> |
  \<open>fol_semantics W R V G (ExRel n1 n2 p) = 
    (\<exists> w \<in> W. R (G n1) w \<and> fol_semantics W R V (almostAgree G n2 w) p)\<close>

primrec ST where
  \<open>ST n (Pro a) nxt = Apply a n\<close> |
  \<open>ST n1 (Nom n2) nxt = Eq n1 n2\<close> |
  \<open>ST n (HNeg p) nxt = FNeg (ST n p nxt)\<close> |
  \<open>ST n (HCon p1 p2) nxt = FCon (ST n p1 nxt) (ST n p2 nxt)\<close> |
  \<open>ST n1 (Sat n2 p) nxt = ST n2 p nxt\<close> |
  \<open>ST n (Pos p) nxt = ExRel n nxt (ST nxt p (Suc nxt))\<close>

theorem correctST: \<open>hybr_semantics W R V G w p 
 = fol_semantics W R V (almostAgree G (Suc (maxNom p 0)) w) 
    (ST (Suc (maxNom p 0)) p (Suc (Suc (maxNom p 0))))\<close>
  sorry

primrec HT :: \<open>'a fol_form \<Rightarrow> 'a hybr_form\<close> where
  \<open>HT (Apply a n) = Sat n (Pro a)\<close> |
  \<open>HT (Eq n1 n2) = Sat n1 (Nom n2)\<close> |
  \<open>HT (FNeg p) = HNeg (HT p)\<close> |
  \<open>HT (FCon p1 p2) = HCon (HT p1) (HT p2)\<close> |
  \<open>HT (ExRel n1 n2 p) = Sat n1 (Pos (HT p))\<close>

theorem correctHT: \<open>fol_semantics W R V G p 
  = hybr_semantics W R V G w (HT p)\<close>
  nitpick

end