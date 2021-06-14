theory HybridSCInduct imports Main
begin

datatype 'a form = 
  Pro 'a | 
  Nom nat | 
  Neg "'a form" |
  Con "'a form" "'a form" | 
  Sat nat "'a form" (\<open>@\<close> 210) | 
  Pos "'a form" (\<open>\<diamond>\<close> 220)

primrec replace_form where
  \<open>replace_form (Pro a) n m = Pro a\<close> |
  \<open>replace_form (Nom i) n m = Nom (if i = n then m else i)\<close> |
  \<open>replace_form (Neg p) n m = Neg (replace_form p n m)\<close> |
  \<open>replace_form (Con p q) n m = Con (replace_form p n m) (replace_form q n m)\<close> |
  \<open>replace_form (Sat i p) n m = Sat (if i = n then m else i) (replace_form p n m)\<close> |
  \<open>replace_form (Pos p) n m = Pos (replace_form p n m)\<close>

primrec replace' :: \<open>(nat \<times> 'a form) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> 'a form)\<close> where
  \<open>replace' (i,p) n m = (if i = n then m else i, replace_form p n m)\<close>

definition replace where 
  \<open>replace A n m B \<equiv> 
    (\<forall> p \<in> A. \<exists> q \<in> B. replace' p n m = q) \<and> (\<forall> q \<in> B. \<exists> p \<in> A. replace' p n m = q)\<close>

primrec fresh' where
  \<open>fresh' (Pro a) n = True\<close> |
  \<open>fresh' (Nom i) n = (i \<noteq> n)\<close> |
  \<open>fresh' (Neg p) n = fresh' p n\<close> |
  \<open>fresh' (Con p q) n = (fresh' p n \<and> fresh' q n)\<close> |
  \<open>fresh' (Sat i p) n = (i \<noteq> n \<and> fresh' p n)\<close> |
  \<open>fresh' (Pos p) n = fresh' p n\<close>

definition fresh where \<open>fresh A n \<equiv> \<forall> (i,p) \<in> A. n \<noteq> i \<and> fresh' p n\<close>

inductive SC :: \<open>(nat \<times> 'a form) set \<Rightarrow> (nat \<times> 'a form) set \<Rightarrow> bool\<close> (infix \<open>\<turnstile>\<close> 0) where
1:\<open>insert a \<Gamma> \<turnstile> insert a \<Delta>\<close> |
2:\<open>\<Gamma> \<turnstile> insert (n, Nom n) \<Delta>\<close> |
3:\<open>replace \<Gamma> n m \<Gamma>' \<Longrightarrow> replace \<Delta> n m \<Delta>' \<Longrightarrow> \<Gamma>' \<turnstile> \<Delta>' \<Longrightarrow> insert (n, Nom m) \<Gamma> \<turnstile> \<Delta>\<close> |
4:\<open>\<Gamma> \<turnstile> insert (n, p) \<Delta> \<Longrightarrow> insert (n, Neg p) \<Gamma> \<turnstile> \<Delta>\<close> |
5:\<open>insert (n, p) \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> insert (n, Neg p) \<Delta>\<close> |
6:\<open>insert (n, p) (insert (n, q) \<Gamma>) \<turnstile> \<Delta> \<Longrightarrow> insert (n, Con p q) \<Gamma> \<turnstile> \<Delta>\<close> |
7:\<open>\<Gamma> \<turnstile> insert (n, p) \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> insert (n, q) \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> insert (n, Con p q) \<Delta>\<close> |
8:\<open>\<Gamma> \<turnstile> insert (m, p) \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> insert (n, Sat m p) \<Delta>\<close> |
9:\<open>insert (m, p) \<Gamma> \<turnstile> \<Delta> \<Longrightarrow> insert (n, Sat m p) \<Gamma> \<turnstile> \<Delta>\<close> |
10:\<open>fresh ({(n, Pos p)} \<union> \<Gamma> \<union> \<Delta>) m \<Longrightarrow> insert (n, Pos (Nom m)) (insert (m, p) \<Gamma>) \<turnstile> \<Delta> \<Longrightarrow> 
  insert (n, Pos p) \<Gamma> \<turnstile> \<Delta>\<close> |
11:\<open>\<not>fresh (\<Gamma> \<union> {(n, Pos p)} \<union> \<Delta>) m \<Longrightarrow> \<Gamma> \<turnstile> insert (n, Pos (Nom m)) \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> insert (m, p) \<Delta> \<Longrightarrow>
  \<Gamma> \<turnstile> insert (n, Pos p) \<Delta>\<close>

primrec semantics_form where 
  \<open>semantics_form R V G w (Pro a) = V w a\<close> |
  \<open>semantics_form R V G w (Nom n) = (G n = w)\<close> |
  \<open>semantics_form R V G w (Neg p) = (\<not> semantics_form R V G w p)\<close> |
  \<open>semantics_form R V G w (Con p q) = (semantics_form R V G w p \<and> semantics_form R V G w p)\<close> |
  \<open>semantics_form R V G w (Sat n p) = semantics_form R V G (G n) p\<close> |
  \<open>semantics_form R V G w (Pos p) = (\<exists> w'. R w w' \<and> semantics_form R V G w' p)\<close>

definition semantics_SC where 
  \<open>semantics_SC R V G A B \<equiv> 
    (\<forall> (n,p) \<in> A. semantics_form R V G (G n) p) \<longrightarrow> (\<exists> (n,p) \<in> B. semantics_form R V G (G n) p)\<close>


lemma completness: \<open>finite A \<Longrightarrow> finite B \<Longrightarrow> (\<forall> R V G. semantics_SC R V G A B) \<Longrightarrow> A \<turnstile> B\<close>
(is \<open>?P1 \<Longrightarrow> ?P2 \<Longrightarrow> ?SEM \<Longrightarrow> ?SC\<close>)
  sorry
end