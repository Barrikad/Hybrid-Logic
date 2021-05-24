theory HybridSequentCalculus imports Main ListSet
begin

datatype 'a hybr_form 
  =  Pro 'a (\<open>PRO _\<close> [999] 999)
  | Nom nat (\<open>NOM _\<close> [998] 998)
  | Neg \<open>'a hybr_form\<close> (\<open>NOT _\<close> [900] 900)
  | Con \<open>'a hybr_form\<close> \<open>'a hybr_form\<close> (infixl "AND" 300)
  | Sat nat \<open>'a hybr_form\<close> (\<open>AT _ _\<close> [899]  899)
  | Pos \<open>'a hybr_form\<close> (\<open>\<diamond> _\<close> [800] 800)

primrec semantics :: \<open>'c set \<Rightarrow> ('c \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
                  (nat \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> 'a hybr_form \<Rightarrow> bool\<close> where
  \<open>semantics W R V G w (Pro a) = V w a\<close> |
  \<open>semantics W R V G w (Nom n) = ((G n) = w)\<close> |
  \<open>semantics W R V G w (Neg p) = (\<not> semantics W R V G w p)\<close> |
  \<open>semantics W R V G w (Con p1 p2) = (semantics W R V G w p1 \<and> semantics W R V G w p2)\<close> |
  \<open>semantics W R V G w (Sat n p) = semantics W R V G (G n) p\<close> |
  \<open>semantics W R V G w (Pos p) = (\<exists>v \<in> W. (R w v) \<and> (semantics W R V G v p))\<close>

abbreviation \<open>sc W X Y R V G w \<equiv> 
  (\<forall> x \<in> X. semantics W R V G w x) \<longrightarrow> (\<exists> y \<in> Y. semantics W R V G w y)\<close>

(*find the maximal nominal in a list of nominals, and return one bigger than that*)
definition lmax :: \<open>nat list \<Rightarrow> nat\<close> where \<open>lmax N \<equiv> foldr (\<lambda> x i. max x i) N 0\<close>

lemma lmax_max: "member n N \<Longrightarrow> n \<le> lmax N"
proof (induct N)
  case Nil
  then show ?case by simp
next
  case (Cons a N)
  assume a1: "member n N \<Longrightarrow> n \<le> lmax N"
  assume a2: "member n (a # N)"
  then show ?case 
  proof cases
    assume \<open>a = n\<close>
    then show ?thesis using lmax_def by simp
  next
    assume \<open>\<not> a = n\<close>
    then have "member n N" using a2 
      by (metis member.simps(2))
    then have 1:"n \<le> lmax N" using a1 by simp
    have "lmax N \<le> lmax (a # N)" using lmax_def by simp
    then show ?thesis using 1 by simp
  qed
qed 
  
(*return nominal not in a set of nominals*)
abbreviation fresh where \<open>fresh N \<equiv> Suc (lmax N)\<close>

lemma fresh_new: "fresh N = n \<Longrightarrow> \<not> member n N"
  using lmax_max by fastforce

(*get a set of all used nominal, for different formula representations*)
primrec nominalsForm where
  \<open>nominalsForm (Pro a) = []\<close> |
  \<open>nominalsForm (Nom n) = [n]\<close> |
  \<open>nominalsForm (Neg p) = nominalsForm p\<close> |
  \<open>nominalsForm (Con p1 p2) = union (nominalsForm p1) (nominalsForm p2)\<close> |
  \<open>nominalsForm (Sat n p) = add n (nominalsForm p)\<close> |
  \<open>nominalsForm (Pos p) = nominalsForm p\<close>

primrec nominalsForms where
  \<open>nominalsForms [] = []\<close> |
  \<open>nominalsForms (x # xs) = union (nominalsForm x) (nominalsForms xs)\<close>

fun nominalsNN where
  \<open>nominalsNN [] = []\<close> |
  \<open>nominalsNN ((n1,n2) # NN) = add n1 (add n2 (nominalsNN NN))\<close>

fun nominalsNA where
  \<open>nominalsNA [] = []\<close> |
  \<open>nominalsNA ((n,a) # NA) = add n (nominalsNA NA)\<close>

fun nominalsNP where
  \<open>nominalsNP [] = []\<close> |
  \<open>nominalsNP ((n,p) # NP) = add n (union (nominalsForm p) (nominalsNP NP))\<close>

fun nominalsNSNP where
  \<open>nominalsNSNP [] = []\<close> |
  \<open>nominalsNSNP ((n,ns,p) # NSNP) = nominalsNSNP NSNP U add n (ns U nominalsForm p)\<close>

lemma form_is_set: \<open>is_set (nominalsForm P)\<close>
  apply (induct P)
       apply simp_all
   apply (simp add: union_is_set)
  by (simp add: add_def)

lemma forms_is_set: \<open>is_set (nominalsForms ps)\<close>
  by (induct ps) (simp_all add: form_is_set union_is_set)

lemma NN_is_set: \<open>is_set (nominalsNN NN)\<close>
  apply (induct NN)
   apply simp
  by (smt (verit) add_def is_set.simps(2) nominalsNN.simps(2) old.prod.exhaust)

lemma NA_is_set: \<open>is_set (nominalsNA NA)\<close>
  apply (induct NA)
   apply simp
  by (metis nominalsNA.simps(2) old.prod.exhaust union.simps(1) union.simps(2) union_is_set)
 
lemma NP_is_set: \<open>is_set (nominalsNP NP)\<close>
  apply (induct NP)
   apply simp
  by (metis (no_types, hide_lams) form_is_set 
      list.distinct(1) nominalsNP.cases nominalsNP.simps(2) 
      union.simps(1) union.simps(2) union_is_set)

lemma NSNP_is_set: \<open>is_set (nominalsNSNP NSNP)\<close>
proof (induct NSNP)
  case Nil
  then show ?case by simp
next
  case (Cons a NSNP)
  then show ?case 
    by (metis list.discI list.inject nominalsNSNP.elims union_is_set)
qed

(*merge functions replaces all occurences of a nominal with another.
Used when two nominals are found to be equal*)
fun mergeNS where 
  \<open>mergeNS NS na nb = map (\<lambda> n. if n = na then nb else n) NS\<close>

fun mergeNN where
  \<open>mergeNN [] na nb = []\<close> |
  \<open>mergeNN ((n1,n2) # NN) na nb = (
    let n3 = (if n1 = na then nb else n1) in 
    let n4 = (if n2 = na then nb else n2) in 
    (n3,n4) # (mergeNN NN na nb))\<close>

fun mergeNA where
  \<open>mergeNA [] na nb = []\<close> |
  \<open>mergeNA ((n1,a) # NA) na nb = (if n1 = na then nb else n1, a) # (mergeNA NA na nb)\<close>

fun mergeP where
  \<open>mergeP (Pro a) na nb = Pro a\<close> |
  \<open>mergeP (Nom n) na nb = Nom (if n = na then nb else n)\<close> |
  \<open>mergeP (Neg p) na nb = Neg (mergeP p na nb)\<close> |
  \<open>mergeP (Con p1 p2) na nb = Con (mergeP p1 na nb) (mergeP p2 na nb)\<close> |
  \<open>mergeP (Sat n p) na nb = Sat (if n = na then nb else n) (mergeP p na nb)\<close> |
  \<open>mergeP (Pos p) na nb = Pos (mergeP p na nb)\<close>

fun mergeNP where
  \<open>mergeNP [] na nb = []\<close> |
  \<open>mergeNP ((n,p) # NP) na nb = (if n = na then nb else n, mergeP p na nb) # (mergeNP NP na nb)\<close>

fun mergeNSNP where
  \<open>mergeNSNP [] na nb = []\<close> |
  \<open>mergeNSNP ((n,ns,p) # R) na nb = 
    (if n = na then nb else n, mergeNS ns na nb, mergeP p na nb) # (mergeNSNP R na nb)\<close>

lemma member_mergeNN: \<open>
  member n (nominalsNN (mergeNN nn n1 n2)) \<Longrightarrow> 
    member n (nominalsNN nn) \<or> n = n2\<close> 
  apply (induct nn)
   apply simp
  using ListSet.member.simps(2) list.discI by fastforce

lemma sub_setNN: \<open>
  member n2 (nominalsNN nn) \<Longrightarrow> sub_set (nominalsNN (mergeNN nn n1 n2)) (nominalsNN nn)\<close>
proof (induct nn)
  case Nil
  then show ?case by simp
next
  case (Cons a nn)
  obtain n1' n2' where adef:\<open>a = (n1',n2')\<close>
    by (meson prod.exhaust_sel)
  then show ?case 
    by (metis (full_types) Cons.prems member_mergeNN member_sub_set)
qed

lemma member_mergeNA: \<open>
  member n (nominalsNA (mergeNA na n1 n2)) \<Longrightarrow> 
    member n (nominalsNA na) \<or> n = n2\<close> 
  apply (induct na)
  apply simp
  using ListSet.member.simps(2) list.discI by fastforce

lemma sub_setNA: \<open>
  member n2 (nominalsNA na) \<Longrightarrow> sub_set (nominalsNA (mergeNA na n1 n2)) (nominalsNA na)\<close> 
proof (induct na)
  case Nil
  then show ?case by simp
next
  case (Cons a na)
  obtain n1' a' where adef:\<open>a = (n1',a')\<close>
    by (meson prod.exhaust_sel)
  then show ?case 
    by (metis (full_types) Cons.prems member_mergeNA member_sub_set)
qed

lemma member_mergeNS: \<open>
  member n (mergeNS ns n1 n2) \<Longrightarrow> member n ns \<or> n = n2\<close> 
  apply (induct ns)
  apply simp
  using ListSet.member.simps(2) list.discI by fastforce

lemma member_mergeNS2: \<open>member n ns \<Longrightarrow> n = n1 \<Longrightarrow> member n2 (mergeNS ns n1 n2)\<close> 
proof (induct ns)
  case Nil
  then show ?case by simp
next
  case (Cons a ns)
  show ?case 
  proof cases
    assume "a = n1"
    then show ?thesis 
      by simp
  next
    assume \<open>a \<noteq> n1\<close>
    then have \<open>member n2 (mergeNS ns n1 n2)\<close> 
      by (metis Cons.hyps Cons.prems(1) Cons.prems(2) ListSet.member.simps(2))
    then show ?thesis
      by simp
  qed
qed

lemma member_mergeNS3: \<open>member n ns \<Longrightarrow> n \<noteq> n1 \<Longrightarrow> member n (mergeNS ns n1 n2)\<close> 
proof (induct ns)
  case Nil
  then show ?case by simp
next
  case (Cons a ns)
  show ?case 
  proof cases
    assume "a = n"
    then show ?thesis
      using Cons.prems by simp
  next
    assume \<open>a \<noteq> n\<close>
    then have \<open>member n ns\<close> 
      by (metis Cons.prems(1) ListSet.member.simps(2))
    then have \<open>member n (mergeNS ns n1 n2)\<close> 
      using Cons.hyps Cons.prems(2) by blast
    then show ?thesis 
      by simp
  qed
qed

lemma sub_setNS: \<open>
  member n2 ns \<Longrightarrow> sub_set (mergeNS ns n1 n2) ns\<close> 
proof (induct ns)
  case Nil
  then show ?case by simp
next
  case (Cons n ns)
  then show ?case 
    by (metis member_mergeNS member_sub_set)
qed

lemma member_mergeP: \<open>
  member n (nominalsForm (mergeP p n1 n2)) \<Longrightarrow> 
    member n (nominalsForm p) \<or> n = n2\<close> 
  apply (induct p)
       apply simp_all 
   apply (metis Un_iff union_simp) 
  by (metis (full_types) add_simp insertCI insertE)

lemma sub_setP: \<open>
  member n2 (nominalsForm p) \<Longrightarrow> sub_set (nominalsForm (mergeP p n1 n2)) (nominalsForm p)\<close> 
proof (induct p)
  case (Con p1 p2)
  then show ?case 
    using member_mergeP by blast
next
  case (Sat x1a p)
  then show ?case
    using member_mergeP by blast
qed simp_all

lemma member_mergeNP: \<open>
  member n (nominalsNP (mergeNP np n1 n2)) \<Longrightarrow> 
    member n (nominalsNP np) \<or> n = n2\<close> 
proof (induct np)
  case Nil
  then show ?case by simp
next
  case (Cons a np)
  obtain n' p' where 1:"a = (n',p')" 
    using surjective_pairing by blast
  then have \<open>
    set_equal 
      (nominalsNP (mergeNP (a # np) n1 n2)) 
      ((nominalsNP (mergeNP [a] n1 n2)) U (nominalsNP (mergeNP np n1 n2)))\<close> 
    using unionadd1 by force
  then consider 
    "member n (nominalsNP (mergeNP [a] n1 n2))" | "member n (nominalsNP (mergeNP np n1 n2))" 
    using Cons.prems union_member by fastforce
  then show ?case 
  proof cases
    case 1
    obtain nm pm where 2: \<open>mergeNP [a] n1 n2 = [(nm,pm)]\<close> 
      by (metis mergeNP.simps(1) mergeNP.simps(2) old.prod.exhaust)
    consider \<open>n = nm \<or> member n (nominalsForm pm)\<close>
      by (metis "1" ListSet.member.simps(2) 2 add_def nominalsNP.simps(1) 
          nominalsNP.simps(2) union.simps(1))
    then show ?thesis 
      by (smt (verit, ccfv_SIG) "2" ListSet.member.simps(2) Pair_inject 
          \<open>\<And>thesis. (\<And>n' p'. a = (n', p') \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> add_def list.inject 
          member_mergeP member_sub_set mergeNP.simps(2) nominalsNP.simps(2) sub_set_union1)
  next
    case 2
    then have "member n (nominalsNP np) \<or> n = n2"
      using Cons.hyps by blast
    moreover have \<open>member n (nominalsNP np) \<Longrightarrow> member n (nominalsNP (a # np))\<close>
      by (metis ListSet.member.simps(2) 1 add_def nominalsNP.simps(2) union_member)
    ultimately show ?thesis
      by blast
  qed
qed

lemma sub_setNP: \<open>
  member n2 (nominalsNP np) \<Longrightarrow> sub_set (nominalsNP (mergeNP np n1 n2)) (nominalsNP np)\<close> 
proof (induct np)
  case Nil
  then show ?case by simp
next
  case (Cons a na)
  obtain n1' a' where adef:\<open>a = (n1',a')\<close>
    by (meson prod.exhaust_sel)
  then show ?case 
    using Cons.prems member_mergeNP by blast
qed


lemma member_mergeNSNP: \<open>
  member n (nominalsNSNP (mergeNSNP nsnp n1 n2)) \<Longrightarrow> 
    member n (nominalsNSNP nsnp) \<or> n = n2\<close> 
proof (induct nsnp)
  case Nil
  then show ?case by simp
next
  case (Cons a nsnp)
  obtain ns' n' p' where adef:\<open>a = (ns',n',p')\<close> 
    using prod_cases3 by blast
  then obtain nsm nm pm where madef:\<open>mergeNSNP [a] n1 n2 = [(nm,nsm,pm)]\<close> 
    by simp
  consider 
    \<open>member n (nominalsNSNP (mergeNSNP nsnp n1 n2))\<close> | 
    \<open>member n (nominalsNSNP (mergeNSNP [a] n1 n2))\<close> 
    by (smt (verit, ccfv_threshold) Cons.prems ListSet.member.simps(2) add_def adef 
        mergeNSNP.simps(2) nominalsNSNP.simps(2) union_member)
  then show ?case 
  proof cases
    case 1
    then show ?thesis 
      by (metis Cons.hyps adef nominalsNSNP.simps(2) union_member)
  next
    case 2
    consider "member n nsm" | "n = nm" | "member n (nominalsForm pm)" 
      by (metis "2" ListSet.member.simps(1) ListSet.member.simps(2) add_def madef 
          nominalsNSNP.simps(1) nominalsNSNP.simps(2) union_member)
    then show ?thesis 
    proof cases
      case 1
      then show ?thesis
        by (smt (verit, ccfv_threshold) ListSet.member.simps(2) Pair_inject add_def adef 
            list.inject madef member_mergeNS mergeNSNP.simps(2) nominalsNSNP.simps(2) union_member)
    next
      case 2
      then show ?thesis 
        by (smt (verit, best) ListSet.member.simps(2) add_def adef madef mergeNSNP.simps(2) 
            nominalsNSNP.simps(2) nth_Cons_0 old.prod.inject union_member)
    next
      case 3
      then show ?thesis 
        by (smt (verit) ListSet.member.simps(2) Pair_inject add_def adef list.inject madef 
            member_mergeP mergeNSNP.simps(2) nominalsNSNP.simps(2) union_member)
    qed
  qed
qed


lemma sub_setNSNP: \<open>
  member n2 (nominalsNSNP nsnp) \<Longrightarrow> 
    sub_set (nominalsNSNP (mergeNSNP nsnp n1 n2)) (nominalsNSNP nsnp)\<close> 
  apply (induct nsnp)
   apply simp
  using member_mergeNSNP by blast

lemma merge_equal: \<open>set_equal ns ms \<Longrightarrow> set_equal (mergeNS ns n1 n2) (mergeNS ms n1 n2)\<close> 
  by simp

lemma merge_union: \<open>set_equal (mergeNS ns n1 n2 U mergeNS ms n1 n2) (mergeNS (ns U ms) n1 n2)\<close> 
proof (induct ns)
  case Nil
  have "set_equal (mergeNS [] n1 n2 U mergeNS ms n1 n2) ([] U mergeNS ms n1 n2)" 
    by simp
  moreover have \<open>set_equal ... (mergeNS ([] U ms) n1 n2)\<close> 
    by (metis merge_equal set_equal_iff unionaddnt)
  ultimately show ?case 
    by auto
next
  case (Cons n ns)
  show ?case 
  proof cases
    assume a:\<open>n = n1\<close>
    then have \<open>
      set_equal (mergeNS (n # ns) n1 n2 U mergeNS ms n1 n2) 
        ((n2 # mergeNS ns n1 n2) U mergeNS ms n1 n2)\<close> 
      by simp
    moreover have \<open>set_equal ... (add n2 (mergeNS ns n1 n2 U mergeNS ms n1 n2))\<close> 
      by (metis set_equal_append_add set_equal_iff union_simp unionadd1)
    moreover have \<open>set_equal ... (add n2 (mergeNS (ns U ms) n1 n2))\<close> 
      using Cons by (meson equal_add)
    moreover have \<open>set_equal ... (n2 # mergeNS (ns U ms) n1 n2)\<close> 
      by (meson set_equal_append_add set_equal_commutative)
    moreover have \<open>set_equal ... (mergeNS (n # (ns U ms)) n1 n2)\<close> 
      using a by simp
    moreover have \<open>set_equal ... (mergeNS ((n # ns) U ms) n1 n2)\<close> 
      by (metis merge_equal set_equal_append_add set_equal_iff union_simp unionadd1)
    ultimately show ?thesis 
      by simp
  next
    assume a:\<open>n \<noteq> n1\<close>
    then have \<open>
      set_equal (mergeNS (n # ns) n1 n2 U mergeNS ms n1 n2) 
        ((n # mergeNS ns n1 n2) U mergeNS ms n1 n2)\<close> 
      by simp
    moreover have \<open>set_equal ... (add n (mergeNS ns n1 n2 U mergeNS ms n1 n2))\<close> 
      by (metis set_equal_append_add set_equal_iff union_simp unionadd1)
    moreover have \<open>set_equal ... (add n (mergeNS (ns U ms) n1 n2))\<close> 
      using Cons by (meson equal_add)
    moreover have \<open>set_equal ... (n # mergeNS (ns U ms) n1 n2)\<close> 
      by (meson set_equal_append_add set_equal_commutative)
    moreover have \<open>set_equal ... (mergeNS (n # (ns U ms)) n1 n2)\<close> 
      using a by simp
    moreover have \<open>set_equal ... (mergeNS ((n # ns) U ms) n1 n2)\<close> 
      by (metis merge_equal set_equal_append_add set_equal_iff union_simp unionadd1)
    ultimately show ?thesis 
      by simp
  qed
qed 

lemma member_mergeNA2:"
  member n (nominalsNA ns) \<Longrightarrow> n \<noteq> n1 \<Longrightarrow> member n (nominalsNA (mergeNA ns n1 n2))" 
  apply (induct ns)
   apply simp
  by (smt (verit) ListSet.member.simps(2) Pair_inject add_def list.distinct(1) list.inject 
      mergeNA.elims nominalsNA.elims)

lemma member_mergeNA3:\<open>
  member n (nominalsNA ns) \<Longrightarrow> n = n1 \<Longrightarrow> member n2 (nominalsNA (mergeNA ns n1 n2))\<close> 
  apply (induct ns)
   apply simp
  by (smt (verit) ListSet.member.simps(2) Pair_inject add_def list.distinct(1) list.inject 
      mergeNA.elims nominalsNA.elims)

lemma merge_nomNA: \<open>set_equal (mergeNS (nominalsNA na) n1 n2) (nominalsNA (mergeNA na n1 n2))\<close> 
proof (induct na)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a na)
  obtain n p where adef:\<open>a = (n,p)\<close> 
    using prod.exhaust_sel by blast
  show ?case 
  proof cases
    assume a:\<open>n = n1\<close>
    show ?thesis 
    proof cases
      assume \<open>member n (nominalsNA na)\<close>
      then show ?thesis 
        by (smt (verit) Cons.hyps a add_def adef member_mergeNA3 mergeNA.simps(2) 
            nominalsNA.simps(2))
    next
      assume a2:\<open>\<not>member n (nominalsNA na)\<close>
      then have \<open>mergeNS (nominalsNA (a # na)) n1 n2 = mergeNS (n # (nominalsNA na)) n1 n2\<close>
        by (metis add_def adef nominalsNA.simps(2))
      moreover have \<open>... = n2 # (mergeNS (nominalsNA na) n1 n2)\<close> 
        by (simp add: a)
      ultimately show ?thesis 
        using Cons.hyps adef by force
    qed
  next
    assume a:\<open>n \<noteq> n1\<close>
    show ?thesis 
    proof cases
      assume \<open>member n (nominalsNA na)\<close>
      then show ?thesis 
        by (smt (verit, ccfv_SIG) Cons.hyps a add_def adef member_mergeNA2 
            mergeNA.simps(2) nominalsNA.simps(2))
    next
      assume a2:\<open>\<not>member n (nominalsNA na)\<close>
      then have "mergeNS (nominalsNA (a # na)) n1 n2 = mergeNS (n # nominalsNA na) n1 n2" 
        by (simp add: add_def adef)
      moreover have "... = n # mergeNS (nominalsNA na) n1 n2" 
        by (simp add: a)
      ultimately show ?thesis
        using Cons.hyps a adef by force
    qed
  qed
qed

lemma member_mergeNN2:"
  member n (nominalsNN ns) \<Longrightarrow> n \<noteq> n1 \<Longrightarrow> member n (nominalsNN (mergeNN ns n1 n2))" 
  apply (induct ns)
   apply simp
  by (smt (verit) ListSet.member.simps(2) Pair_inject add_def list.distinct(1) list.inject 
      mergeNN.elims nominalsNN.elims)

lemma member_mergeNN3:\<open>
  member n (nominalsNN ns) \<Longrightarrow> n = n1 \<Longrightarrow> member n2 (nominalsNN (mergeNN ns n1 n2))\<close> 
  apply (induct ns)
   apply simp
  by (smt (verit) ListSet.member.simps(2) Pair_inject add_def list.distinct(1) list.inject 
      mergeNN.elims nominalsNN.elims)

lemma add_mergeNN:\<open>
  n = n1 \<Longrightarrow> set_equal (mergeNS (add n ns) n1 n2) (add n2 (mergeNS ns n1 n2))\<close> (is "?L \<Longrightarrow> ?R")
proof-
  assume a:\<open>?L\<close>
  have "set_equal (mergeNS (add n ns) n1 n2) (mergeNS (n # ns) n1 n2)" 
    by (meson merge_equal set_equal_append_add set_equal_commutative)
  moreover have \<open>... = n2 # mergeNS ns n1 n2\<close> 
    by (simp add: a)
  ultimately show \<open>?R\<close>
    by (metis set_equal_append_add set_equal_iff)
qed

lemma add_mergeNN2:\<open>
  n \<noteq> n1 \<Longrightarrow> set_equal (mergeNS (add n ns) n1 n2) (add n (mergeNS ns n1 n2))\<close> (is "?L \<Longrightarrow> ?R")
proof-
  assume a:\<open>?L\<close>
  have "set_equal (mergeNS (add n ns) n1 n2) (mergeNS (n # ns) n1 n2)" 
    by (meson merge_equal set_equal_append_add set_equal_commutative)
  moreover have \<open>... = n # mergeNS ns n1 n2\<close> 
    by (simp add: a)
  ultimately show "?R" 
    by (metis set_equal_append_add set_equal_iff)
qed

lemma merge_nomNN: \<open>set_equal (mergeNS (nominalsNN nn) n1 n2) (nominalsNN (mergeNN nn n1 n2))\<close> 
proof (induct nn)
  case Nil
  then show ?case by simp
next
  case (Cons a nn)
  obtain na nb where adef: \<open>a = (na,nb)\<close> 
    using prod.exhaust_sel by blast
  consider "na = n1 \<and> nb = n1" | "na = n1 \<and> nb \<noteq> n1" | "na \<noteq> n1 \<and> nb = n1" | "na \<noteq> n1 \<and> nb \<noteq> n1" 
    by auto
  then show ?case 
  proof cases
    case 1
    then have "mergeNN (a # nn) n1 n2 = (n2,n2) # mergeNN nn n1 n2" 
      by (simp add: adef)
    then have 11:\<open>nominalsNN (mergeNN (a # nn) n1 n2) = add n2 (nominalsNN (mergeNN nn n1 n2))\<close> 
      by (metis ListSet.member.simps(2) add_def nominalsNN.simps(2))
    have \<open>nominalsNN (a # nn) = add n1 (nominalsNN nn)\<close> 
      by (metis "1" ListSet.member.simps(2) add_def adef nominalsNN.simps(2))
    then have 12:\<open>
      set_equal (mergeNS (nominalsNN (a # nn)) n1 n2) (add n2 (mergeNS (nominalsNN nn) n1 n2))\<close>
      by (metis add_mergeNN)
    then have "set_equal ... (add n2 (nominalsNN (mergeNN nn n1 n2)))" 
      by (meson Cons.hyps equal_add)
    then show ?thesis 
      using 11 12 by force
  next
    case 2
    then have "mergeNN (a # nn) n1 n2 = (n2,nb) # mergeNN nn n1 n2" 
      by (simp add: adef)
    then have \<open>
      nominalsNN (mergeNN (a # nn) n1 n2) = add n2 (add nb (nominalsNN (mergeNN nn n1 n2)))\<close> 
      by (metis nominalsNN.simps(2))
    moreover have \<open>
      set_equal ... 
        (add n2 (add nb (mergeNS (nominalsNN nn) n1 n2)))\<close> 
      by (meson Cons.hyps equal_add set_equal_commutative)
    moreover have "
      set_equal ... (add n2 (mergeNS (add nb (nominalsNN nn)) n1 n2))" 
      by (meson "2" add_mergeNN2 equal_add set_equal_commutative)
    ultimately show ?thesis 
      by (metis "2" add_mergeNN adef nominalsNN.simps(2) set_equal_iff)
  next
    case 3
    then have "mergeNN (a # nn) n1 n2 = (na,n2) # mergeNN nn n1 n2" 
      by (simp add: adef)
    then have \<open>
      nominalsNN (mergeNN (a # nn) n1 n2) = add na (add n2 (nominalsNN (mergeNN nn n1 n2)))\<close> 
      by (metis nominalsNN.simps(2))
    moreover have \<open>set_equal ... (add na (add n2 (mergeNS (nominalsNN nn) n1 n2))) \<close> 
      by (meson Cons.hyps equal_add set_equal_commutative)
    moreover have \<open>set_equal ... (add na (mergeNS (add n1 (nominalsNN nn)) n1 n2))\<close> 
      by (meson add_mergeNN equal_add set_equal_commutative)
    ultimately show ?thesis 
      by (metis "3" add_mergeNN2 adef nominalsNN.simps(2) set_equal_iff)
  next
    case 4
    then have "mergeNN (a # nn) n1 n2 = (na,nb) # mergeNN nn n1 n2" 
      by (simp add: adef)
    then have \<open>
      nominalsNN (mergeNN (a # nn) n1 n2) = add na (add nb (nominalsNN (mergeNN nn n1 n2)))\<close> 
      by (metis nominalsNN.simps(2))
    moreover have \<open>set_equal ... (add na (add nb (mergeNS (nominalsNN nn) n1 n2))) \<close> 
      by (meson Cons.hyps equal_add set_equal_commutative)
    moreover have \<open>set_equal ... (add na (mergeNS (add nb (nominalsNN nn)) n1 n2))\<close> 
      by (meson "4" add_mergeNN2 equal_add set_equal_commutative)
    ultimately show ?thesis 
      by (metis "4" add_mergeNN2 adef nominalsNN.simps(2) set_equal_iff)
  qed
qed

lemma merge_nomP: \<open>set_equal (mergeNS (nominalsForm p) n1 n2) (nominalsForm (mergeP p n1 n2))\<close>
proof (induct p)
  case (Con p1 p2)
  have \<open>
    set_equal (mergeNS (nominalsForm (p1 AND p2)) n1 n2) 
      (mergeNS (nominalsForm p1 U nominalsForm p2) n1 n2)\<close> 
    by simp
  moreover have \<open>set_equal ... (mergeNS (nominalsForm p1) n1 n2 U mergeNS (nominalsForm p2) n1 n2)\<close> 
    by (meson merge_union set_equal_commutative)
  moreover have \<open>set_equal ... (nominalsForm (mergeP p1 n1 n2) U nominalsForm (mergeP p2 n1 n2))\<close>
    by (meson Con.hyps(1) Con.hyps(2) double_union_equal)
  ultimately show ?case 
    by (metis mergeP.simps(4) nominalsForm.simps(4) set_equal_iff)
next
  case (Sat n p)
  then show ?case 
    by (smt (verit, ccfv_SIG) add_mergeNN add_mergeNN2 equal_add mergeP.simps(5) 
        nominalsForm.simps(5) set_equal_iff)
qed auto
 
lemma merge_nomNP: \<open>set_equal (mergeNS (nominalsNP np) n1 n2) (nominalsNP (mergeNP np n1 n2))\<close> 
proof (induct np)
  case Nil
  then show ?case by simp
next
  case (Cons a np)
  obtain n p where adef:\<open>a = (n,p)\<close> 
    by (meson prod.exhaust_sel)
  then have \<open>
    mergeNS (nominalsNP (a # np)) n1 n2 = (mergeNS (add n (nominalsForm p U nominalsNP np)) n1 n2)\<close>
    (is \<open>?mnL = ?mnR\<close>)
    using adef by simp
  show ?case 
  proof cases
    assume a:\<open>n = n1\<close>
    then have \<open>set_equal ?mnR (add n2 (mergeNS (nominalsForm p U nominalsNP np) n1 n2))\<close> 
      by (metis add_mergeNN)
    moreover have \<open>
      set_equal ... (add n2 (mergeNS (nominalsForm p) n1 n2 U mergeNS (nominalsNP np) n1 n2))\<close>
      by (meson equal_add merge_union set_equal_commutative)
    moreover have \<open>
      set_equal ... (add n2 (nominalsForm (mergeP p n1 n2) U nominalsNP (mergeNP np n1 n2)))\<close> 
      by (meson Cons.hyps double_union_equal equal_add merge_nomP)
    ultimately show ?thesis 
      by (simp add: a adef)
  next
    assume a:\<open>n \<noteq> n1\<close>
    then have \<open>set_equal ?mnR (add n (mergeNS (nominalsForm p U nominalsNP np) n1 n2))\<close> 
      by (meson add_mergeNN2)
    moreover have \<open>
      set_equal ... (add n (mergeNS (nominalsForm p) n1 n2 U mergeNS (nominalsNP np) n1 n2))\<close>
      by (meson equal_add merge_union set_equal_commutative)
    moreover have \<open>
      set_equal ... (add n (nominalsForm (mergeP p n1 n2) U nominalsNP (mergeNP np n1 n2)))\<close> 
      by (meson Cons.hyps double_union_equal equal_add merge_nomP)
    ultimately show ?thesis 
      by (simp add: a adef)
  qed
qed

lemma merge_nomNSNP: \<open>set_equal (mergeNS (nominalsNSNP nsnp) n1 n2) (nominalsNSNP (mergeNSNP nsnp n1 n2))\<close> 
proof (induct nsnp)
  case Nil
  then show ?case by simp
next
  case (Cons a nsnp)
  obtain ns n p where adef: \<open>a = (n,ns,p)\<close> 
    using prod_cases3 by blast
  then have 1:\<open>
    mergeNS (nominalsNSNP (a # nsnp)) n1 n2 = 
      mergeNS (nominalsNSNP nsnp U add n (ns U nominalsForm p)) n1 n2\<close>
    by simp
  have 2:\<open>
    set_equal ... (mergeNS (nominalsNSNP nsnp) n1 n2 U mergeNS (add n (ns U nominalsForm p)) n1 n2)\<close>
    (is \<open>set_equal ?mnL ?mnR\<close>)
    by (meson merge_union set_equal_commutative)
  show ?case 
  proof cases
    assume a:"n = n1"
    then have \<open>
      set_equal ?mnR (nominalsNSNP (mergeNSNP nsnp n1 n2) U 
        add n2 (mergeNS (ns U nominalsForm p) n1 n2))\<close> 
      by (metis Cons.hyps  add_mergeNN double_union_equal)
    moreover have \<open>
      set_equal ... (nominalsNSNP (mergeNSNP nsnp n1 n2) U 
        add n2 (mergeNS ns n1 n2 U mergeNS (nominalsForm p) n1 n2))\<close> 
      by (metis equal_add merge_union set_equal_commutative union_with_equal)
    moreover have \<open>
      set_equal ... (nominalsNSNP (mergeNSNP nsnp n1 n2) U 
        add n2 (mergeNS ns n1 n2 U nominalsForm (mergeP p n1 n2)))\<close> 
      by (meson equal_add merge_nomP union_with_equal)
    ultimately show ?thesis 
      using "2" a adef by force
  next
    assume a:"n \<noteq> n1"
    then have \<open>
      set_equal ?mnR (nominalsNSNP (mergeNSNP nsnp n1 n2) U 
        add n (mergeNS (ns U nominalsForm p) n1 n2))\<close> 
      by (meson Cons.hyps add_mergeNN2 double_union_equal)
    moreover have \<open>
      set_equal ... (nominalsNSNP (mergeNSNP nsnp n1 n2) U 
        add n (mergeNS ns n1 n2 U mergeNS (nominalsForm p) n1 n2))\<close> 
      by (metis equal_add merge_union set_equal_commutative union_with_equal)
    moreover have \<open>
      set_equal ... (nominalsNSNP (mergeNSNP nsnp n1 n2) U 
        add n (mergeNS ns n1 n2 U nominalsForm (mergeP p n1 n2)))\<close> 
      by (meson equal_add merge_nomP union_with_equal)
    ultimately show ?thesis 
      using "2" a adef by force
  qed
qed

lemma merge_noms: \<open>
  set_equal 
    (mergeNS (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U 
      nominalsNSNP R U nominalsNP Q) n1 n2) 
    (nominalsNA (mergeNA LA n1 n2) U nominalsNA (mergeNA RA n1 n2) U nominalsNN (mergeNN RN n1 n2) U
      nominalsNN (mergeNN LP n1 n2) U nominalsNN (mergeNN RP n1 n2) U 
      nominalsNSNP (mergeNSNP R n1 n2) U nominalsNP (mergeNP Q n1 n2))\<close> 
proof-
  have "
    set_equal (
      nominalsNA (mergeNA LA n1 n2) U nominalsNA (mergeNA RA n1 n2) U 
      nominalsNN (mergeNN RN n1 n2) U nominalsNN (mergeNN LP n1 n2) U 
      nominalsNN (mergeNN RP n1 n2) U nominalsNSNP (mergeNSNP R n1 n2) U 
      nominalsNP (mergeNP Q n1 n2)) (
      nominalsNA (mergeNA LA n1 n2) U nominalsNA (mergeNA RA n1 n2) U 
      nominalsNN (mergeNN RN n1 n2) U nominalsNN (mergeNN LP n1 n2) U 
      nominalsNN (mergeNN RP n1 n2) U nominalsNSNP (mergeNSNP R n1 n2) U 
      mergeNS (nominalsNP Q) n1 n2)" 
    by (metis merge_nomNP set_equal_commutative union_with_equal)
  moreover have "
    set_equal ... (
      nominalsNA (mergeNA LA n1 n2) U nominalsNA (mergeNA RA n1 n2) U 
      nominalsNN (mergeNN RN n1 n2) U nominalsNN (mergeNN LP n1 n2) U 
      nominalsNN (mergeNN RP n1 n2) U mergeNS (nominalsNSNP R) n1 n2 U 
      mergeNS (nominalsNP Q) n1 n2)" 
    by (metis merge_nomNSNP set_equal_commutative union_with_equal union_with_equal2)
  moreover have "
    set_equal ... (
      nominalsNA (mergeNA LA n1 n2) U nominalsNA (mergeNA RA n1 n2) U 
      nominalsNN (mergeNN RN n1 n2) U nominalsNN (mergeNN LP n1 n2) U 
      mergeNS (nominalsNN RP) n1 n2 U mergeNS (nominalsNSNP R) n1 n2 U 
      mergeNS (nominalsNP Q) n1 n2)"
    by (meson merge_nomNN set_equal_commutative union_with_equal union_with_equal2)
  moreover have "
    set_equal ... (
      nominalsNA (mergeNA LA n1 n2) U nominalsNA (mergeNA RA n1 n2) U 
      nominalsNN (mergeNN RN n1 n2) U mergeNS (nominalsNN LP) n1 n2 U 
      mergeNS (nominalsNN RP) n1 n2 U mergeNS (nominalsNSNP R) n1 n2 U 
      mergeNS (nominalsNP Q) n1 n2)" 
    by (meson merge_nomNN set_equal_commutative union_with_equal union_with_equal2)
  moreover have "
    set_equal ... (
      nominalsNA (mergeNA LA n1 n2) U nominalsNA (mergeNA RA n1 n2) U
      mergeNS (nominalsNN RN) n1 n2 U mergeNS (nominalsNN LP) n1 n2 U 
      mergeNS (nominalsNN RP) n1 n2 U mergeNS (nominalsNSNP R) n1 n2 U 
      mergeNS (nominalsNP Q) n1 n2)" 
    by (meson merge_nomNN set_equal_commutative union_with_equal union_with_equal2)
  moreover have "
    set_equal ... (
      nominalsNA (mergeNA LA n1 n2) U mergeNS (nominalsNA RA) n1 n2 U
      mergeNS (nominalsNN RN) n1 n2 U mergeNS (nominalsNN LP) n1 n2 U 
      mergeNS (nominalsNN RP) n1 n2 U mergeNS (nominalsNSNP R) n1 n2 U 
      mergeNS (nominalsNP Q) n1 n2)" 
    by (meson merge_nomNA set_equal_commutative union_with_equal union_with_equal2)
  moreover have "
    set_equal ... (
      mergeNS (nominalsNA LA) n1 n2 U mergeNS (nominalsNA RA) n1 n2 U 
      mergeNS (nominalsNN RN) n1 n2 U mergeNS (nominalsNN LP) n1 n2 U 
      mergeNS (nominalsNN RP) n1 n2 U mergeNS (nominalsNSNP R) n1 n2 U 
      mergeNS (nominalsNP Q) n1 n2)" 
    by (meson merge_nomNA set_equal_commutative union_with_equal union_with_equal2)
  moreover have \<open>set_equal ... (mergeNS (nominalsNA LA) n1 n2 U mergeNS (nominalsNA RA) n1 n2 U 
      mergeNS (nominalsNN RN) n1 n2 U mergeNS (nominalsNN LP) n1 n2 U 
      mergeNS (nominalsNN RP) n1 n2 U mergeNS (nominalsNSNP R U nominalsNP Q) n1 n2)\<close> 
    by (meson merge_union union_with_equal)
  moreover have \<open>set_equal ... (mergeNS (nominalsNA LA) n1 n2 U mergeNS (nominalsNA RA) n1 n2 U 
      mergeNS (nominalsNN RN) n1 n2 U mergeNS (nominalsNN LP) n1 n2 U 
      mergeNS (nominalsNN RP U nominalsNSNP R U nominalsNP Q) n1 n2)\<close>
    by (meson merge_union union_with_equal)
  moreover have \<open>set_equal ... (mergeNS (nominalsNA LA) n1 n2 U mergeNS (nominalsNA RA) n1 n2 U 
      mergeNS (nominalsNN RN) n1 n2 U 
      mergeNS (nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q) n1 n2)\<close>
    by (meson merge_union union_with_equal)
  moreover have \<open>set_equal ... (mergeNS (nominalsNA LA) n1 n2 U mergeNS (nominalsNA RA) n1 n2 U 
      mergeNS (nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U 
      nominalsNP Q) n1 n2)\<close>
    by (meson merge_union union_with_equal)
  moreover have \<open>set_equal ... (mergeNS (nominalsNA LA) n1 n2 U 
      mergeNS (nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U 
      nominalsNP Q) n1 n2)\<close>
    by (meson merge_union union_with_equal)
  moreover have \<open>set_equal ... (mergeNS (nominalsNA LA U nominalsNA RA U nominalsNN RN U 
      nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q) n1 n2)\<close>
    by (meson merge_union union_with_equal)
  ultimately show ?thesis 
    by simp
qed

lemma nominals_con: \<open>
  R = R1 @ R2 \<Longrightarrow> set_equal (nominalsNSNP R) (nominalsNSNP R1 U nominalsNSNP R2)\<close> 
proof (induct R1 arbitrary: R)
  case Nil
  then show ?case 
    by (metis nominalsNSNP.simps(1) self_append_conv2 set_equal_commutative unionaddnt)
next
  case (Cons a R1)
  obtain n ns p where adef:\<open>a = (n,ns,p)\<close>
    using prod_cases3 by blast
  obtain R' where Rdef:\<open>R' = R1 @ R2\<close> 
    by simp
  have \<open>set_equal (nominalsNSNP R) (add n (ns U nominalsForm p) U nominalsNSNP R')\<close> 
    by (metis Cons.prems Rdef adef append_Cons nominalsNSNP.simps(2) union_commutative)
  moreover have \<open>set_equal (nominalsNSNP R') (nominalsNSNP R1 U nominalsNSNP R2)\<close> 
    using Cons.hyps Rdef by auto
  ultimately have 1:\<open>
    set_equal (nominalsNSNP R) (add n (ns U nominalsForm p) U (nominalsNSNP R1 U nominalsNSNP R2))\<close> 
    by (meson set_equal_associative union_with_equal)
  have \<open>set_equal (nominalsNSNP (a # R1)) (nominalsNSNP R1 U add n (ns U nominalsForm p))\<close>
    using adef by simp
  moreover have \<open>set_equal ... (add n (ns U nominalsForm p) U nominalsNSNP R1)\<close> 
    by (meson union_commutative)
  ultimately have \<open>set_equal (nominalsNSNP (a # R1) U nominalsNSNP R2) 
    ((add n (ns U nominalsForm p) U nominalsNSNP R1) U nominalsNSNP R2)\<close> 
    by (meson set_equal_associative union_with_equal2)
  moreover have \<open>set_equal ...
    (add n (ns U nominalsForm p) U (nominalsNSNP R1 U nominalsNSNP R2))\<close> 
    by (meson set_equal_associative set_equal_commutative union_associative union_with_equal)
  ultimately show ?case 
    using "1" by auto
qed
(*
functions for finding possibility formulas that has not been tried with one of the existing
nominals yet
See last case of atomize for use
*)

(*
In saturate' we return one R with the matching element removed, and one with the found nominal 
added to the matching element.
The first represents that the formula has been discharged, and should not be included further.
  This is used when testing if the discharge made the sequent valid
The second is to attempt a discharge with other nominals, but avoid using the same nominal twice.
*)
fun saturate' where
  \<open>saturate' R' [] ns = None\<close> |
  \<open>saturate' R' ((n,ms,p) # R) ns = (
    case remove ns ms of
      []      \<Rightarrow> saturate' (R' @ [(n,ms,p)]) R ns
    | (m # _) \<Rightarrow> Some (n,m,p,R' @ R,R' @ [(n,m # ms,p)] @ R))\<close>

abbreviation saturate where \<open>saturate R ns \<equiv> saturate' [] R ns\<close>

lemma sat_empty: \<open>saturate [] ns = None\<close>
  by (simp)

lemma sat_findnt1: \<open>(\<forall> n ms p. member (n,ms,p) R \<longrightarrow> remove ns ms = []) \<longrightarrow> saturate R ns = None\<close>
proof (induct R ns rule: saturate'.induct)
  case (1 R' ns)
  then show ?case by simp
next
  case (2 R' n ms p R ns)
  assume 1: "(remove ns ms = [] \<Longrightarrow>
             (\<forall>n ms p. member (n, ms, p) R \<longrightarrow> remove ns ms = []) \<longrightarrow>
              saturate' (R' @ [(n, ms, p)]) R ns = None)"
  have "(\<forall>na msa pa. member (na, msa, pa) ((n, ms, p) # R) \<longrightarrow> remove ns msa = []) \<Longrightarrow>
        saturate' R' ((n, ms, p) # R) ns = None" 
  proof-
    assume 2: "\<forall>na msa pa. member (na, msa, pa) ((n, ms, p) # R) \<longrightarrow> remove ns msa = []"
    then have "remove ns ms = []" 
      by (meson member.simps(2))
    from this 1 have "(\<forall>n ms p. member (n, ms, p) R \<longrightarrow> remove ns ms = []) \<longrightarrow>
                       saturate' (R' @ [(n, ms, p)]) R ns = None" by simp
    from this 2 have 3:"saturate' (R' @ [(n, ms, p)]) R ns = None" 
      by (meson member.simps(2))
    have 4: "remove ns ms = [] \<Longrightarrow> 
          saturate' R' ((n, ms, p) # R) ns = saturate' (R' @ [(n, ms, p)])  R ns"
      by simp
    then show "saturate' R' ((n, ms, p) # R) ns = None" using 3 4 
      by (simp add: \<open>remove ns ms = []\<close>)
  qed
  then show ?case by simp
qed 

lemma sat_findnt2: \<open>saturate R ns = None \<longrightarrow> (\<forall> n ms p. member (n,ms,p) R \<longrightarrow> remove ns ms = [])\<close>
proof (induct R ns rule: saturate'.induct)
case (1 R' ns)
then show ?case by simp
next
  case (2 R' n ms p R ns)
  assume 1:\<open>remove ns ms = [] \<Longrightarrow>
        saturate' (R' @ [(n, ms, p)]) R ns = None \<longrightarrow>
        (\<forall>n ms p. member (n, ms, p) R \<longrightarrow> remove ns ms = [])\<close>
  have \<open>saturate' R' ((n, ms, p) # R) ns = None \<longrightarrow>
       (\<forall>na msa pa. member (na, msa, pa) ((n, ms, p) # R) \<longrightarrow> remove ns msa = [])\<close>
  proof 
    assume 2: \<open>saturate' R' ((n, ms, p) # R) ns = None\<close>
    have 3: "remove ns ms = [] \<Longrightarrow>
          saturate' R' ((n, ms, p) # R) ns = saturate' (R' @ [(n, ms, p)]) R ns" by simp
    have 4 :"remove ns ms = []" 
    proof (rule ccontr)
      assume "\<not> remove ns ms = []"
      then have "\<exists> m y. remove ns ms = m # y" 
        by (meson list.exhaust)
      then obtain m y where "remove ns ms = m # y" 
        by (meson)
      then have "\<exists> C. saturate' R' ((n, ms, p) # R) ns = Some C" by simp
      then show "False" using 2 by simp
    qed
    from 1 this have "saturate' (R' @ [(n, ms, p)]) R ns = None \<longrightarrow>
        (\<forall>n ms p. member (n, ms, p) R \<longrightarrow> remove ns ms = [])" by simp
    then show \<open>(\<forall>na msa pa. member (na, msa, pa) ((n, ms, p) # R) \<longrightarrow> remove ns msa = [])\<close> 
      using 2 3 4 by (metis member.simps(2) Pair_inject)
  qed
  then show ?case by simp
qed

lemma sat_iff[iff]: "(\<forall> n ms p. member (n,ms,p) R \<longrightarrow> remove ns ms = []) \<longleftrightarrow> saturate R ns = None"
  using sat_findnt1 sat_findnt2 by blast

hide_fact sat_findnt1 sat_findnt2

lemma sat_R1: "
  saturate' R' R ns = Some (n,m,p,R1,R2) \<longrightarrow> 
  (\<exists> y. R1 = R' @ y) \<and> (\<exists> y. R2 = R' @ y)"
proof (induct R arbitrary: n m p R' R1 R2)
  case Nil
  then show ?case by simp
next
  fix a R n m p ns R' R1 R2
  assume a1: "(
    \<And>n m p R' R1 R2.
      saturate' R' R ns = Some (n, m, p, R1, R2) \<longrightarrow>
      (\<exists>y. R1 = R' @ y) \<and> (\<exists>y. R2 = R' @ y)) "
  show "
    saturate' R' (a # R) ns = Some (n, m, p, R1, R2) \<longrightarrow>
    (\<exists>y. R1 = R' @ y) \<and> (\<exists>y. R2 = R' @ y)"
  proof
    assume a2: "saturate' R' (a # R) ns = Some (n, m, p, R1, R2)"
    then have "\<exists> n' ms p'. a = (n',ms,p')"
      by (meson prod_cases3)
    then obtain n' ms p' where adef: "a = (n',ms,p')"
      by blast
    then show "(\<exists>y. R1 = R' @ y) \<and> (\<exists>y. R2 = R' @ y)" 
    proof cases
      assume "remove ns ms = []"
      then have "saturate' (R' @ [a]) R ns = Some (n, m, p, R1, R2)" using adef a2 
        by simp
      then show ?thesis 
        using append.assoc a1 by blast
    next
      assume "\<not> remove ns ms = []"
      then have "\<exists>m' y. remove ns ms = m' # y" 
        by (metis list.distinct(1) list.inject transpose.cases)
      then show ?thesis using adef a2 by auto
    qed
  qed
qed

lemma addnt1: "
  saturate' R'' R ns = Some (n,m,p,R'' @ R1,R'' @ R2) \<Longrightarrow>
  saturate' (R' @ R'') R ns = Some (n,m,p,R' @ R'' @ R1, R' @ R'' @ R2)"
proof (induct R arbitrary: R'' R' n m p R1 R2)
  case Nil
  then show ?case by simp
next
  fix a R R' R'' n m p R1 R2
  assume a1: "
    \<And>R'' R' n m p R1 R2.
      saturate' R'' R ns = Some (n, m, p, R'' @ R1, R'' @ R2) \<Longrightarrow>
      saturate' (R' @ R'') R ns =
      Some (n, m, p, R' @ R'' @ R1, R' @ R'' @ R2)"
  then show "
    saturate' R'' (a # R) ns = Some (n, m, p, R'' @ R1, R'' @ R2) \<Longrightarrow>
    saturate' (R' @ R'') (a # R) ns =
      Some (n, m, p, R' @ R'' @ R1, R' @ R'' @ R2)" 
  proof-
    assume a2: "
      saturate' R'' (a # R) ns = Some (n, m, p, R'' @ R1, R'' @ R2)"
    then have "\<exists> n' ms p'. a = (n',ms,p')"
      by (meson prod_cases3)
    then obtain n' ms p' where adef: "a = (n',ms,p')"
      by blast
    show ?thesis 
    proof cases
      assume a3: "remove ns ms = []"
      from this adef have 1: "saturate' (R'') (a # R) ns = saturate' (R'' @ [a]) R ns" by simp
      from this a2 have "
        \<exists> y z. R1 = a # y \<and> R2 = a # z"
        by (smt (z3) append_Cons append_assoc append_eq_append_conv sat_R1)
      then obtain y z where yzdef: "R1 = a # y \<and> R2 = a # z" by blast
      from this a2 1 have "
        saturate' (R'' @ [a]) R ns = Some (n, m, p, R'' @ [a] @ y,R'' @ [a] @ z)"
        by simp
      from this a1 have 2:"
        saturate' (R' @ R'' @ [a]) R ns = Some (n, m, p, R' @ R'' @ [a] @ y, R' @ R'' @ [a] @ z)"
        by simp
      from a3 adef have "
        saturate' (R' @ R'' @ [a]) R ns = saturate' (R' @ R'') (a # R) ns"
        by simp
      then show ?thesis 
        by (simp add: yzdef 2)
    next
      assume "\<not>remove ns ms = []"
      then have \<open>\<exists> m ms'. remove ns ms = m # ms'\<close> 
        by (meson list.exhaust)
      then obtain m' ms' where nsms: \<open>remove ns ms = m' # ms'\<close> by blast
      from this adef a2 have 1:\<open>n = n' \<and> m = m' \<and> p = p' \<and> R1 = R \<and> R2 = (n',m' # ms,p') # R\<close>
        by auto
      from this adef nsms have "
        saturate' (R' @ R'') (a # R) ns = 
          Some (n,m,p,R' @ R'' @ R, R' @ R'' @ [(n',m' # ms,p')] @ R)" 
        by simp
      then show ?thesis 
        by (simp add: 1)
    qed
  qed
qed

lemma addnt2: \<open>
  saturate' R1 R ns = Some (n,m,p,R1 @ R', R1 @ R'') \<Longrightarrow> saturate R ns = Some (n,m,p,R',R'')\<close>
proof (induct R arbitrary: n m p R' R'' R1)
  case Nil
  then show ?case by simp
next
  fix a R n m p R' R'' R1
  assume a1: "(
    \<And>n m p R' R'' R1.
      saturate' R1 R ns = Some (n, m, p, R1 @ R', R1 @ R'') \<Longrightarrow>
      saturate R ns = Some (n, m, p, R', R''))"
  show "
    saturate' R1 (a # R) ns = Some (n, m, p, R1 @ R', R1 @ R'') \<Longrightarrow>
    saturate (a # R) ns = Some (n, m, p, R', R'') " 
  proof-
    assume a2: "
      saturate' R1 (a # R) ns = Some (n, m, p, R1 @ R', R1 @ R'')"
    then have "\<exists> n' ms p'. a = (n',ms,p')" 
      by (meson prod_cases3)
    then obtain n' ms p' where adef: "a = (n',ms,p')" by blast
    show ?thesis 
    proof cases
      assume a3: "remove ns ms = []"
      then have 1: "saturate' R1 (a # R) ns = saturate' (R1 @ [a]) R ns" 
        using adef by simp
      from this a2 sat_R1 have "\<exists> R3 R4. R' = a # R3 \<and> R'' = a # R4" 
        by (smt (z3) append_Cons append_assoc same_append_eq)
      then obtain R3 R4 where Rdef: "R' = a # R3 \<and> R'' = a # R4" by blast
      from this 1 a1 a2 have "saturate R ns = Some (n, m, p, R3, R4)" 
        by (smt (verit, best) append_Cons append_assoc 
            append_eq_append_conv append_self_conv2 list.inject sat_R1)
      from this 1 addnt1 have 2:"saturate' [a] R ns = Some (n, m, p, a # R3, a # R4)" 
        by (smt (verit) append_Cons self_append_conv2)
      from a3 adef have "saturate' [a] R ns = saturate' [] (a # R) ns"
        by simp
      then show "saturate (a # R) ns = Some (n, m, p, R', R'')"
        using Rdef 1 2 by auto
    next
      assume "\<not>remove ns ms = []"
      then have "\<exists> m' ms'. remove ns ms = m' # ms'" 
        by (meson list.exhaust)
      then obtain m' ms' where nsms: "remove ns ms = m' # ms'" by blast
      from this adef a2 have 2: \<open>n = n' \<and> m = m' \<and> p = p' \<and> R' = R \<and> R'' = (n',m' # ms,p') # R\<close>
        by auto
      then have "saturate (a # R) ns = Some (n,m,p,R,(n,m' # ms,p) # R)" using adef nsms by simp  
      then show ?thesis using 2 by simp
    qed
  qed
qed 

lemma addnt[iff]: "
  saturate R ns = Some (n,m,p,R1,R2) \<longleftrightarrow> saturate' R' R ns = Some (n,m,p,R' @ R1,R' @ R2)"
  using addnt1 addnt2 
  by (smt (verit, ccfv_SIG) append_Nil2 sat_R1)

hide_fact addnt1 addnt2

lemma saturate_split: \<open>
  saturate' R3 R ns = Some (n,m,p,R',R'') \<Longrightarrow> 
    (\<exists> R1 R2 ms. R' = R1 @ R2 \<and> R3 @ R = R1 @ [(n,ms,p)] @ R2)\<close> 
proof (induct R arbitrary: n m p R' R'' R3)
  case Nil
  then show ?case by simp
next
  case (Cons r R)
  obtain n' ns' p' where rdef: \<open>r = (n',ns',p')\<close> 
    by (meson prod_cases3)
  consider \<open>remove ns ns' = []\<close> | \<open>\<exists> m ms. remove ns ns' = m # ms\<close> 
    by (meson list.exhaust)
  then show ?case 
  proof cases
    case 1
    then have \<open>saturate' R3 (r # R) ns = saturate' (R3 @ [r]) R ns\<close> 
      using rdef by simp
    then show ?thesis 
      by (smt (verit, ccfv_threshold) Cons.hyps Cons.prems append_Cons append_eq_append_conv2 
          append_self_conv)
  next
    case 2
    then obtain m u where \<open>remove ns ns' = m # u\<close> 
      by fast
    then have \<open>saturate' R3 (r # R) ns = Some (n',m,p',R3 @ R,R3 @ [(n',m # ns',p')] @ R)\<close> 
      using rdef by simp
    then have 1:\<open>Some (n, m, p, R', R'') = Some (n',m,p',R3 @ R,R3 @ [(n',m # ns',p')] @ R)\<close> 
      by (simp add: Cons.prems)
    then have \<open>R' = R3 @ R\<close> 
      by simp
    moreover have \<open>R3 @ (r # R) = R3 @ ((n,ns',p) # R)\<close> 
      using "1" rdef by blast
    ultimately show ?thesis 
      by auto
  qed
qed 

lemma saturate_split2: \<open>
  saturate' R3 R ns = Some (n,m,p,R',R'') \<Longrightarrow> 
    (\<exists> R1 R2 ms ms'. R'' = R1 @ [(n,m # ms,p)] @ R2 \<and> R3 @ R = R1 @ [(n,ms,p)] @ R2 \<and> 
      remove ns ms = m # ms')\<close> 
proof (induct R arbitrary: R3)
  case Nil
  then show ?case by simp
next
  case (Cons r R)
  obtain n' ns' p' where rdef: \<open>r = (n',ns',p')\<close> 
    by (meson prod_cases3)
  consider \<open>remove ns ns' = []\<close> | \<open>\<exists> m ms. remove ns ns' = m # ms\<close> 
    by (meson list.exhaust)
  then show ?case 
  proof cases
    case 1
    then have \<open>saturate' R3 (r # R) ns = saturate' (R3 @ [r]) R ns\<close> 
      using rdef by simp
    then show ?thesis 
      by (smt (verit, ccfv_threshold) Cons.hyps Cons.prems append_Cons append_eq_append_conv2 
          append_self_conv)
  next
    case 2
    then obtain m u where mu_def:\<open>remove ns ns' = m # u\<close> 
      by fast
    then have 2:\<open>saturate' R3 (r # R) ns = Some (n',m,p',R3 @ R,R3 @ [(n',m # ns',p')] @ R)\<close> 
      using rdef by simp
    then have 1:\<open>Some (n, m, p, R', R'') = Some (n',m,p',R3 @ R,R3 @ [(n',m # ns',p')] @ R)\<close> 
      by (simp add: Cons.prems)
    then have \<open>R'' = R3 @ [(n',m # ns',p')] @ R\<close> 
      by simp
    moreover have \<open>R3 @ (r # R) = R3 @ ((n,ns',p) # R)\<close> 
      using "1" rdef by blast
    ultimately show ?thesis 
      using Cons.prems 2 mu_def by auto
  qed
qed

lemma saturate_nom_members:\<open>
  saturate' R2 R ns = Some (n,m,p,R',R'') \<Longrightarrow> member n (nominalsNSNP R) \<and> member m ns\<close> 
proof (induct R arbitrary: R2 n m p R' R'')
  case Nil
  then show ?case by simp
next
  case (Cons r R)
  obtain n' ns' p' where rdef:\<open>r = (n',ns',p')\<close> 
    using prod_cases3 by blast 
  consider "remove ns ns' = []" | \<open>\<exists> m ms. remove ns ns' = m # ms\<close> 
    by (meson list.exhaust)
  then show ?case 
  proof cases
    case 1
    then have \<open>saturate' R2 (r # R) ns = saturate' (R2 @ [r]) R ns\<close> 
      using rdef by simp
    then have \<open>... = Some (n, m, p, R', R'')\<close> 
      using Cons.prems by auto
    then have 1:\<open>member n (nominalsNSNP R) \<and> member m ns\<close> 
      using Cons.hyps by auto
    then have \<open>member n (nominalsNSNP (r # R)) \<and> member m ns\<close> 
    proof-
      have \<open>\<exists> r'. nominalsNSNP (r # R) = nominalsNSNP R U r'\<close> 
        by (metis nominalsNSNP.simps(2) prod_cases3)
      then show ?thesis 
        by (metis "1" union_member)
    qed
    then show ?thesis by simp
  next
    case 2
    then obtain m ms where mdef:\<open>remove ns ns' = m # ms\<close>
      by fast
    then have \<open>saturate' R2 (r # R) ns = Some (n',m,p',R2 @ R,R2 @ [(n',m # ns',p')] @ R)\<close> 
      using rdef by simp
    moreover have \<open>member n' (nominalsNSNP (r # R))\<close> 
    proof-
      obtain u where \<open>nominalsNSNP (r # R) = nominalsNSNP R U add n' u\<close>
        by (simp add: rdef)
      then show ?thesis
        by (metis ListSet.member.simps(2) add_def union_member)
    qed
    moreover have \<open>member m ns\<close> 
      by (metis ListSet.member.simps(2) mdef member_sub_set sub_remove_set)
    ultimately show ?thesis 
      by (simp add: Cons.prems) 
  qed
qed

(*Check if any of the pairs in a list contains two of the same element*)
fun reflect where
  \<open>reflect [] = False\<close> |
  \<open>reflect ((n1,n2) # B) = (n1 = n2 \<or> reflect B)\<close>

(*termination functions*)
primrec pos_count where 
  \<open>pos_count (Pro a) = 0\<close> |
  \<open>pos_count (Nom n) = 0\<close> |
  \<open>pos_count (Neg p) = pos_count p\<close> |
  \<open>pos_count (Con p1 p2) = pos_count p1 + pos_count p2\<close> |
  \<open>pos_count (Sat n p) = pos_count p\<close> |
  \<open>pos_count (Pos p) = Suc (pos_count p)\<close>

fun pos_countNP where
  \<open>pos_countNP [] = 0\<close> |                                          
  \<open>pos_countNP ((_,p) # NP) = pos_count p + pos_countNP NP\<close>

fun pos_countNSNP where
  \<open>pos_countNSNP [] = 0\<close> |                                          
  \<open>pos_countNSNP ((_,_,p) # NSNP) = pos_count p + pos_countNSNP NSNP\<close>


fun missing' where
  \<open>missing' ms [] = 0\<close> |
  \<open>missing' ms (n # ns) = (if \<not>member n ms then Suc (missing' ms ns) else missing' ms ns)\<close>

fun missing :: "('a \<times> nat list \<times>'b) list \<Rightarrow> nat list \<Rightarrow> nat" where
  \<open>missing [] ns = 0\<close> |
  \<open>missing ((_,ms,_) # R) ns = missing' ms ns + missing R ns\<close>

(*
----------EXPLANATION OF PARAMETERS OF ATOMIZE---------
All parameters are lists of tuples representing formulas of different types
The first element identifies the nominal at which the formula holds

LA/RA: LHS and RHS atomic non-nominal propositions. Sequent is valid if they share an element

RN: RHS nominal propositions. Sequent is valid if we have @n n. There is no LN because we process 
    them immediately

LP/RP: LHS and RHS possibility relations between nominals. Sequent is valid if they share an element

R: RHS possibility formulas with potentially complex subformulas. Formulas here can be discharged
   multiple times with different witnessing nominals

Q/P: LHS and RHS complex formulas.
*)

function atomize :: \<open>
  (nat \<times> 'a) list \<Rightarrow> (nat \<times> 'a) list \<Rightarrow> (nat \<times> nat) list \<Rightarrow> (nat \<times> nat) list \<Rightarrow> (nat \<times> nat) list \<Rightarrow>
  (nat \<times> (nat list) \<times> 'a hybr_form) list \<Rightarrow> (nat \<times> 'a hybr_form) list \<Rightarrow> (nat \<times> 'a hybr_form) list 
  \<Rightarrow> bool\<close> where
  (*match RHS*)
  \<open>atomize LA RA RN LP RP R Q ((n,Pro a) # P) = 
    atomize LA ((n,a) # RA) RN LP RP R Q P\<close> |

  \<open>atomize LA RA RN LP RP R Q ((n1,Nom n2) # P) = 
    atomize LA RA ((n1,n2) # RN) LP RP R Q P\<close> |

  \<open>atomize LA RA RN LP RP R Q ((n,Neg p) # P) = 
    atomize LA RA RN LP RP R ((n,p) # Q) P\<close> |

  \<open>atomize LA RA RN LP RP R Q ((n,Con p1 p2) # P) =
    ((atomize LA RA RN LP RP R Q ((n,p1) # P)) \<and> (atomize LA RA RN LP RP R Q ((n,p2) # P)))\<close> |

  \<open>atomize LA RA RN LP RP R Q ((n1,Sat n2 p) # P) = 
    atomize LA RA RN LP RP R Q ((n2,p) # P)\<close> |
(*We need to try to find a nominal witnessing Pos later. See last case*)
  \<open>atomize LA RA RN LP RP R Q ((n,Pos p) # P) = 
    atomize LA RA RN LP RP ((n,[],p) # R) Q P\<close>|

  (*match LHS*)
  \<open>atomize LA RA RN LP RP R ((n,Pro a) # Q) [] = 
    atomize ((n,a) # LA) RA RN LP RP R Q []\<close> |
(*we assume/assert that n1=n2. therefore, remove one of them*)
  \<open>atomize LA RA RN LP RP R ((n1,Nom n2) # Q) [] = 
    atomize (mergeNA LA n1 n2) (mergeNA RA n1 n2) (mergeNN RN n1 n2) 
      (mergeNN LP n1 n2) (mergeNN RP n1 n2) (mergeNSNP R n1 n2) (mergeNP Q n1 n2) []\<close> |

  \<open>atomize LA RA RN LP RP R ((n,Neg p) # Q) [] = 
    atomize LA RA RN LP RP R Q [(n,p)]\<close> |

  \<open>atomize LA RA RN LP RP R ((n,Con p1 p2) # Q) []= 
    atomize LA RA RN LP RP R ((n,p1) # (n,p2) # Q) []\<close> |

  \<open>atomize LA RA RN LP RP R ((n1,Sat n2 p) # Q) [] = 
    atomize LA RA RN LP RP R ((n2,p) # Q) []\<close> |

  \<open>atomize LA RA RN LP RP R ((n,Pos p) # Q) [] = (
    let nw = fresh (
      nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U 
      nominalsNN RP U nominalsNSNP R U nominalsNP ((n,Pos p) # Q)) 
    in (atomize LA RA RN ((n,nw) # LP) RP R ((nw,p) # Q) []))\<close> |
(*-------Try all relevant assignments of nominals to possibility on RHS-----------
If no assignment can be made, check if current sequent is a tautology.
Else we can process a statement @n\<diamond>P.
  Find a nominal m to witness the statement
  Check if the sequent with @n\<diamond>P removed fulfills both @n\<diamond>m and @mP
Lastly, try another assignment. Remember that we already tried m.*)
  \<open>atomize LA RA RN LP RP R [] [] = (
      case 
        saturate R (
          nominalsNA LA U nominalsNA RA U nominalsNN RN U 
          nominalsNN LP U nominalsNN RP U nominalsNSNP R)
      of
        None \<Rightarrow> (common LA RA \<or> common LP RP \<or> reflect RN)
      | Some (n,m,p,R',R'') \<Rightarrow> 
          (atomize LA RA RN LP ((n,m) # RP) R' [] [] \<and> atomize LA RA RN LP RP R' [] [(m,p)]) 
          \<or> atomize LA RA RN LP RP R'' [] [])\<close> 
  by pat_completeness simp_all
(*size definition for proving termination of atomize*)

context
begin

lemma merge_lengthNSNP: \<open>length nsnp = length (mergeNSNP nsnp n1 n2)\<close> 
  by (induct nsnp) auto

lemma saturate_size1: \<open>
  saturate R ns = Some (n,m,p,R',R'') \<longrightarrow>
  Suc (size R') = size R\<close>
proof (induct R arbitrary: n m p ns R' R'')
  case Nil
  then show ?case by simp
next
  case (Cons a R)
  assume a1: "(
    \<And>n m p ns R' R''.
    saturate R ns = Some (n, m, p, R', R'') \<longrightarrow>
    Suc (length R') = length R)"
  show ?case 
  proof
    assume a2: "saturate (a # R) ns = Some (n, m, p, R', R'')"
    then have "\<exists> n' ms p'. a = (n',ms,p')"
      by (meson prod_cases3)
    then obtain n' ms p' where 1: \<open>a = (n',ms,p')\<close> by blast
    show "Suc (length R') = length (a # R)" 
    proof cases
      assume "remove ns ms = []"
      then have 1:"saturate' [] (a # R) ns = saturate' [a] R ns" using 1 by simp
      from this a2 have "\<exists> R1 R2. R' = a # R1 \<and> R'' = a # R2" using sat_R1 
        by (metis append_Cons)
      then obtain R1 R2 where R1def: "R' = a # R1 \<and> R'' = a # R2" by blast
      then have "saturate' [] R ns = Some (n, m, p, R1, R2)" 
        by (metis (no_types, lifting) "1" a2 addnt append_Cons self_append_conv2)
      then show ?thesis using a1
        using R1def by auto
    next
      assume "\<not> remove ns ms = []"
      then have \<open>\<exists> m' ms'. remove ns ms = m' # ms'\<close> 
        by (meson list.exhaust)
      then obtain m' ms' where nsms: "remove ns ms = m' # ms'" by blast
      from this 1 a2 have 2: \<open>n = n' \<and> m = m' \<and> p = p' \<and> R' = R \<and> R'' = (n',m' # ms,p') # R\<close>
        by auto
      then show ?thesis
        by simp
    qed
  qed
qed

(*missing*)
lemma miss1: \<open>missing' (m # ms) ns \<le> missing' ms ns\<close>
proof (induct ns arbitrary: ms)
  case Nil
  then show ?case by simp
next
  case (Cons a ns)
  then show ?case 
    by (metis member.simps(2) Suc_leD Suc_le_mono missing'.simps(2))
qed  

lemma miss2: \<open>remove ns ms = m' # ms' \<Longrightarrow> missing' ms ns > missing' (m' # ms) ns\<close>
proof (induct ns arbitrary: ms m' ms')
  case Nil
  then show ?case by simp
next
  fix a ns ms m' ms'
  assume a1: "\<And>ms m' ms'. remove ns ms = m' # ms' \<Longrightarrow> missing' (m' # ms) ns < missing' ms ns"
  then show "remove (a # ns) ms = m' # ms' \<Longrightarrow> missing' (m' # ms) (a # ns) < missing' ms (a # ns)"
  proof-
    assume a2: "remove (a # ns) ms = m' # ms'"
    show "missing' (m' # ms) (a # ns) < missing' ms (a # ns)"
    proof cases
      assume a3: "member a (m' # ms)"
      then show "missing' (m' # ms) (a # ns) < missing' ms (a # ns)" 
      proof cases
        assume am:"a = m'"
        then have "\<not> member a ms" using a2 remove_simp
          by (metis Diff_iff list.set_intros(1) member_iff)
        then show ?thesis using miss1 
          by (metis Suc_le_lessD Suc_le_mono a3 missing'.simps(2))
      next
        assume "\<not>a = m'"
        then show ?thesis 
          by (metis member.simps(2) 
              a1 a2 a3 missing'.simps(2) remove.simps(2))
      qed
    next
      assume "\<not> member a (m' # ms)"
      then show "missing' (m' # ms) (a # ns) < missing' ms (a # ns)" 
        by (metis member.simps(2) a2 list.inject remove.simps(2))
    qed
  qed
qed

lemma miss_plus: \<open>missing (R1 @ R2) ns = missing R1 ns + missing R2 ns\<close>
  by (induct R1) auto

lemma saturate_size2: \<open>
  saturate' R1 R ns = Some (n,m,p,R',R'') \<Longrightarrow>
  missing R'' ns < missing (R1 @ R) ns\<close>
proof (induct R arbitrary: n m p R1 R' R'')
  case Nil
  then show ?case by simp
next
  fix a R n m p R1 R' R''
  assume a1: "
    \<And>n m p R1 R' R''.
      saturate' R1 R ns = Some (n, m, p, R', R'') \<Longrightarrow>
      missing R'' ns < missing (R1 @ R) ns"
  show "
    saturate' R1 (a # R) ns = Some (n, m, p, R', R'') \<Longrightarrow>
       missing R'' ns < missing (R1 @ a # R) ns"
  proof-
    assume a2: "saturate' R1 (a # R) ns = Some (n, m, p, R', R'')"
    then have "\<exists> n' ms p'. a = (n',ms,p')"
      by (meson prod_cases3)
    then obtain n' ms p' where adef: \<open>a = (n',ms,p')\<close> by blast
    show "missing R'' ns < missing (R1 @ a # R) ns" 
    proof cases
      assume "remove ns ms = []"
      then have "saturate' R1 (a # R) ns = saturate' (R1 @ [a]) R ns" using adef by simp
      then have "missing R'' ns < missing (R1 @ [a] @ R) ns" using a1 a2 
        by (metis append_assoc)
      then show ?thesis by simp
    next
      assume a3:"\<not> remove ns ms = []"
      then have \<open>\<exists> m' ms'. remove ns ms = m' # ms'\<close> 
        by (meson list.exhaust)
      then obtain m' ms' where nsms: "remove ns ms = m' # ms'" by blast
      from this adef a2 have 2: \<open>
        n = n' \<and> m = m' \<and> p = p' \<and> R' = R1 @ R \<and> R'' = R1 @ [(n',m' # ms,p')] @ R\<close>
        by auto
      have "missing [(n',m' # ms,p')] ns < missing [(n',ms,p')] ns"
        by (simp add: miss2 nsms)
      then show ?thesis 
        by (simp add: "2" adef miss_plus)
    qed
  qed
qed

lemma remove_add_missing: "
  is_set A \<Longrightarrow> member a A \<Longrightarrow> missing' X A = missing' X (a # (remove A [a]))"
  apply (induct A)
   apply simp
  by (smt (z3) member.simps(2) add_right_imp_eq is_set.simps(2) is_set_size 
      length_Cons less_not_refl list.size(4) missing'.simps(2) remove.simps(2) remove_size removent)

lemma missing_set_equal1: \<open>is_set A \<and> is_set B \<Longrightarrow> set_equal A B \<Longrightarrow> missing' X A = missing' X B\<close>
proof (induct A arbitrary: B)
  case Nil
  then show ?case by simp
next
  case (Cons a A)
  have 1:\<open>\<not>member a A\<close> 
    using Cons.prems(1) by auto
  have \<open>set_equal (remove (a # A) [a]) (remove B [a])\<close> using remove_equal 
    by (metis Cons.prems(2))
  then have "set_equal A (remove B [a])" 
    by (metis member.simps(2) 1 common.simps(1) 
        common.simps(2) remove.simps(2) removent)
  have "is_set A" 
    using Cons.prems(1) by auto
  have "is_set (remove B [a])"
    by (simp add: remove_is_set Cons.prems(1))
  then have "missing' X A = missing' X (remove B [a])"
    using Cons.hyps \<open>is_set A\<close> \<open>set_equal A (remove B [a])\<close> by blast
  then have "missing' X (a # A) = missing' X (a # (remove B [a]))"
    by simp
      
  then show ?case by (metis Cons.prems(1) Cons.prems(2) list.distinct(1) 
          remove.simps(2) remove_add_missing set_equal_def)
qed

lemma missing_set_equal2: \<open>is_set A \<Longrightarrow> is_set B \<Longrightarrow> set_equal A B \<Longrightarrow> missing X A = missing X B\<close>
  apply (induct X)
   apply simp
  by (smt (verit, ccfv_threshold) Pair_inject list.distinct(1) 
      list.inject missing.elims missing_set_equal1)

lemma missing_sub_set1: \<open>is_set A  \<Longrightarrow> sub_set A B \<Longrightarrow> missing' X A \<le> missing' X B\<close>
proof (induct B arbitrary: A)
  case Nil
  then show ?case by simp
next
  case (Cons a B)
  then show ?case 
  proof cases
    assume \<open>member a A\<close>
    have \<open>sub_set (remove A [a]) (a # B)\<close> 
      by (meson Cons.prems(2) sub_remove_set)
    then have \<open>sub_set (remove A [a]) B\<close> 
      by (meson ListSet.member.simps(2) ListSet.member_remove sub_set_remove2)
    then have \<open>missing' X (remove A [a]) \<le> missing' X B\<close> 
      by (simp add: Cons.hyps Cons.prems(1) remove_is_set)
    then have \<open>missing' X (a # (remove A [a])) \<le> missing' X (a # B)\<close> 
      by simp
    then show ?thesis 
      by (metis Cons.prems(1) \<open>member a A\<close> remove_add_missing)
  next
    assume "\<not> member a A"
    then show ?thesis
      by (metis Cons.hyps Cons.prems(1) Cons.prems(2) ListSet.member.simps(2) le_Suc_eq 
          member_sub_set missing'.simps(2))
  qed
qed

lemma missing_sub_set2: \<open>is_set A \<Longrightarrow> sub_set A B \<Longrightarrow> missing X A \<le> missing X B\<close>
proof (induct X)
  case Nil
  then show ?case by simp
next
  case (Cons a X)
  have \<open>\<exists> x ms y. a = (x,ms,y)\<close>
    by (meson prod_cases3)
  then show ?case 
    by (metis Cons.hyps Cons.prems(1) Cons.prems(2) Cons.prems(2) 
        add_mono_thms_linordered_semiring(1) missing.simps(2) missing_sub_set1)
qed

lemma missing_naught: \<open>missing R [] = 0\<close> 
proof (induct R)
  case Nil
  then show ?case by simp
next
  case (Cons a R)
  obtain u1 ns u2 where \<open>a = (u1,ns,u2)\<close> 
    using prod_cases3 by blast
  then show ?case 
    by (simp add: Cons.hyps)
qed

lemma missing_merge1: \<open>missing' (mergeNS ms n1 n2) (mergeNS ns n1 n2) \<le> missing' ms ns\<close>
proof (induct ns)
  case Nil
  then show ?case by simp
next
  case (Cons n ns)
  then show ?case 
  proof cases
    assume a1:\<open>n = n1\<close>
    show ?thesis 
    proof cases
      assume a2:\<open>member n ms\<close>
      moreover have "member n2 (mergeNS ms n1 n2)" using a1 a2
        by (metis member_mergeNS2)
      moreover have \<open>
        missing' (mergeNS ms n1 n2) (mergeNS (n # ns) n1 n2) = 
        missing' (mergeNS ms n1 n2) (n2 # (mergeNS ns n1 n2))\<close> 
        by (simp add: a1)
      ultimately show ?thesis 
        by (metis Cons.hyps missing'.simps(2))
    next
      assume a2:\<open>\<not> member n ms\<close>
      then have 1:\<open>missing' ms (n # ns) = 1 + missing' ms ns\<close> by simp
      show ?thesis 
      proof cases
        assume a3:\<open>member n2 (mergeNS ms n1 n2)\<close>
        from this a1 have \<open>
          missing' (mergeNS ms n1 n2) (mergeNS (n # ns) n1 n2) = 
          missing' (mergeNS ms n1 n2) (mergeNS ns n1 n2)\<close> 
          by simp
        then show ?thesis 
          by (metis "1" Cons.hyps add_increasing zero_le_one)
      next
        assume a3:\<open>\<not>member n2 (mergeNS ms n1 n2)\<close>
        then have \<open>
          missing' (mergeNS ms n1 n2) (mergeNS (n # ns) n1 n2) = 
          1 + missing' (mergeNS ms n1 n2) (mergeNS ns n1 n2)\<close> using a1 by simp
        then show ?thesis
          using "1" Cons.hyps by linarith
      qed
    qed
  next
    assume a1:\<open>n \<noteq> n1\<close>
    show ?thesis 
    proof cases
      assume a2:\<open>member n ms\<close>
      then have 1:\<open>missing' ms (n # ns) = missing' ms ns\<close> by simp
      have \<open>member n (mergeNS ms n1 n2)\<close> using a2
        by (meson a1 member_mergeNS3)
      then have \<open>
        missing' (mergeNS ms n1 n2) (mergeNS (n # ns) n1 n2) = 
        missing' (mergeNS ms n1 n2) (mergeNS ns n1 n2)\<close> 
        by auto
      then show ?thesis
        using Cons.hyps 1 by linarith
    next
      assume a2:\<open>\<not> member n ms\<close>
      then have 1:\<open>missing' ms (n # ns) = 1 + missing' ms ns\<close> by simp
      show ?thesis 
      proof cases
        assume "member n (mergeNS ms n1 n2)"
        then have \<open>
          missing' (mergeNS ms n1 n2) (mergeNS (n # ns) n1 n2) =
          missing' (mergeNS ms n1 n2) (mergeNS ns n1 n2)\<close> 
          by auto
        then show ?thesis
          using "1" Cons.hyps by presburger
      next
        assume "\<not>member n (mergeNS ms n1 n2)"
        then have \<open>
          missing' (mergeNS ms n1 n2) (mergeNS (n # ns) n1 n2) =
          1 + missing' (mergeNS ms n1 n2) (mergeNS ns n1 n2)\<close> 
          using a1 by auto
        then show ?thesis 
          using "1" Cons.hyps by linarith
      qed
    qed
  qed
qed
  

lemma missing_merge: \<open>missing (mergeNSNP R n1 n2) (mergeNS ns n1 n2) \<le> missing R ns\<close> 
proof (induct R)
  case Nil
  then show ?case by simp
next
  case (Cons umsu R)
  obtain u1 ms u2 where msdef: \<open>umsu = (u1,ms,u2)\<close> 
    using prod_cases3 by blast
  have \<open>missing' (mergeNS ms n1 n2) (mergeNS ns n1 n2) \<le> missing' ms ns\<close> 
    using missing_merge1 by simp
  then show ?case 
    using Cons.hyps msdef by auto
qed
(*\missing*)

lemma pos_merge: \<open>pos_count (mergeP p n1 n2) = pos_count p\<close> 
  by (induct p) simp_all

lemma pos_mergeNP: \<open>pos_countNP (mergeNP Q n1 n2) = pos_countNP Q\<close>
proof (induct Q)
  case Nil
  then show ?case by simp
next
  case (Cons a Q)
  obtain n p where adef:"a = (n,p)"
    by (meson prod.exhaust_sel)
  have \<open>pos_count (mergeP p n1 n2) = pos_count p\<close>
    by (simp add: pos_merge)
  then show ?case 
    using Cons.hyps adef by auto
qed

lemma pos_mergeNSNP: \<open>pos_countNSNP (mergeNSNP R n1 n2) = pos_countNSNP R\<close>
proof (induct R)
  case Nil
  then show ?case by simp
next
  case (Cons a R)
  obtain n ns p where adef:\<open>a = (n,ns,p)\<close>
    using prod_cases3 by blast
  have \<open>pos_count (mergeP p n1 n2) = pos_count p\<close>
    by (simp add: pos_merge)
  then show ?case
    using Cons.hyps adef by auto
qed

primrec size_atom_form :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a hybr_form \<Rightarrow> nat\<close> where
  \<open>size_atom_form ps r ns (Pro a) = Suc 0\<close> |
  \<open>size_atom_form ps r ns (Nom n) = Suc 0\<close> |
  \<open>size_atom_form ps r ns (Neg p) = Suc (size_atom_form ps r ns p)\<close> |
  \<open>size_atom_form ps r ns (Con p1 p2) = Suc (
    size_atom_form ps r ns p1 + 
    size_atom_form ps r ns p2)\<close> |
  \<open>size_atom_form ps r ns (Sat n p) = Suc (size_atom_form ps r ns p)\<close> |
  \<open>size_atom_form ps r ns (Pos p) = ps + r + ns + Suc (Suc (size_atom_form ps r ns p))\<close>

lemma size_atom_form_size_ns: \<open>
  ns \<le> ms \<Longrightarrow> psn \<le> psm \<Longrightarrow> size_atom_form psn r ns p \<le> size_atom_form psm r ms p\<close> 
  by (induct p) auto

lemma lesser_sum: \<open>(\<forall>x. 
    (f :: 'a \<Rightarrow> nat) x \<le> (f' :: 'a \<Rightarrow> nat) x) \<Longrightarrow> 
    (\<Sum> x \<leftarrow> (X :: 'a list). f x) \<le> (\<Sum> x \<leftarrow> X. f' x)\<close>
  by (simp add: sum_list_mono)

lemma lesser_add: \<open>(a :: nat) \<le> b \<Longrightarrow> c \<le> d \<Longrightarrow> a + c \<le> b + d\<close>
  by simp

abbreviation ns_0 where \<open>ns_0 LA RA RN LP RP R Q P \<equiv> 
  nominalsNA LA U nominalsNA RA U nominalsNN RN U
  nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U nominalsNP P\<close>

abbreviation ns_1 where \<open>ns_1 LA RA RN LP RP R Q \<equiv> 
  nominalsNA LA U nominalsNA RA U nominalsNN RN U
  nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q\<close>

abbreviation ps_0 where \<open>ps_0 R Q P \<equiv> pos_countNSNP R + pos_countNP Q + pos_countNP P\<close>

abbreviation n1_0 where 
  \<open>n1_0 Q ps R ns \<equiv> \<Sum>(u, p)\<leftarrow>Q. size_atom_form ps (length R) (length ns) p\<close>

abbreviation n2_0 where 
  \<open>n2_0 ps R ns \<equiv> \<Sum>(u, u', p)\<leftarrow>R. Suc (size_atom_form ps (length R) (length ns) p)\<close>

lemma n1_0_ps_less: \<open>length ns \<le> length ns' \<Longrightarrow> ps \<le> ps' \<Longrightarrow> n1_0 Q ps R ns \<le> n1_0 Q ps' R ns'\<close>
  by (simp add: lesser_sum size_atom_form_size_ns)

lemma n2_0_ps_less: \<open>length ns \<le> length ns' \<Longrightarrow> ps \<le> ps' \<Longrightarrow> n2_0 ps R ns \<le> n2_0 ps' R ns'\<close>
  by (simp add: lesser_sum size_atom_form_size_ns)

lemma size_atom_suc_dec: \<open>
  ns + ps + R = ns' + ps' + R' \<Longrightarrow> size_atom_form ps R ns p = size_atom_form ps' R' ns' p\<close> 
  by (induct p) simp_all

lemma size_atom_suc_dec2: \<open>
  ns + ps + R \<le> ns' + ps' + R' \<Longrightarrow> size_atom_form ps R ns p \<le> size_atom_form ps' R' ns' p\<close> 
  by (induct p) simp_all

lemma n1_0_suc_dec: \<open>ps + ns + r \<le> ps' + ns' + r' \<Longrightarrow>
  (\<Sum>(_,p) \<leftarrow> Q. size_atom_form ps  r  ns  p) \<le>
  (\<Sum>(_,p) \<leftarrow> Q. size_atom_form ps' r' ns' p)\<close>
proof (induct Q)
  case Nil
  then show ?case by simp
next
  case (Cons a Q)
  let ?sm = \<open>\<lambda> Q ps r ns. (\<Sum>(_,p) \<leftarrow> Q. size_atom_form ps r ns p)\<close>
  obtain u p where adef:"a = (u,p)" 
    using prod.exhaust_sel by blast
  then have "size_atom_form ps  r  ns p \<le> size_atom_form ps' r' ns' p" 
    by (metis Cons.prems add.commute size_atom_suc_dec2)
  moreover have \<open>?sm Q ps r ns \<le> ?sm Q ps' r' ns'\<close> 
    by (simp add: Cons.hyps Cons.prems)
  ultimately show ?case
    by (smt (z3) adef case_prod_conv lesser_add list.simps(9) sum_list.Cons)
qed

lemma n1_0_suc_dec2: \<open>ps + length ns + length R \<le> ps' + length ns' + length R' \<Longrightarrow>
  n1_0 Q ps R ns \<le>
  n1_0 Q ps' R' ns'\<close> 
  using n1_0_suc_dec by blast

lemma n2_0_suc_dec: \<open>ps + ns + r \<le> ps' + ns' + r' \<Longrightarrow>
  (\<Sum>(u, uu, p)\<leftarrow>R. Suc (size_atom_form ps r ns p)) \<le>
  (\<Sum>(u, uu, p)\<leftarrow>R. Suc (size_atom_form ps' r' ns' p))\<close>
proof (induct R)
  case Nil
  then show ?case by simp
next
  case (Cons a R)
  let ?sm = \<open>\<lambda> Q ps r ns. (\<Sum>(_, _, p)\<leftarrow>R. Suc (size_atom_form ps r ns p))\<close>
  obtain u u' p where adef:"a = (u,u',p)" 
    using prod_cases3 by blast
  then have "Suc (size_atom_form ps  r  ns p) \<le> Suc (size_atom_form ps' r' ns' p)" 
    by (metis Cons.prems Suc_le_mono add.commute size_atom_suc_dec2)
  moreover have \<open>?sm R ps r ns \<le> ?sm R ps' r' ns'\<close>
    by (simp add: Cons.hyps Cons.prems)
  ultimately show ?case 
    by (smt (z3) adef case_prod_conv lesser_add list.simps(9) sum_list.Cons)
qed

lemma n2_0_suc_dec2: \<open>ps + length ns \<le> ps' + length ns' \<Longrightarrow>
  n2_0 ps R ns \<le>
  n2_0 ps' R ns'\<close> 
proof-
  assume \<open>ps + length ns \<le> ps' + length ns'\<close>
  then have 1:\<open>ps + (length R) + (length ns) \<le> ps' + (length R) + (length ns')\<close> by simp
  show ?thesis 
    proof -
    have "length ns + (ps + length R) \<le> ps' + length R + length ns'"
      by (metis "1" add.commute)
    then show ?thesis
      by (simp add: n2_0_suc_dec)
  qed
qed

lemma sum_suc: "(\<Sum>(u, u', p)\<leftarrow>R. Suc (f p)) = (\<Sum>(u, u', p)\<leftarrow>R. f p) + length R" 
  by (induct R) auto

lemma missing_less: \<open>missing' ms ns \<le> length ns\<close>
  by (induct ns)  auto

lemma merge_size_atom:\<open>ns \<le> ns' \<Longrightarrow> R \<le> R' \<Longrightarrow> ps \<le> ps' \<Longrightarrow>
  size_atom_form ps R ns (mergeP p n1 n2) \<le> 
  size_atom_form ps' R' ns' p\<close> 
  by (induct p) simp_all

lemma missing_add_length: \<open>missing R (add n ns) \<le> missing R ns + length R\<close> 
proof (induct R)
  case Nil
  then show ?case by simp
next
  case (Cons a R)
  obtain u1 u2 ms where adef: \<open>a = (u1,ms,u2)\<close>
    using prod_cases3 by blast
  show ?case 
  proof cases
    assume "member n ns"
    then show ?thesis 
      by (simp add: add_def)
  next
    assume a:\<open>\<not>member n ns\<close>
    have \<open>missing' ms (n # ns) \<le> missing' ms ns + 1\<close>
      by force
    then show ?thesis 
      by (smt (z3) Cons.hyps a add.assoc add.commute add_def adef dual_order.antisym le_add2 
          length_Cons lesser_add list.inject missing.simps(2) order_refl plus_1_eq_Suc)
  qed
qed

lemma merge_n1_0: \<open>length ns \<le> length ns' \<Longrightarrow> length R \<le> length R' \<Longrightarrow> ps \<le> ps' \<Longrightarrow>
  n1_0 (mergeNP Q n1 n2) ps R ns \<le> n1_0 Q ps' R' ns'\<close> 
proof (induct Q)
  case Nil
  then show ?case by simp
next
  case (Cons a Q)
  obtain u p where adef:\<open>a = (u,p)\<close>
    by (meson prod.exhaust_sel)
  then have \<open>
    n1_0 (mergeNP (a # Q) n1 n2) ps R ns = 
    size_atom_form ps (length R) (length ns) (mergeP p n1 n2) + n1_0 (mergeNP Q n1 n2) ps R ns\<close> 
    by force
  moreover have \<open>
    n1_0 (a # Q) ps' R' ns' = 
    size_atom_form ps' (length R') (length ns') p + n1_0 Q ps' R' ns'\<close> 
    using adef by force
  moreover have \<open>
    size_atom_form ps (length R) (length ns) (mergeP p n1 n2) \<le>
    size_atom_form ps' (length R') (length ns') p\<close>
    using merge_size_atom Cons.prems 
    by blast
  moreover have \<open>n1_0 (mergeNP Q n1 n2) ps R ns \<le> n1_0 Q ps' R' ns'\<close> 
    using Cons.hyps Cons.prems(1) Cons.prems(2) Cons.prems(3) by auto
  ultimately show ?case 
    by linarith
qed 

lemma merge_n2_0_1:\<open>ns \<le> ns' \<Longrightarrow> ps \<le> ps' \<Longrightarrow> 
  (\<Sum>(u, u', p')\<leftarrow> (mergeNSNP R n1 n2). Suc (size_atom_form ps lR ns p')) \<le> 
  (\<Sum>(u, u', p')\<leftarrow> R. Suc (size_atom_form ps' lR ns' p'))\<close> 
proof (induct R)
  case Nil
  then show ?case by simp
next
  case (Cons a R)
  obtain u u' p where adef:\<open>a = (u,u',p)\<close>
    using prod_cases3 by blast
  then obtain u1 u2 where 
    udef:\<open>(u1,u2,mergeP p n1 n2) # (mergeNSNP R n1 n2) = (mergeNSNP (a # R) n1 n2)\<close>
    by simp
  have 1: \<open>
    Suc (size_atom_form ps lR ns (mergeP p n1 n2)) \<le>
    Suc (size_atom_form ps' lR ns' p)\<close>
    using Cons.prems merge_size_atom 
    by force
  have \<open>
    (\<Sum>(u, u', p')\<leftarrow>mergeNSNP (a # R) n1 n2. Suc (size_atom_form ps lR ns p')) =
    (\<Sum>(u, u', p')\<leftarrow>((u1,u2,mergeP p n1 n2) # mergeNSNP R n1 n2). Suc (size_atom_form ps lR ns p'))\<close>
    using udef by simp
  moreover have \<open>
    ... = Suc (size_atom_form ps lR ns (mergeP p n1 n2)) + 
      (\<Sum>(u, u', p')\<leftarrow>mergeNSNP R n1 n2. Suc (size_atom_form ps lR ns p'))\<close>  
    by simp
  moreover have \<open>
    ... \<le> Suc (size_atom_form ps' lR ns' p) + 
      (\<Sum>(u, u', p')\<leftarrow>R. Suc (size_atom_form ps' lR ns' p'))\<close> 
    using "1" Cons.hyps Cons.prems(1) Cons.prems(2) by linarith
  moreover have \<open>
    ... = (\<Sum>(u, u', p')\<leftarrow> ((u,u',p) # R). Suc (size_atom_form ps' lR ns' p'))\<close> 
    by simp
  moreover have \<open>
    ... = (\<Sum>(u, u', p')\<leftarrow> (a # R). Suc (size_atom_form ps' lR ns' p'))\<close> 
    using adef by simp
  ultimately show ?case by simp
qed


lemma merge_n2_0: \<open>length ns \<le> length ns' \<Longrightarrow> ps \<le> ps' \<Longrightarrow> 
  n2_0 ps (mergeNSNP R n1 n2) ns \<le> n2_0 ps' R ns'\<close> (is "?P1 \<Longrightarrow> ?P2 \<Longrightarrow> ?C")
proof-
  assume a1:"?P1"
  assume a2:\<open>?P2\<close>
  have \<open>length (mergeNSNP R n1 n2) = length R\<close> 
    by (metis merge_lengthNSNP)
  then have "
    n2_0 ps (mergeNSNP R n1 n2) ns = 
    (\<Sum>(u, u', p)\<leftarrow>(mergeNSNP R n1 n2). Suc (size_atom_form ps (length R) (length ns) p))"
    by simp
  moreover have \<open>
    ... \<le> (\<Sum>(u, u', p)\<leftarrow>R. Suc (size_atom_form ps' (length R) (length ns') p))\<close>
    using a1 a2 merge_n2_0_1 by force
  moreover have \<open>
    ... = n2_0 ps' R ns'\<close> 
    by simp
  ultimately show ?C 
    by simp
qed

lemma n2_0_lesser:\<open>(ps \<le> ps' \<Longrightarrow> Rl \<le> Rl' \<Longrightarrow> ns \<le> ns' \<Longrightarrow> 
  (\<Sum>(u, u', p)\<leftarrow>R. Suc (size_atom_form ps Rl ns p)) \<le> 
  (\<Sum>(u, u', p)\<leftarrow>R. Suc (size_atom_form ps' Rl' ns' p)))\<close>
proof (induct R)
  case Nil
  then show ?case by simp
next
  case (Cons r R)
  obtain u u' p where rdef:\<open>r = (u,u',p)\<close> 
    using prod_cases3 by blast
  have \<open>
    (\<Sum>(u, u', p)\<leftarrow>r # R. Suc (size_atom_form ps Rl ns p)) = 
    Suc (size_atom_form ps Rl ns p) + (\<Sum>(u, u', p)\<leftarrow>R. Suc (size_atom_form ps Rl ns p))\<close>
    using rdef by simp
  moreover have \<open>
    (\<Sum>(u, u', p)\<leftarrow>r # R. Suc (size_atom_form ps' Rl' ns' p)) = 
    Suc (size_atom_form ps' Rl' ns' p) + (\<Sum>(u, u', p)\<leftarrow>R. Suc (size_atom_form ps' Rl' ns' p))\<close>
    using rdef by simp
  moreover have \<open>Suc (size_atom_form ps Rl ns p) \<le> Suc (size_atom_form ps' Rl' ns' p)\<close>
    by (simp add: Cons.prems(1) Cons.prems(2) Cons.prems(3) add_le_mono size_atom_suc_dec2)
  ultimately show ?case 
    using Cons.hyps Cons.prems(1) Cons.prems(2) Cons.prems(3) by linarith
qed

lemma pos_count_con: \<open>pos_countNSNP (A @ B) = pos_countNSNP A + pos_countNSNP B\<close> 
  apply (induct A) 
   apply simp
  using add.left_commute by auto

termination
  apply (relation \<open>measure (
    \<lambda>(LA :: (nat \<times> 'a) list,RA  :: (nat \<times> 'a) list,RN :: (nat \<times> nat) list,LP  :: (nat \<times> nat) list,
      RP :: (nat \<times> nat) list, R :: (nat \<times> nat list \<times> 'a hybr_form) list,
      Q :: (nat \<times> 'a hybr_form) list, P :: (nat \<times> 'a hybr_form) list). 
    let ns = ns_0 LA RA RN LP RP R Q P in
    let ps = ps_0 R Q P in
    (\<Sum>(_,p) \<leftarrow> Q @ P. size_atom_form ps (size R) (size ns) p) + 
    (\<Sum>(_,_,p) \<leftarrow> R. Suc (size_atom_form ps (size R) (size ns) p)) + 
    missing R ns)\<close>) 
                  apply simp_all
proof-
  fix LA RA :: \<open>(nat \<times> 'a) list\<close>
  fix RN :: \<open>(nat \<times> nat) list\<close>
  fix LP RP :: \<open>(nat \<times> nat) list\<close>
  fix R :: \<open>(nat \<times> nat list \<times>'a hybr_form) list\<close>
  fix Q P :: \<open>(nat \<times>'a hybr_form) list\<close>
  fix n :: nat
  let ?ns = "\<lambda> LA RA RN LP RP R Q n P.
    nominalsNA LA U add n (nominalsNA RA) U nominalsNN RN U nominalsNN LP U 
    nominalsNN RP U nominalsNSNP R U nominalsNP Q U nominalsNP P"
  let ?ms = "\<lambda> LA RA RN LP RP R Q n P.
    nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U 
    nominalsNSNP R U nominalsNP Q U add n ([] U nominalsNP P)"
  let ?show_this = "\<lambda> LA RA RN LP RP R Q n P.
    (let ns = ?ns LA RA RN LP RP R Q n P in 
    let ps = ps_0 R Q P in
      n1_0 Q ps R ns +
      n1_0 P ps R ns +
      n2_0 ps R ns +
      missing R ns) < (
    let ns = ?ms LA RA RN LP RP R Q n P in
    let ps = ps_0 R Q P in Suc (
      n1_0 Q ps R ns +
      n1_0 P ps R ns +
      n2_0 ps R ns +
      missing R ns))"
  show "?show_this LA RA RN LP RP R Q n P"
  proof-
    have isset: "is_set (?ns LA RA RN LP RP R Q n P) \<and> is_set (?ms LA RA RN LP RP R Q n P)"
      using NA_is_set union_is_set by auto

    have setequal: "set_equal (?ns LA RA RN LP RP R Q n P) (?ms LA RA RN LP RP R Q n P)" 
    proof -
      have "
        set (nominalsNA LA U add n (nominalsNA RA) U nominalsNN RN U nominalsNN LP U nominalsNN RP U
          nominalsNSNP R U nominalsNP Q U nominalsNP P) =
        set (add n (ns_0 LA RA RN LP RP R Q P))" 
        by (metis Un_insert_left Un_insert_right add_simp union_simp)
      then show ?thesis 
        by (smt (z3) Un_insert_right add_simp set_equal_iff union_simp unionaddnt)
    qed

    then have "
      missing R (?ns LA RA RN LP RP R Q n P) = missing R (?ms LA RA RN LP RP R Q n P)" 
      using isset missing_set_equal2 by blast
    moreover have "
      length (?ns LA RA RN LP RP R Q n P) = length (?ms LA RA RN LP RP R Q n P)" 
      using isset set_size_equal setequal by blast
    ultimately show "?show_this LA RA RN LP RP R Q n P" 
      by (metis lessI)
  qed
next
  fix LA RA :: \<open>(nat \<times> 'a) list\<close>
  fix RN :: \<open>(nat \<times> nat) list\<close>
  fix LP RP :: \<open>(nat \<times> nat) list\<close>
  fix R :: \<open>(nat \<times> nat list \<times>'a hybr_form) list\<close>
  fix Q P :: \<open>(nat \<times>'a hybr_form) list\<close>
  fix n1 n2 :: nat
  let ?ns = "\<lambda> LA RA RN LP RP R Q n1 n2 P.
    nominalsNA LA U nominalsNA RA U add n1 (add n2 (nominalsNN RN)) U nominalsNN LP U 
    nominalsNN RP U nominalsNSNP R U nominalsNP Q U nominalsNP P"
  let ?ms = "\<lambda> LA RA RN LP RP R Q n1 n2 P.
    nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U 
    nominalsNSNP R U nominalsNP Q U add n1 ([n2] U nominalsNP P)"
  let ?show_this = "\<lambda> LA RA RN LP RP R Q n1 n2 P.
    (let ns = ?ns LA RA RN LP RP R Q n1 n2 P in 
    let ps = ps_0 R Q P in
      n1_0 Q ps R ns +
      n1_0 P ps R ns +
      n2_0 ps R ns +
      missing R ns) < (
    let ns = ?ms LA RA RN LP RP R Q n1 n2 P in
    let ps = ps_0 R Q P in Suc (
      n1_0 Q ps R ns +
      n1_0 P ps R ns +
      n2_0 ps R ns +
      missing R ns))"
  show "?show_this LA RA RN LP RP R Q n1 n2 P"
  proof-

    have isset: "
      is_set (?ns LA RA RN LP RP R Q n1 n2 P) \<and> is_set (?ms LA RA RN LP RP R Q n1 n2 P)"
      using NA_is_set union_is_set by auto

    have setequal: "set_equal (?ns LA RA RN LP RP R Q n1 n2 P) (?ms LA RA RN LP RP R Q n1 n2 P)" 
    proof -
      have "set_equal (add n1 ([n2] U nominalsNP P)) (add n1 (add n2 (nominalsNP P)))" 
        by (metis member.simps(1) add_def set_equal_iff union.simps(1) 
            union_associative unionadd1 unionadd2 unionaddnt)
      then have "
        set_equal 
          (?ms LA RA RN LP RP R Q n1 n2 P)  
          (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U 
            nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n1 (add n2 (nominalsNP P)))" 
        using union_with_equal by metis
      moreover have "
        set (...) =
        set (add n1 (add n2 (ns_0 LA RA RN LP RP R Q P)))"
        by (smt (verit, ccfv_threshold) Un_insert_right add_simp union_simp)
      moreover have "
        set (?ns LA RA RN LP RP R Q n1 n2 P) =
        set (add n1 (add n2 (ns_0 LA RA RN LP RP R Q P)))"   
        by (smt (z3) Un_insert_left Un_insert_right add_simp union_simp)
      ultimately show ?thesis 
        by simp
    qed
    then have "
      missing R (?ns LA RA RN LP RP R Q n1 n2 P) = missing R (?ms LA RA RN LP RP R Q n1 n2 P)" 
      using isset missing_set_equal2 by blast
    moreover have "
      length (?ns LA RA RN LP RP R Q n1 n2 P) = length (?ms LA RA RN LP RP R Q n1 n2 P)" 
      using isset set_size_equal setequal by blast
    ultimately show "?show_this LA RA RN LP RP R Q n1 n2 P" 
      by (metis (full_types) lessI)
  qed
next
  fix LA RA :: \<open>(nat \<times> 'a) list\<close>
  fix RN :: \<open>(nat \<times> nat) list\<close>
  fix LP RP :: \<open>(nat \<times> nat) list\<close>
  fix R :: \<open>(nat \<times> nat list \<times>'a hybr_form) list\<close>
  fix Q P :: \<open>(nat \<times>'a hybr_form) list\<close>
  fix n :: nat
  fix p :: "'a hybr_form"
  let ?ns = "\<lambda> LA RA RN LP RP R Q n p P.
    nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U 
    nominalsNN RP U nominalsNSNP R U add n (nominalsForm p U nominalsNP Q) U nominalsNP P"
  let ?ms = "\<lambda> LA RA RN LP RP R Q n p P.
    nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U 
    nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p U nominalsNP P)"
  let ?psn = "\<lambda> R Q P p. pos_countNSNP R + (pos_count p + pos_countNP Q) + pos_countNP P"
  let ?psm = "\<lambda> R Q P p. pos_countNSNP R + pos_countNP Q + (pos_count p + pos_countNP P)"
  let ?show_this = "\<lambda> LA RA RN LP RP R Q n p P.
    (let ns = ?ns LA RA RN LP RP R Q n p P in 
    let ps = ?psn R Q P p in
      size_atom_form ps (length R) (length ns) p +
      n1_0 Q ps R ns +
      n1_0 P ps R ns +
      n2_0 ps R ns +
      missing R ns) < (
    let ns = ?ms LA RA RN LP RP R Q n p P in
    let ps = ?psm R Q P p in Suc (
      n1_0 Q ps R ns +
      (size_atom_form ps (length R) (length ns) p +
      n1_0 P ps R ns) +
      n2_0 ps R ns +
      missing R ns))"
  show "?show_this LA RA RN LP RP R Q n p P"
  proof-
    have isset: "
      is_set (?ns LA RA RN LP RP R Q n p P) \<and> is_set (?ms LA RA RN LP RP R Q n p P)"
      using NA_is_set union_is_set by auto

    have setequal: "set_equal (?ns LA RA RN LP RP R Q n p P) (?ms LA RA RN LP RP R Q n p P)" 
    proof -
      have "set_equal 
        (?ns LA RA RN LP RP R Q n p P)
        (add n (nominalsForm p U (ns_0 LA RA RN LP RP R Q P)))" 
        apply simp
        by (smt (z3) Un_insert_left add_simp sup_assoc sup_left_commute union_simp)
      moreover have "set_equal 
        (?ms LA RA RN LP RP R Q n p P)
        (add n (nominalsForm p U ns_0 LA RA RN LP RP R Q P))" 
        apply simp
        by (smt (z3) Un_insert_left add_simp sup_assoc sup_left_commute union_simp)
      ultimately show ?thesis
        by blast
    qed
    then have 1:"
      missing R (?ns LA RA RN LP RP R Q n p P) = missing R (?ms LA RA RN LP RP R Q n p P)" 
      using isset missing_set_equal2
      by blast
    have 2:"
      length (?ns LA RA RN LP RP R Q n p P) = length (?ms LA RA RN LP RP R Q n p P)" 
      using isset set_size_equal setequal 
      by meson
    moreover have "?psn R Q P p = ?psm R Q P p"
      by simp
    show "?show_this LA RA RN LP RP R Q n p P" 
    proof -
      have "
        size_atom_form (?psn R Q P p) (length R) (length (?ms LA RA RN LP RP R Q n p P)) p + 
        n1_0 Q (?psn R Q P p) R (?ms LA RA RN LP RP R Q n p P) + 
        n1_0 P (?psn R Q P p) R (?ms LA RA RN LP RP R Q n p P) + 
        n2_0 (?psn R Q P p) R (?ms LA RA RN LP RP R Q n p P) + 
        missing R (?ms LA RA RN LP RP R Q n p P) < Suc (
        n1_0 Q (?psn R Q P p) R (?ms LA RA RN LP RP R Q n p P) + 
        (n1_0 P (?psm R Q P p) R (?ms LA RA RN LP RP R Q n p P) + 
        (n2_0 (?psm R Q P p) R (?ms LA RA RN LP RP R Q n p P) + 
        (missing R (?ms LA RA RN LP RP R Q n p P) + 
        size_atom_form (pos_countNP Q + (pos_countNP P + (pos_countNSNP R + pos_count p))) 
          (length R) (length (?ms LA RA RN LP RP R Q n p P)) p))))"
        by (simp add: add.commute add.left_commute)
      then show ?thesis 
      proof -
        assume "size_atom_form (pos_countNSNP R + (pos_count p + pos_countNP Q) + pos_countNP P) (length R) (length (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p U nominalsNP P))) p + n1_0 Q (pos_countNSNP R + (pos_count p + pos_countNP Q) + pos_countNP P) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p U nominalsNP P)) + n1_0 P (pos_countNSNP R + (pos_count p + pos_countNP Q) + pos_countNP P) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p U nominalsNP P)) + n2_0 (pos_countNSNP R + (pos_count p + pos_countNP Q) + pos_countNP P) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p U nominalsNP P)) + missing R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p U nominalsNP P)) < Suc (n1_0 Q (pos_countNSNP R + (pos_count p + pos_countNP Q) + pos_countNP P) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p U nominalsNP P)) + (n1_0 P (pos_countNSNP R + pos_countNP Q + (pos_count p + pos_countNP P)) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p U nominalsNP P)) + (n2_0 (pos_countNSNP R + pos_countNP Q + (pos_count p + pos_countNP P)) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p U nominalsNP P)) + (missing R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p U nominalsNP P)) + size_atom_form (pos_countNP Q + (pos_countNP P + (pos_countNSNP R + pos_count p))) (length R) (length (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p U nominalsNP P))) p))))"
        have "n1_0 Q (pos_countNSNP R + (pos_count p + pos_countNP Q) + pos_countNP P) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U add n (nominalsForm p U nominalsNP Q) U nominalsNP P) + (n1_0 P (pos_countNSNP R + (pos_count p + pos_countNP Q) + pos_countNP P) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U add n (nominalsForm p U nominalsNP Q) U nominalsNP P) + (n2_0 (pos_countNSNP R + (pos_count p + pos_countNP Q) + pos_countNP P) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U add n (nominalsForm p U nominalsNP Q) U nominalsNP P) + (missing R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p U nominalsNP P)) + size_atom_form (pos_countNP Q + (pos_countNP P + (pos_countNSNP R + pos_count p))) (length R) (length (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p U nominalsNP P))) p))) < Suc (n1_0 Q (pos_countNSNP R + (pos_count p + pos_countNP Q) + pos_countNP P) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p U nominalsNP P)) + (n1_0 P (pos_countNSNP R + (pos_count p + pos_countNP Q) + pos_countNP P) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p U nominalsNP P)) + (n2_0 (pos_countNSNP R + (pos_count p + pos_countNP Q) + pos_countNP P) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p U nominalsNP P)) + (missing R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p U nominalsNP P)) + size_atom_form (pos_countNP Q + (pos_countNP P + (pos_countNSNP R + pos_count p))) (length R) (length (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p U nominalsNP P))) p))))"
          by (simp add: calculation)
        then have "n1_0 Q (pos_countNSNP R + (pos_count p + pos_countNP Q) + pos_countNP P) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U add n (nominalsForm p U nominalsNP Q) U nominalsNP P) + (n1_0 P (pos_countNSNP R + (pos_count p + pos_countNP Q) + pos_countNP P) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U add n (nominalsForm p U nominalsNP Q) U nominalsNP P) + (n2_0 (pos_countNSNP R + (pos_count p + pos_countNP Q) + pos_countNP P) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U add n (nominalsForm p U nominalsNP Q) U nominalsNP P) + (missing R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U add n (nominalsForm p U nominalsNP Q) U nominalsNP P) + size_atom_form (pos_countNP Q + (pos_countNP P + (pos_countNSNP R + pos_count p))) (length R) (length (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p U nominalsNP P))) p))) < Suc (n1_0 Q (pos_countNSNP R + (pos_count p + pos_countNP Q) + pos_countNP P) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p U nominalsNP P)) + (n1_0 P (pos_countNSNP R + (pos_count p + pos_countNP Q) + pos_countNP P) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p U nominalsNP P)) + (n2_0 (pos_countNSNP R + (pos_count p + pos_countNP Q) + pos_countNP P) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p U nominalsNP P)) + (missing R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p U nominalsNP P)) + size_atom_form (pos_countNP Q + (pos_countNP P + (pos_countNSNP R + pos_count p))) (length R) (length (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p U nominalsNP P))) p))))"
          by (metis (lifting) "1") 
        then have "size_atom_form (pos_countNSNP R + (pos_count p + pos_countNP Q) + pos_countNP P) (length R) (length (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U add n (nominalsForm p U nominalsNP Q) U nominalsNP P)) p + n1_0 Q (pos_countNSNP R + (pos_count p + pos_countNP Q) + pos_countNP P) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U add n (nominalsForm p U nominalsNP Q) U nominalsNP P) + n1_0 P (pos_countNSNP R + (pos_count p + pos_countNP Q) + pos_countNP P) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U add n (nominalsForm p U nominalsNP Q) U nominalsNP P) + n2_0 (pos_countNSNP R + (pos_count p + pos_countNP Q) + pos_countNP P) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U add n (nominalsForm p U nominalsNP Q) U nominalsNP P) + missing R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U add n (nominalsForm p U nominalsNP Q) U nominalsNP P) < Suc (missing R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p U nominalsNP P)) + (n1_0 Q (pos_countNSNP R + pos_countNP Q + (pos_count p + pos_countNP P)) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p U nominalsNP P)) + (size_atom_form (pos_countNSNP R + pos_countNP Q + (pos_count p + pos_countNP P)) (length R) (length (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p U nominalsNP P))) p + n1_0 P (pos_countNSNP R + pos_countNP Q + (pos_count p + pos_countNP P)) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p U nominalsNP P))) + n2_0 (pos_countNSNP R + pos_countNP Q + (pos_count p + pos_countNP P)) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p U nominalsNP P))))"
          by (simp add: add.commute add.left_commute calculation)
        then show ?thesis
          by (metis add.commute)
      qed
    qed
  qed
next
  fix LA RA :: \<open>(nat \<times> 'a) list\<close>
  fix RN :: \<open>(nat \<times> nat) list\<close>
  fix LP RP :: \<open>(nat \<times> nat) list\<close>
  fix R :: \<open>(nat \<times> nat list \<times>'a hybr_form) list\<close>
  fix Q P :: \<open>(nat \<times>'a hybr_form) list\<close>
  fix n :: nat
  fix p1 p2 :: \<open>'a hybr_form\<close>
  let ?ns = "\<lambda> LA RA RN LP RP R Q n p1 P.
    nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U 
    nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p1 U nominalsNP P)"
  let ?ms = "\<lambda> LA RA RN LP RP R Q n p1 p2 P.
    nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U 
    nominalsNSNP R U nominalsNP Q U add n ((nominalsForm p1 U nominalsForm p2) U nominalsNP P)"
  let ?psn = \<open>\<lambda> R Q P p1. pos_countNSNP R + pos_countNP Q + (pos_count p1 + pos_countNP P)\<close>
  let ?psm = \<open>\<lambda> R Q P p1 p2. 
    pos_countNSNP R + pos_countNP Q + (pos_count p1 + pos_count p2 + pos_countNP P)\<close>
  let ?show_this = "\<lambda> LA RA RN LP RP R Q n p1 p2 P.
    (let ns = ?ns LA RA RN LP RP R Q n p1 P in
    let ps = ?psn R Q P p1 in
      n1_0 Q ps R ns + 
      (size_atom_form ps (length R) (length ns) p1 + 
      n1_0 P ps R ns) + n2_0 ps R ns +
      missing R ns) < (
    let ns = ?ms LA RA RN LP RP R Q n p1 p2 P in 
    let ps = ?psm R Q P p1 p2 in Suc(
      n1_0 Q ps R ns +
      (size_atom_form ps (length R) (length ns) p1 + size_atom_form ps (length R) (length ns) p2 +
      n1_0 P ps R ns) +
      n2_0 ps R ns +
      missing R ns))"
  show "?show_this LA RA RN LP RP R Q n p1 p2 P"
  proof-
    have isset: "
      is_set (?ns LA RA RN LP RP R Q n p1 P) \<and> is_set (?ms LA RA RN LP RP R Q n p1 p2 P)"
      using NA_is_set union_is_set by auto

    have setsub: "sub_set (?ns LA RA RN LP RP R Q n p1 P) 
                          (?ms LA RA RN LP RP R Q n p1 p2 P)" 
    proof -
      have \<open>set_equal (?ns LA RA RN LP RP R Q n p1 P) 
            (add n (nominalsForm p1 U (ns_0 LA RA RN LP RP R Q P)))\<close>
        apply simp
        by (smt (z3) Un_insert_left add_simp sup_assoc sup_left_commute union_simp)
      moreover have \<open>set_equal (?ms LA RA RN LP RP R Q n p1 p2 P) 
            (nominalsForm p2 U (add n (nominalsForm p1 U (ns_0 LA RA RN LP RP R Q P))))\<close>
        apply simp
        by (smt (z3) Un_insert_left add_simp sup_assoc sup_left_commute union_simp)
      moreover then have \<open>sub_set (add n (nominalsForm p1 U (ns_0 LA RA RN LP RP R Q P))) ...\<close> 
        by (meson sub_set_union2)
      ultimately show ?thesis 
        by simp
    qed
    then have 1: "
      missing R (?ns LA RA RN LP RP R Q n p1 P) \<le> missing R (?ms LA RA RN LP RP R Q n p1 p2 P)" 
      using setsub by (meson isset missing_sub_set2)
    moreover have "
      length (?ns LA RA RN LP RP R Q n p1 P) \<le> length (?ms LA RA RN LP RP R Q n p1 p2 P)" 
      using isset set_size_equal setsub sub_set_size by blast
    ultimately have 2: "\<forall> r p. 
      size_atom_form (?psn R Q P p1) r (length (?ns LA RA RN LP RP R Q n p1 P)) p \<le> 
      size_atom_form (?psm R Q P p1 p2) r (length (?ms LA RA RN LP RP R Q n p1 p2 P)) p" 
      by (simp add: size_atom_form_size_ns) 
    have \<open>(
      let ns = ?ns LA RA RN LP RP R Q n p1 P in 
      let ps = ?psn R Q P p1 in
        n1_0 Q ps R ns) \<le> (
      let ns = ?ms LA RA RN LP RP R Q n p1 p2 P in
      let ps = ?psm R Q P p1 p2 in
        n1_0 Q ps R ns) \<and> (
      let ns = ?ns LA RA RN LP RP R Q n p1 P in 
      let ps = ?psn R Q P p1 in
        n1_0 P ps R ns) \<le> (
      let ns = ?ms LA RA RN LP RP R Q n p1 p2 P in 
      let ps = ?psm R Q P p1 p2 in
        n1_0 P ps R ns) \<and> (
      let ns = ?ns LA RA RN LP RP R Q n p1 P in 
      let ps = ?psn R Q P p1 in
        n2_0 ps R ns) \<le> (
      let ns = ?ms LA RA RN LP RP R Q n p1 p2 P in 
      let ps = ?psm R Q P p1 p2 in
        n2_0 ps R ns)\<close> 
      by (auto simp add: lesser_sum 2 lesser_add)
    then have \<open>(
      let ns = ?ns LA RA RN LP RP R Q n p1 P in 
      let ps = ?psn R Q P p1 in
        size_atom_form ps (length R) (length ns) p1 +
        n1_0 Q ps R ns + n1_0 P ps R ns + n2_0 ps R ns + missing R ns) \<le> (
      let ns = ?ms LA RA RN LP RP R Q n p1 p2 P in
      let ps = ?psm R Q P p1 p2 in
        size_atom_form ps (length R) (length ns) p1 + 
        size_atom_form ps (length R) (length ns) p2 +
        n1_0 Q ps R ns + n1_0 P ps R ns + n2_0 ps R ns + missing R ns)\<close>
      by (metis "1" 2 add.commute lesser_add trans_le_add2) 
    then show "?show_this LA RA RN LP RP R Q n p1 p2 P" 
      by (smt (z3) add.commute add.left_commute less_Suc_eq_le)
  qed
next
  fix LA RA :: \<open>(nat \<times> 'a) list\<close>
  fix RN :: \<open>(nat \<times> nat) list\<close>
  fix LP RP :: \<open>(nat \<times> nat) list\<close>
  fix R :: \<open>(nat \<times> nat list \<times>'a hybr_form) list\<close>
  fix Q P :: \<open>(nat \<times>'a hybr_form) list\<close>
  fix n :: nat
  fix p1 p2 :: \<open>'a hybr_form\<close>
  let ?ns = "\<lambda> LA RA RN LP RP R Q n p2 P.
    nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U 
    nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p2 U nominalsNP P)"
  let ?ms = "\<lambda> LA RA RN LP RP R Q n p1 p2 P.
    nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U 
    nominalsNSNP R U nominalsNP Q U add n ((nominalsForm p1 U nominalsForm p2) U nominalsNP P)"
  let ?psn = \<open>\<lambda> R Q P p2. pos_countNSNP R + pos_countNP Q + (pos_count p2 + pos_countNP P)\<close>
  let ?psm = \<open>\<lambda> R Q P p1 p2. 
    pos_countNSNP R + pos_countNP Q + (pos_count p1 + pos_count p2 + pos_countNP P)\<close>
  let ?show_this = "\<lambda> LA RA RN LP RP R Q n p1 p2 P.
    (let ns = ?ns LA RA RN LP RP R Q n p2 P in
    let ps = ?psn R Q P p2 in
      n1_0 Q ps R ns + 
      (size_atom_form ps (length R) (length ns) p2 + 
      n1_0 P ps R ns) + n2_0 ps R ns +
      missing R ns) < (
    let ns = ?ms LA RA RN LP RP R Q n p1 p2 P in 
    let ps = ?psm R Q P p1 p2 in Suc(
      n1_0 Q ps R ns +
      (size_atom_form ps (length R) (length ns) p1 + size_atom_form ps (length R) (length ns) p2 +
      n1_0 P ps R ns) +
      n2_0 ps R ns +
      missing R ns))"
  show "?show_this LA RA RN LP RP R Q n p1 p2 P"
  proof-
    have isset: "
      is_set (?ns LA RA RN LP RP R Q n p1 P) \<and> is_set (?ms LA RA RN LP RP R Q n p1 p2 P)"
      using NA_is_set union_is_set by auto

    have setsub: "sub_set (?ns LA RA RN LP RP R Q n p2 P) 
                          (?ms LA RA RN LP RP R Q n p1 p2 P)" 
    proof -
      have \<open>set_equal (?ns LA RA RN LP RP R Q n p2 P) 
            (add n (nominalsForm p2 U (ns_0 LA RA RN LP RP R Q P)))\<close>
        apply simp
        by (smt (z3) Un_insert_left add_simp sup_assoc sup_left_commute union_simp)
      moreover have \<open>set_equal (?ms LA RA RN LP RP R Q n p1 p2 P) 
            (nominalsForm p1 U (add n (nominalsForm p2 U (ns_0 LA RA RN LP RP R Q P))))\<close>
        apply simp
        by (smt (z3) Un_insert_left add_simp sup_assoc sup_left_commute union_simp)
      moreover then have \<open>sub_set (add n (nominalsForm p2 U (ns_0 LA RA RN LP RP R Q P))) ...\<close> 
        by (meson sub_set_union2)
      ultimately show ?thesis 
        by simp
    qed
    then have 1: "
      missing R (?ns LA RA RN LP RP R Q n p2 P) \<le> missing R (?ms LA RA RN LP RP R Q n p1 p2 P)" 
      using setsub by (meson NA_is_set missing_sub_set2 union_is_set)
    moreover have "
      length (?ns LA RA RN LP RP R Q n p2 P) \<le> length (?ms LA RA RN LP RP R Q n p1 p2 P)" 
      by (meson NA_is_set setsub sub_set_size union_is_set)
    ultimately have 2: "\<forall> r p. 
      size_atom_form (?psn R Q P p2) r (length (?ns LA RA RN LP RP R Q n p2 P)) p \<le> 
      size_atom_form (?psm R Q P p1 p2) r (length (?ms LA RA RN LP RP R Q n p1 p2 P)) p" 
      by (simp add: size_atom_form_size_ns) 
    have \<open>(
      let ns = ?ns LA RA RN LP RP R Q n p2 P in 
      let ps = ?psn R Q P p2 in
        n1_0 Q ps R ns) \<le> (
      let ns = ?ms LA RA RN LP RP R Q n p1 p2 P in
      let ps = ?psm R Q P p1 p2 in
        n1_0 Q ps R ns) \<and> (
      let ns = ?ns LA RA RN LP RP R Q n p2 P in 
      let ps = ?psn R Q P p2 in
        n1_0 P ps R ns) \<le> (
      let ns = ?ms LA RA RN LP RP R Q n p1 p2 P in 
      let ps = ?psm R Q P p1 p2 in
        n1_0 P ps R ns) \<and> (
      let ns = ?ns LA RA RN LP RP R Q n p2 P in 
      let ps = ?psn R Q P p2 in
        n2_0 ps R ns) \<le> (
      let ns = ?ms LA RA RN LP RP R Q n p1 p2 P in 
      let ps = ?psm R Q P p1 p2 in
        n2_0 ps R ns)\<close> 
      by (auto simp add: lesser_sum 2 lesser_add)
    then have \<open>(
      let ns = ?ns LA RA RN LP RP R Q n p2 P in 
      let ps = ?psn R Q P p2 in
        size_atom_form ps (length R) (length ns) p2 +
        n1_0 Q ps R ns + n1_0 P ps R ns + n2_0 ps R ns + missing R ns) \<le> (
      let ns = ?ms LA RA RN LP RP R Q n p1 p2 P in
      let ps = ?psm R Q P p1 p2 in
        size_atom_form ps (length R) (length ns) p1 + 
        size_atom_form ps (length R) (length ns) p2 +
        n1_0 Q ps R ns + n1_0 P ps R ns + n2_0 ps R ns + missing R ns)\<close>
      by (metis "1" 2 lesser_add trans_le_add2) 
    then show "?show_this LA RA RN LP RP R Q n p1 p2 P" 
      by (smt (z3) add.commute add.left_commute less_Suc_eq_le)
  qed
next
  fix LA RA :: \<open>(nat \<times> 'a) list\<close>
  fix RN :: \<open>(nat \<times> nat) list\<close>
  fix LP RP :: \<open>(nat \<times> nat) list\<close>
  fix R :: \<open>(nat \<times> nat list \<times>'a hybr_form) list\<close>
  fix Q P :: \<open>(nat \<times>'a hybr_form) list\<close>
  fix n1 n2 :: nat
  fix p :: \<open>'a hybr_form\<close>
  let ?ns = "\<lambda> LA RA RN LP RP R Q n2 p P.
    nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U 
    nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n2 (nominalsForm p U nominalsNP P)"
  let ?ms = "\<lambda> LA RA RN LP RP R Q n1 n2 p P.
    nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U 
    nominalsNSNP R U nominalsNP Q U add n1 (add n2 (nominalsForm p) U nominalsNP P)"
  let ?psn = \<open>\<lambda> R Q P p. pos_countNSNP R + pos_countNP Q + (pos_count p + pos_countNP P)\<close>
  let ?show_this = "\<lambda> LA RA RN LP RP R Q n1 n2 p P.
    (let ns = ?ns LA RA RN LP RP R Q n2 p P in
    let ps = ?psn R Q P p in
      n1_0 Q ps R ns + 
      (size_atom_form ps (length R) (length ns) p + 
      n1_0 P ps R ns) + n2_0 ps R ns +
      missing R ns) < (
    let ns = ?ms LA RA RN LP RP R Q n1 n2 p P in 
    let ps = ?psn R Q P p in Suc(
      n1_0 Q ps R ns +
      (size_atom_form ps (length R) (length ns) p +
      n1_0 P ps R ns) +
      n2_0 ps R ns +
      missing R ns))"
  show "?show_this LA RA RN LP RP R Q n1 n2 p P"
  proof-
    have isset: "
      is_set (?ns LA RA RN LP RP R Q n2 p P) \<and> is_set (?ms LA RA RN LP RP R Q n1 n2 p P)"
      using NA_is_set union_is_set by auto

    have setsub: "sub_set (?ns LA RA RN LP RP R Q n2 p P) 
                          (?ms LA RA RN LP RP R Q n1 n2 p P)" 
    proof -
      have \<open>set_equal (?ns LA RA RN LP RP R Q n2 p P) 
            (add n2 (nominalsForm p U (ns_0 LA RA RN LP RP R Q P)))\<close>
        apply simp
        by (smt (z3) Un_insert_left add_simp sup_assoc sup_left_commute union_simp)
      moreover have \<open>set_equal (?ms LA RA RN LP RP R Q n1 n2 p P) 
            (add n1 (add n2 (nominalsForm p U (ns_0 LA RA RN LP RP R Q P))))\<close>
        apply simp
        by (smt (z3) Un_insert_left add_simp sup_assoc sup_left_commute union_simp)
      moreover have \<open>sub_set (add n2 (nominalsForm p U (ns_0 LA RA RN LP RP R Q P))) ...\<close>
        by (metis sub_set_union1 union.simps(1) union.simps(2))
      ultimately show ?thesis 
        by simp
    qed
    then have 1: "
      missing R (?ns LA RA RN LP RP R Q n2 p P) \<le> missing R (?ms LA RA RN LP RP R Q n1 n2 p P)" 
      using setsub by (meson isset missing_sub_set2)
    moreover have "
      length (?ns LA RA RN LP RP R Q n2 p P) \<le> length (?ms LA RA RN LP RP R Q n1 n2 p P)" 
      using isset set_size_equal setsub sub_set_size by blast
    ultimately have 2: "\<forall> r p'. 
      size_atom_form (?psn R Q P p) r (length (?ns LA RA RN LP RP R Q n2 p P)) p' \<le> 
      size_atom_form (?psn R Q P p) r (length (?ms LA RA RN LP RP R Q n1 n2 p P)) p'" 
      by (simp add: size_atom_form_size_ns) 
    have \<open>(
      let ns = ?ns LA RA RN LP RP R Q n2 p P in 
      let ps = ?psn R Q P p in
        n1_0 Q ps R ns) \<le> (
      let ns = ?ms LA RA RN LP RP R Q n1 n2 p P in
      let ps = ?psn R Q P p in
        n1_0 Q ps R ns) \<and> (
      let ns = ?ns LA RA RN LP RP R Q n2 p P in 
      let ps = ?psn R Q P p in
        n1_0 P ps R ns) \<le> (
      let ns = ?ms LA RA RN LP RP R Q n1 n2 p P in 
      let ps = ?psn R Q P p in
        n1_0 P ps R ns) \<and> (
      let ns = ?ns LA RA RN LP RP R Q n2 p P in 
      let ps = ?psn R Q P p in
        n2_0 ps R ns) \<le> (
      let ns = ?ms LA RA RN LP RP R Q n1 n2 p P in 
      let ps = ?psn R Q P p in
        n2_0 ps R ns)\<close> 
      by (auto simp add: lesser_sum 2 lesser_add)
    then have \<open>(
      let ns = ?ns LA RA RN LP RP R Q n2 p P in 
      let ps = ?psn R Q P p in
        size_atom_form ps (length R) (length ns) p +
        n1_0 Q ps R ns + n1_0 P ps R ns + n2_0 ps R ns + missing R ns) \<le> (
      let ns = ?ms LA RA RN LP RP R Q n1 n2 p P in
      let ps = ?psn R Q P p in
        size_atom_form ps (length R) (length ns) p +
        n1_0 Q ps R ns + n1_0 P ps R ns + n2_0 ps R ns + missing R ns)\<close>
      by (metis 1 2 lesser_add) 
    then show "?show_this LA RA RN LP RP R Q n1 n2 p P" 
      by (smt (z3) add.commute add.left_commute less_Suc_eq_le)
  qed
next
  fix LA RA :: \<open>(nat \<times> 'a) list\<close>
  fix RN :: \<open>(nat \<times> nat) list\<close>
  fix LP RP :: \<open>(nat \<times> nat) list\<close>
  fix R :: \<open>(nat \<times> nat list \<times>'a hybr_form) list\<close>
  fix Q P :: \<open>(nat \<times>'a hybr_form) list\<close>
  fix n :: nat
  fix p :: \<open>'a hybr_form\<close>
  let ?ns = "\<lambda> LA RA RN LP RP R Q n p P.
    nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U 
    nominalsNN RP U (nominalsNSNP R U add n ([] U nominalsForm p)) U nominalsNP Q U nominalsNP P"
  let ?ms = "\<lambda> LA RA RN LP RP R Q n p P.
    nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U 
    nominalsNSNP R U nominalsNP Q U add n (nominalsForm p U nominalsNP P)"
  let ?n1 = \<open>\<lambda> Q ps R ns. \<Sum>(u, y)\<leftarrow>Q. size_atom_form ps (Suc (length R)) (length ns) y\<close>
  let ?n2 = \<open>\<lambda> ps R ns. \<Sum>(u, u', p)\<leftarrow>R. Suc (size_atom_form ps (Suc (length R)) (length ns) p)\<close>
  let ?psn = \<open>\<lambda> R Q P p. pos_count p + pos_countNSNP R + pos_countNP Q + pos_countNP P\<close>
  let ?psm = \<open>\<lambda> R Q P p. pos_countNSNP R + pos_countNP Q + (pos_count p + pos_countNP P)\<close>
  let ?show_this = "\<lambda> LA RA RN LP RP R Q n p P. (
    let ns = ?ns LA RA RN LP RP R Q n p P in
    let ps = ?psn R Q P p in Suc (
      ?n1 Q ps R ns +
      ?n1 P ps R ns +
      (size_atom_form ps (Suc (length R)) (length ns) p +
      ?n2 ps R ns) +
      (missing' [] ns + missing R ns))) < (
    let ns = ?ms LA RA RN LP RP R Q n p P in  Suc (Suc (Suc (
      n1_0 Q (Suc (?psm R Q P p)) R ns +
      (?psm R Q P p + length R + length ns +
      size_atom_form (Suc (?psm R Q P p)) (length R) (length ns) p +
      n1_0 P (Suc (?psm R Q P p)) R ns) +
      n2_0 (Suc (?psm R Q P p)) R ns +
      missing R ns))))"
  show "?show_this LA RA RN LP RP R Q n p P"
  proof-
    have isset: "
      is_set (?ns LA RA RN LP RP R Q n p P) \<and> is_set (?ms LA RA RN LP RP R Q n p P)"
      using NA_is_set union_is_set by auto

    have setequal: "set_equal (?ns LA RA RN LP RP R Q n p P) 
                              (?ms LA RA RN LP RP R Q n p P)" 
    proof -
      have \<open>set_equal (?ns LA RA RN LP RP R Q n p P) 
        (add n (([] U nominalsForm p) U (ns_0 LA RA RN LP RP R Q P)))\<close>
        apply simp
        by (smt (z3) Un_insert_left add_simp sup_assoc sup_left_commute union_simp)
      moreover have \<open>set_equal ...
        (add n (nominalsForm p U (ns_0 LA RA RN LP RP R Q P)))\<close> 
        by (meson equal_add union_with_equal2 unionaddnt) 
      moreover have \<open>set_equal (?ms LA RA RN LP RP R Q n p P) 
            (add n (nominalsForm p U (ns_0 LA RA RN LP RP R Q P)))\<close>
        apply simp
        by (smt (z3) Un_insert_left add_simp sup_assoc sup_left_commute union_simp)
      ultimately show ?thesis 
        by simp
    qed
    then have 1: "
      missing R (?ns LA RA RN LP RP R Q n p P) \<le> missing R (?ms LA RA RN LP RP R Q n p P)" 
      using setequal isset missing_set_equal2 
      by (metis (no_types, lifting) order_refl)
    have 3: "
      length (?ns LA RA RN LP RP R Q n p P) = length (?ms LA RA RN LP RP R Q n p P)" 
      using isset set_size_equal setequal sub_set_size by blast
    then have 4: \<open>
      ?psn R Q P p + Suc (length R) + length (?ns LA RA RN LP RP R Q n p P) = 
      (Suc (?psm R Q P p)) + length R + length (?ms LA RA RN LP RP R Q n p P) \<close> 
      by auto
    have \<open>(
      ?n1 Q (?psn R Q P p) R (?ns LA RA RN LP RP R Q n p P)) \<le> (
      n1_0 Q (Suc (?psm R Q P p)) R (?ms LA RA RN LP RP R Q n p P))\<close> 
    proof-
      have "
        (\<Sum>(u, y)\<leftarrow>Q. size_atom_form (?psn R Q P p) (Suc (length R)) 
          (length (?ns LA RA RN LP RP R Q n p P)) y) \<le>
        (\<Sum>(u, y)\<leftarrow>Q. size_atom_form (Suc (?psm R Q P p)) (length R) 
          (length (?ms LA RA RN LP RP R Q n p P)) y)" 
        by (simp add: 3 4 n1_0_suc_dec)
      then show ?thesis 
        by simp
    qed
    moreover have "(
      ?n1 P (?psn R Q P p) R (?ns LA RA RN LP RP R Q n p P)) \<le> (
      n1_0 P (Suc (?psm R Q P p)) R (?ms LA RA RN LP RP R Q n p P))" 
    proof-
      have "
        (\<Sum>(u, y)\<leftarrow>P. size_atom_form (?psn R Q P p) (Suc (length R)) 
          (length (?ns LA RA RN LP RP R Q n p P)) y) \<le>
        (\<Sum>(u, y)\<leftarrow>P. size_atom_form (Suc (?psm R Q P p)) (length R) 
          (length (?ms LA RA RN LP RP R Q n p P)) y)" 
        by (simp add: 3 4 n1_0_suc_dec)
      then show ?thesis 
        by simp
    qed
    moreover have "
      ?n2 (?psn R Q P p) R (?ns LA RA RN LP RP R Q n p P) \<le> 
      n2_0 (Suc (?psm R Q P p)) R (?ms LA RA RN LP RP R Q n p P) + length R" 
    proof-
      have \<open>
        (?psn R Q P p) + (Suc (length R)) + (length (?ns LA RA RN LP RP R Q n p P)) \<le>
        (Suc (?psm R Q P p)) + (length R) + (length (?ms LA RA RN LP RP R Q n p P))\<close>
        using "4" by auto
      then have \<open>
        (\<Sum>(u, uu, p')\<leftarrow>R. Suc (size_atom_form (?psn R Q P p) (Suc (length R)) 
          (length (?ns LA RA RN LP RP R Q n p P)) p')) \<le> 
        (\<Sum>(u, uu, p')\<leftarrow>R. Suc (size_atom_form (Suc (?psm R Q P p)) (length R) 
          (length (?ms LA RA RN LP RP R Q n p P)) p'))\<close>  
        using n2_0_suc_dec
      proof -(*generated proof*)
        have "\<And>n na nb nc nd ne ps. \<not> n + (na + nb) \<le> nc + (nd + ne) \<or> 
          (\<Sum>(nc, ns, h)\<leftarrow>(ps::(nat \<times> nat list \<times> 'a hybr_form) list). 
            Suc (size_atom_form n nb na h)) \<le> (\<Sum>(n, ns, h)\<leftarrow>ps. Suc (size_atom_form nc ne nd h))"
          by (simp add: n2_0_suc_dec)
        then have "
          (\<Sum>(na, ns, h)\<leftarrow>R. Suc (size_atom_form (?psn R Q P p) (Suc (length R)) 
            (length (?ms LA RA RN LP RP R Q n p P)) h)) \<le> 
          n2_0 (Suc (?psm R Q P p)) R 
            (?ms LA RA RN LP RP R Q n p P)"
          by force
        then show ?thesis
          by (metis "3") 
      qed
      then show ?thesis 
        by (simp add: sum_suc)
    qed
    moreover have "(
      (missing' [] (?ns LA RA RN LP RP R Q n p P))) \<le> (
      length (?ms LA RA RN LP RP R Q n p P))" 
      by (metis "3" missing_less)
    moreover have "(
      size_atom_form (?psn R Q P p) (Suc (length R)) (length (?ns LA RA RN LP RP R Q n p P)) p) \<le> (
      size_atom_form (Suc (?psm R Q P p)) (length R) (length (?ms LA RA RN LP RP R Q n p P)) p)"
      by (smt (z3) "3" "4" add.assoc add_right_imp_eq eq_iff size_atom_suc_dec)
    ultimately have "(
      let ns = ?ns LA RA RN LP RP R Q n p P in
      let ps = ?psn R Q P p in 
        ?n1 Q ps R ns +
        ?n1 P ps R ns +
        ?n2 ps R ns +
        missing' [] ns +
        size_atom_form ps (Suc (length R)) (length ns) p +
        missing R ns) \<le> (
      let ns = ?ms LA RA RN LP RP R Q n p P in
        n1_0 Q (Suc (?psm R Q P p)) R ns +
        n1_0 P (Suc (?psm R Q P p)) R ns +
        (n2_0 (Suc (?psm R Q P p)) R ns + length R) +
        length ns +
        size_atom_form (Suc (?psm R Q P p)) (length R) (length ns) p + 
        missing R ns)" by (metis 1 lesser_add)
    then show "?show_this LA RA RN LP RP R Q n p P" 
      by (simp add: Let_def)
  qed
next
  fix LA RA :: \<open>(nat \<times> 'a) list\<close>
  fix RN :: \<open>(nat \<times> nat) list\<close>
  fix LP RP :: \<open>(nat \<times> nat) list\<close>
  fix R :: \<open>(nat \<times> nat list \<times>'a hybr_form) list\<close>
  fix Q :: \<open>(nat \<times>'a hybr_form) list\<close>
  fix n :: nat
  let ?ns = "\<lambda> LA RA RN LP RP R Q n.
    add n (nominalsNA LA) U nominalsNA RA U nominalsNN RN U nominalsNN LP U 
    nominalsNN RP U nominalsNSNP R U nominalsNP Q"
  let ?ms = "\<lambda> LA RA RN LP RP R Q n.
    nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U 
    nominalsNSNP R U  add n ([] U nominalsNP Q)"
  let ?show_this = "\<lambda> LA RA RN LP RP R Q n.
    (let ns = ?ns LA RA RN LP RP R Q n in 
    let ps = pos_countNSNP R + pos_countNP Q in
      n1_0 Q ps R ns +
      n2_0 ps R ns +
      missing R ns) < (
    let ns = ?ms LA RA RN LP RP R Q n in
    let ps = pos_countNSNP R + pos_countNP Q in Suc (
      n1_0 Q ps R ns +
      n2_0 ps R ns +
      missing R ns))"
  show "?show_this LA RA RN LP RP R Q n"
  proof-
    have isset: "is_set (?ns LA RA RN LP RP R Q n) \<and> is_set (?ms LA RA RN LP RP R Q n)"
      by (simp add: NA_is_set add_is_set union_is_set)

    have setequal: "set_equal (?ns LA RA RN LP RP R Q n) (?ms LA RA RN LP RP R Q n)" 
    proof -
      have "
        set (?ns LA RA RN LP RP R Q n) =
        set (add n (ns_1 LA RA RN LP RP R Q))" 
        by (metis Un_insert_left add_simp union_simp)
      then show ?thesis 
        by (smt (z3) Un_insert_right add_simp set_equal_iff union_simp unionaddnt)
    qed

    then have "
      missing R (?ns LA RA RN LP RP R Q n) = missing R (?ms LA RA RN LP RP R Q n)" 
      using isset missing_set_equal2 by blast
    moreover have "
      length (?ns LA RA RN LP RP R Q n) = length (?ms LA RA RN LP RP R Q n)" 
      using isset set_size_equal setequal by blast
    ultimately show "?show_this LA RA RN LP RP R Q n" 
      by (metis lessI)
  qed
next
  fix LA RA :: \<open>(nat \<times> 'a) list\<close>
  fix RN :: \<open>(nat \<times> nat) list\<close>
  fix LP RP :: \<open>(nat \<times> nat) list\<close>
  fix R :: \<open>(nat \<times> nat list \<times>'a hybr_form) list\<close>
  fix Q :: \<open>(nat \<times>'a hybr_form) list\<close>
  fix n1 n2 :: nat
  let ?mLA = "mergeNA LA n1 n2"
  let ?mRA = "mergeNA RA n1 n2"
  let ?mRN = "mergeNN RN n1 n2"
  let ?mLP = "mergeNN LP n1 n2"
  let ?mRP = "mergeNN RP n1 n2"
  let ?mR = "mergeNSNP R n1 n2"
  let ?mQ = "mergeNP Q n1 n2"
  let ?pns = "pos_countNSNP ?mR + pos_countNP ?mQ"
  let ?pms = "pos_countNSNP R + pos_countNP Q"
  let ?ns = "
    ns_1 ?mLA ?mRA ?mRN ?mLP ?mRP ?mR ?mQ"
  let ?ms = "
    nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U 
    nominalsNSNP R U add n1 ([n2] U nominalsNP Q)"
  let ?show_this = "
    (let ns = ?ns in 
    let ps = ?pns in
      n1_0 ?mQ ps ?mR ns + 
      n2_0 ps ?mR ns +
      missing ?mR ns) < (
    let ns = ?ms in
    let ps = ?pms in Suc (
      n1_0 Q ps R ns +
      n2_0 ps R ns +
      missing R ns))"
  show "?show_this"
  proof-
    have isset: "
      is_set (?ns) \<and> is_set (?ms)"
      using NA_is_set union_is_set by auto

    have subset: "sub_set (?ns) (?ms)" 
      by (smt (z3) ListSet.member.simps(2) add_def member_mergeNA member_mergeNN member_mergeNP 
          member_mergeNSNP member_sub_set union_member)
    have 1:"
      missing ?mR (?ns) \<le> missing R (?ms)" 
    proof-
      have 2:\<open>is_set (ns_1 LA RA RN LP RP R Q)\<close>
        using NA_is_set union_is_set by auto
      have "set_equal (
        ns_1 (mergeNA LA n1 n2) (mergeNA RA n1 n2) (mergeNN RN n1 n2) (mergeNN LP n1 n2) 
          (mergeNN RP n1 n2) (mergeNSNP R n1 n2) (mergeNP Q n1 n2)) (
        mergeNS (ns_1 LA RA RN LP RP R Q) n1 n2)" 
        using merge_noms by blast
      then have "missing ?mR 
        (ns_1 (mergeNA LA n1 n2) (mergeNA RA n1 n2) (mergeNN RN n1 n2) (mergeNN LP n1 n2) 
          (mergeNN RP n1 n2) (mergeNSNP R n1 n2) (mergeNP Q n1 n2)) \<le> 
        missing ?mR ..."
        by (meson isset missing_sub_set2 set_equal_def sub_set_def) 
      moreover have \<open>... \<le> missing R (ns_1 LA RA RN LP RP R Q)\<close>
        using missing_merge by auto
      moreover have \<open>... \<le> missing R (?ms)\<close> 
        by (smt (z3) "2" ListSet.member.simps(1) isset member_sub_set missing_sub_set2 
            removent2 set_equal_def union_member unionadd1)
      ultimately show ?thesis 
        by linarith
    qed
    moreover have 2:"
      length ?ns \<le> length ?ms"
      using isset sub_set_size subset by blast
    moreover have "
      length ?mR = length R"
      by (metis merge_lengthNSNP)
    moreover have 3:"?pns = ?pms"
      by (simp add: pos_mergeNP pos_mergeNSNP)
    ultimately have 4:"n1_0 ?mQ ?pns ?mR ?ns \<le> n1_0 Q ?pms R ?ms" 
      by (simp add: merge_n1_0)
    have \<open>n2_0 ?pns ?mR ?ns \<le> n2_0 ?pms R ?ms\<close>  
      by (simp add: 2 3 merge_n2_0)
    then show "?show_this" 
      by (metis 1 4 add_le_mono le_imp_less_Suc)
  qed
next
  fix LA RA :: \<open>(nat \<times> 'a) list\<close>
  fix RN :: \<open>(nat \<times> nat) list\<close>
  fix LP RP :: \<open>(nat \<times> nat) list\<close>
  fix R :: \<open>(nat \<times> nat list \<times>'a hybr_form) list\<close>
  fix Q :: \<open>(nat \<times>'a hybr_form) list\<close>
  fix n :: nat
  fix p :: "'a hybr_form"
  let ?ns = "\<lambda> LA RA RN LP RP R Q n p.
    nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U 
    nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p)"
  let ?ms = "\<lambda> LA RA RN LP RP R Q n p.
    nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U 
    nominalsNN RP U nominalsNSNP R U add n (nominalsForm p U nominalsNP Q)"
  let ?psn = "\<lambda> R Q p. pos_countNSNP R + pos_countNP Q + pos_count p"
  let ?psm = "\<lambda> R Q p. pos_countNSNP R + (pos_count p + pos_countNP Q)"
  let ?show_this = "\<lambda> LA RA RN LP RP R Q n p.
    (let ns = ?ns LA RA RN LP RP R Q n p in 
    let ps = ?psn R Q p in
      n1_0 Q ps R ns + size_atom_form ps (length R) (length ns) p + n2_0 ps R ns + missing R ns) < (
    let ns = ?ms LA RA RN LP RP R Q n p in
    let ps = ?psm R Q p in Suc (
      size_atom_form ps (length R) (length ns) p + n1_0 Q ps R ns + n2_0 ps R ns + missing R ns))"
  show "?show_this LA RA RN LP RP R Q n p"
  proof-
    have isset: "
      is_set (?ns LA RA RN LP RP R Q n p) \<and> is_set (?ms LA RA RN LP RP R Q n p)"
      using NA_is_set union_is_set by auto

    have setequal: "set_equal (?ns LA RA RN LP RP R Q n p) (?ms LA RA RN LP RP R Q n p)"
    proof -
      have "set_equal (?ns LA RA RN LP RP R Q n p) (
        nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U 
        nominalsNN RP U nominalsNSNP R U add n (nominalsNP Q U nominalsForm p))"
        by (metis set_equal_commutative union_with_equal unionadd2)
      moreover have \<open>set_equal ... (
        nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U 
        nominalsNN RP U add n (nominalsNSNP R U nominalsNP Q U nominalsForm p))\<close>
        by (metis set_equal_commutative union_with_equal unionadd2)
      moreover have \<open>set_equal ... (
        nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U 
        add n (nominalsNN RP U nominalsNSNP R U nominalsNP Q U nominalsForm p))\<close>
        by (metis set_equal_commutative union_with_equal unionadd2)
      moreover have \<open>set_equal ... (
        nominalsNA LA U nominalsNA RA U nominalsNN RN U add n (nominalsNN LP U 
        nominalsNN RP U nominalsNSNP R U nominalsNP Q U nominalsForm p))\<close>
        by (metis set_equal_commutative union_with_equal unionadd2)
      moreover have \<open>set_equal ... (
        nominalsNA LA U nominalsNA RA U add n (nominalsNN RN U nominalsNN LP U 
        nominalsNN RP U nominalsNSNP R U nominalsNP Q U nominalsForm p))\<close>
        by (metis set_equal_commutative union_with_equal unionadd2)
      moreover have \<open>set_equal ... (
        nominalsNA LA U add n (nominalsNA RA U nominalsNN RN U nominalsNN LP U 
        nominalsNN RP U nominalsNSNP R U nominalsNP Q U nominalsForm p))\<close>
        by (metis set_equal_commutative union_with_equal unionadd2)
      moreover have \<open>set_equal ... (
        add n (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U 
        nominalsNN RP U nominalsNSNP R U nominalsNP Q U nominalsForm p))\<close>
        by (metis set_equal_commutative unionadd2)
      moreover have "set_equal ... (add n (nominalsForm p U ns_1 LA RA RN LP RP R Q))" 
      proof-
        have \<open>
          set_equal (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U 
              nominalsNN RP U nominalsNSNP R U nominalsNP Q U nominalsForm p)
            (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsForm p U nominalsNN LP U 
              nominalsNN RP U nominalsNSNP R U nominalsNP Q)\<close> 
          by (meson set_equal_associative union_associative union_commutative union_with_equal)
        moreover have \<open>
          set_equal ...
            (nominalsForm p U nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U 
              nominalsNN RP U nominalsNSNP R U nominalsNP Q)\<close> 
          by (meson set_equal_associative union_associative union_commutative union_with_equal)
        ultimately show ?thesis 
          by (meson equal_add set_equal_associative)
      qed
      moreover have "set_equal 
        (?ms LA RA RN LP RP R Q n p)
        (add n (nominalsForm p U ns_1 LA RA RN LP RP R Q))"
        apply simp
        by (smt (z3) Un_insert_left add_simp sup_assoc sup_left_commute union_simp)
      ultimately show ?thesis
        by blast
    qed
    then have 1:"
      missing R (?ns LA RA RN LP RP R Q n p) = missing R (?ms LA RA RN LP RP R Q n p)" 
      using isset missing_set_equal2
      by blast
    have 2:"
      length (?ns LA RA RN LP RP R Q n p) = length (?ms LA RA RN LP RP R Q n p)" 
      using isset set_size_equal setequal 
      by meson
    have 3:"?psn R Q p = ?psm R Q p"
      by simp
    have \<open>
      n1_0 Q (?psn R Q p) R (?ns LA RA RN LP RP R Q n p) \<le> 
      n1_0 Q (?psm R Q p) R (?ms LA RA RN LP RP R Q n p)\<close> 
      by (metis (mono_tags) "2" add.commute dual_order.eq_iff group_cancel.add2)
    moreover have \<open>
      n2_0 (?psn R Q p) R (?ns LA RA RN LP RP R Q n p) \<le>   
      n2_0 (?psm R Q p) R (?ms LA RA RN LP RP R Q n p)\<close> 
      by (simp add: "2" add.commute add.left_commute)
    moreover have \<open>
      size_atom_form (?psn R Q p) (length R) (length (?ns LA RA RN LP RP R Q n p)) p \<le> 
        size_atom_form (?psm R Q p) (length R) (length (?ms LA RA RN LP RP R Q n p)) p\<close> 
      by (simp add: 2 3)
    show "?show_this LA RA RN LP RP R Q n p" 
    proof - (*Generated proof - sorry...*)
      have f1: "((\<lambda>na. size_atom_form (pos_countNSNP R + pos_countNP Q + pos_count p) (length R) (length (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p))))::nat \<Rightarrow> 'a hybr_form \<Rightarrow> nat) = (\<lambda>na. size_atom_form (pos_countNP Q + (pos_countNSNP R + pos_count p)) (length R) (length (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U add n (nominalsForm p U nominalsNP Q))))"
        by (simp add: "2" add.commute add.left_commute)
      have f2: "((\<lambda>na. size_atom_form (pos_countNSNP R + (pos_count p + pos_countNP Q)) (length R) (length (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U add n (nominalsForm p U nominalsNP Q))))::nat \<Rightarrow> 'a hybr_form \<Rightarrow> nat) = (\<lambda>na. size_atom_form (pos_countNP Q + (pos_countNSNP R + pos_count p)) (length R) (length (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U add n (nominalsForm p U nominalsNP Q))))"
        by (metis (no_types) add.commute group_cancel.add2)
      have f3: "((\<lambda>ns h. Suc (size_atom_form (pos_countNSNP R + pos_countNP Q + pos_count p) (length R) (length (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p))) h))::nat list \<Rightarrow> 'a hybr_form \<Rightarrow> nat) = (\<lambda>ns h. Suc (size_atom_form (pos_countNP Q + (pos_countNSNP R + pos_count p)) (length R) (length (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U add n (nominalsForm p U nominalsNP Q))) h))"
        by (metis f1)
      have f4: "((\<lambda>ns h. Suc (size_atom_form (pos_countNSNP R + (pos_count p + pos_countNP Q)) (length R) (length (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U add n (nominalsForm p U nominalsNP Q))) h))::nat list \<Rightarrow> 'a hybr_form \<Rightarrow> nat) = (\<lambda>ns h. Suc (size_atom_form (pos_countNP Q + (pos_countNSNP R + pos_count p)) (length R) (length (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U add n (nominalsForm p U nominalsNP Q))) h))"
        by (metis (no_types) add.commute group_cancel.add2)
      have "n1_0 Q (pos_countNSNP R + pos_countNP Q + pos_count p) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p)) + (n2_0 (pos_countNSNP R + pos_countNP Q + pos_count p) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p)) + (missing R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p)) + size_atom_form (pos_countNSNP R + pos_countNP Q + pos_count p) (length R) (length (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U add n (nominalsForm p U nominalsNP Q))) p)) < Suc (n1_0 Q (pos_countNSNP R + pos_countNP Q + pos_count p) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p)) + (n2_0 (pos_countNSNP R + pos_countNP Q + pos_count p) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p)) + (missing R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U add n (nominalsForm p U nominalsNP Q)) + size_atom_form (pos_countNP Q + (pos_countNSNP R + pos_count p)) (length R) (length (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U add n (nominalsForm p U nominalsNP Q))) p)))"
        by (smt (z3) \<open>missing R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p)) = missing R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U add n (nominalsForm p U nominalsNP Q))\<close> add.commute add_diff_inverse_nat group_cancel.add2 less_add_Suc1 less_irrefl_nat)
      then have "n1_0 Q (pos_countNSNP R + pos_countNP Q + pos_count p) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p)) + (n2_0 (pos_countNSNP R + pos_countNP Q + pos_count p) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p)) + (missing R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p)) + size_atom_form (pos_countNSNP R + pos_countNP Q + pos_count p) (length R) (length (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p))) p)) < Suc (n1_0 Q (pos_countNSNP R + pos_countNP Q + pos_count p) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p)) + (n2_0 (pos_countNSNP R + pos_countNP Q + pos_count p) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p)) + (missing R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U add n (nominalsForm p U nominalsNP Q)) + size_atom_form (pos_countNP Q + (pos_countNSNP R + pos_count p)) (length R) (length (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U add n (nominalsForm p U nominalsNP Q))) p)))"
        by (metis (lifting) "2")
      then have "n1_0 Q (pos_countNSNP R + pos_countNP Q + pos_count p) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p)) + size_atom_form (pos_countNSNP R + pos_countNP Q + pos_count p) (length R) (length (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p))) p + n2_0 (pos_countNSNP R + pos_countNP Q + pos_count p) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p)) + missing R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p)) < Suc (n1_0 Q (pos_countNSNP R + (pos_count p + pos_countNP Q)) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U add n (nominalsForm p U nominalsNP Q)) + (n2_0 (pos_countNSNP R + (pos_count p + pos_countNP Q)) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U add n (nominalsForm p U nominalsNP Q)) + (missing R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U add n (nominalsForm p U nominalsNP Q)) + size_atom_form (pos_countNP Q + (pos_countNSNP R + pos_count p)) (length R) (length (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U add n (nominalsForm p U nominalsNP Q))) p)))"
        using f4 f3 f2 f1 by presburger
      then have "n1_0 Q (pos_countNSNP R + pos_countNP Q + pos_count p) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p)) + size_atom_form (pos_countNSNP R + pos_countNP Q + pos_count p) (length R) (length (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p))) p + n2_0 (pos_countNSNP R + pos_countNP Q + pos_count p) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p)) + missing R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U add n (nominalsForm p)) < Suc (n2_0 (pos_countNSNP R + (pos_count p + pos_countNP Q)) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U add n (nominalsForm p U nominalsNP Q)) + (n1_0 Q (pos_countNSNP R + (pos_count p + pos_countNP Q)) R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U add n (nominalsForm p U nominalsNP Q)) + (missing R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U add n (nominalsForm p U nominalsNP Q)) + size_atom_form (pos_countNSNP R + (pos_count p + pos_countNP Q)) (length R) (length (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R U add n (nominalsForm p U nominalsNP Q))) p)))"
        by (smt (z3) add.commute group_cancel.add2)
      then show ?thesis
        by (smt (z3) add.commute group_cancel.add2)
    qed
  qed
next
  fix LA RA :: \<open>(nat \<times> 'a) list\<close>
  fix RN :: \<open>(nat \<times> nat) list\<close>
  fix LP RP :: \<open>(nat \<times> nat) list\<close>
  fix R :: \<open>(nat \<times> nat list \<times>'a hybr_form) list\<close>
  fix Q :: \<open>(nat \<times>'a hybr_form) list\<close>
  fix n :: nat
  fix p1 p2 :: "'a hybr_form"
  let ?ns = "
    nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U 
    nominalsNSNP R U add n (nominalsForm p1 U add n (nominalsForm p2 U nominalsNP Q))"
  let ?ms = "
    nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U 
    nominalsNSNP R U add n ((nominalsForm p1 U nominalsForm p2) U nominalsNP Q)"
  let ?pn = \<open>pos_countNSNP R + (pos_count p1 + (pos_count p2 + pos_countNP Q))\<close>
  let ?pm = \<open>pos_countNSNP R + (pos_count p1 + pos_count p2 + pos_countNP Q)\<close>
  let ?lhs = \<open>\<lambda> ps ns. 
    size_atom_form ps (length R) (length ns) p1 +
    (size_atom_form ps (length R) (length ns) p2 + n1_0 Q ps R ns) +
    n2_0 ps R ns +
    missing R ns\<close>
  let ?rhs = \<open>\<lambda>ps ns.
    size_atom_form ps (length R) (length ns) p1 + size_atom_form ps (length R) (length ns) p2 +
    n1_0 Q ps R ns +
    n2_0 ps R ns +
    missing R ns\<close>
  let ?show_this = "
    (let ns = ?ns in 
    let ps = ?pn in
      ?lhs ps ns) < (
    let ns = ?ms in
    let ps = ?pm in Suc (
      ?rhs ps ns))"
  show "?show_this"
  proof-
    have isset: "is_set ?ns \<and> is_set ?ms"
      by (simp add: NA_is_set union_is_set)

    have setequal: "set_equal ?ns ?ms" 
    proof -
      have "set_equal 
        ?ns
        (add n (add n (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U 
          nominalsNN RP U nominalsNSNP R U (nominalsForm p1 U nominalsForm p2) U nominalsNP Q)))" 
        by (smt (verit, del_insts) Un_assoc Un_insert_right add_simp set_equal_iff union_simp)
      moreover have "
        set_equal ...
          (add n ((nominalsForm p1 U nominalsForm p2) U ns_1 LA RA RN LP RP R Q))" 
        by (smt (z3) List.set_insert Un_left_commute add_simp in_set_insert insertCI 
            set_equal_iff union_simp)
      moreover have \<open>set_equal 
        ...
        (add n (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U 
           nominalsNSNP R U (nominalsForm p1 U nominalsForm p2) U nominalsNP Q))\<close>
        by (smt (z3) Un_left_commute add_simp set_equal_iff union_simp)
      moreover have \<open>set_equal ... ?ms\<close> 
        by (metis Un_insert_right add_simp set_equal_iff union_simp)
      ultimately show ?thesis 
        by blast
    qed

    then have"
      missing R ?ns = missing R ?ms" 
      using isset missing_set_equal2 by blast
    moreover have"
      length ?ns = length ?ms" 
      using isset set_size_equal setequal by blast
    ultimately have "
      ?lhs ?pn ?ns < 
      Suc (?rhs ?pm ?ms)"
        by (simp add: add.commute add.left_commute)
    then show "?show_this" 
        by (smt (z3) add.commute add.left_commute)  
  qed
next
  fix LA RA :: \<open>(nat \<times> 'a) list\<close>
  fix RN :: \<open>(nat \<times> nat) list\<close>
  fix LP RP :: \<open>(nat \<times> nat) list\<close>
  fix R :: \<open>(nat \<times> nat list \<times>'a hybr_form) list\<close>
  fix Q :: \<open>(nat \<times>'a hybr_form) list\<close>
  fix n1 n2 :: nat
  fix p :: "'a hybr_form"
  let ?ns = "
    nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U 
    nominalsNSNP R U add n2 (nominalsForm p U nominalsNP Q)"
  let ?ms = "
    nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U 
    nominalsNSNP R U add n1 (add n2 (nominalsForm p) U nominalsNP Q)"
  let ?pn = \<open>pos_countNSNP R + (pos_count p + pos_countNP Q)\<close>
  let ?pm = \<open>pos_countNSNP R + (pos_count p + pos_countNP Q)\<close>
  let ?lhs = \<open>\<lambda> ps ns. 
    size_atom_form ps (length R) (length ns) p + n1_0 Q ps R ns + n2_0 ps R ns + missing R ns\<close>
  let ?rhs = \<open>\<lambda>ps ns.
    size_atom_form ps (length R) (length ns) p + n1_0 Q ps R ns + n2_0 ps R ns + missing R ns\<close>
  let ?show_this = "
    (let ns = ?ns in 
    let ps = ?pn in
      ?lhs ps ns) < (
    let ns = ?ms in
    let ps = ?pm in Suc (
      ?rhs ps ns))"
  show "?show_this"
  proof-
    have isset: "is_set ?ns \<and> is_set ?ms"
      by (simp add: NA_is_set union_is_set)

    have subset: "sub_set ?ns ?ms" 
      by (smt (z3) member.simps(2) add_def member_sub_set union_member)

    then have 1:"
      missing R ?ns \<le> missing R ?ms"
      using isset missing_sub_set2 by blast
    moreover have 2:"
      length ?ns \<le> length ?ms"  
      using isset sub_set_size subset by auto
    moreover have "
      size_atom_form ?pn (length R) (length ?ns) p \<le> size_atom_form ?pm (length R) (length ?ms) p" 
      by (simp add: "2" size_atom_form_size_ns)
    moreover have "
      n1_0 Q ?pn R ?ns \<le> n1_0 Q ?pm R ?ms" 
      using "2" n1_0_ps_less by blast
    moreover have "
      n2_0 ?pn R ?ns \<le> n2_0 ?pm R ?ms" 
      using "2" n2_0_ps_less by blast
    ultimately have "
      ?lhs ?pn ?ns < 
      Suc (?rhs ?pm ?ms)" 
      by (meson le_imp_less_Suc lesser_add)
    then show "?show_this" 
        by (smt (z3) add.commute add.left_commute)  
  qed
next
  fix LA RA :: \<open>(nat \<times> 'a) list\<close>
  fix RN :: \<open>(nat \<times> nat) list\<close>
  fix LP RP :: \<open>(nat \<times> nat) list\<close>
  fix R :: \<open>(nat \<times> nat list \<times>'a hybr_form) list\<close>
  fix Q :: \<open>(nat \<times>'a hybr_form) list\<close>
  fix n :: nat
  fix p :: "'a hybr_form"
  let ?fresh = \<open>
    fresh (
      nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U 
      nominalsNSNP R U add n (nominalsForm p U nominalsNP Q))\<close>
  let ?ns = "
    nominalsNA LA U nominalsNA RA U nominalsNN RN U
    add n (add (?fresh) (nominalsNN LP)) U
    nominalsNN RP U nominalsNSNP R U
    add (?fresh) (nominalsForm p U nominalsNP Q)"
  let ?ms = "
    nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U 
    nominalsNSNP R U add n (nominalsForm p U nominalsNP Q)"
  let ?pn = \<open>pos_countNSNP R + (pos_count p + pos_countNP Q)\<close>
  let ?pm = \<open>pos_countNSNP R + (pos_count p + pos_countNP Q)\<close>
  let ?lhs = \<open>\<lambda> ps ns. 
    size_atom_form ps (length R) (length ns) p + n1_0 Q ps R ns + n2_0 ps R ns + missing R ns\<close>
  let ?rhs = \<open>\<lambda> ns.
    Suc (Suc (?pm + length R + length ns + 
      size_atom_form (Suc (?pm)) (length R) (length ns) p +
      n1_0 Q (Suc (?pm)) R ns +
      n2_0 (Suc (?pm)) R ns +
      missing R ns))\<close>
  let ?show_this = "
    (let ns = ?ns in 
    let ps = ?pn in
      ?lhs ps ns) < (
    let ns = ?ms in Suc (
      ?rhs ns))"
  show "?show_this"
  proof-
    have isset: "is_set ?ns \<and> is_set ?ms \<and> is_set (add ?fresh ?ms)" 
      by (simp add: NA_is_set add_is_set union_is_set)

    have setequal: "set_equal ?ns (add ?fresh ?ms)" 
    proof-
      have \<open>set_equal ?ns (
        nominalsNA LA U nominalsNA RA U nominalsNN RN U
        add n (add (?fresh) (nominalsNN LP) U
        nominalsNN RP U nominalsNSNP R U
        add (?fresh) (nominalsForm p U nominalsNP Q)))\<close> 
        by (metis set_equal_commutative union_with_equal unionadd1)
      moreover have \<open>set_equal ... (
        add n (nominalsNA LA U nominalsNA RA U nominalsNN RN U
        add (?fresh) (nominalsNN LP) U
        nominalsNN RP U nominalsNSNP R U
        add (?fresh) (nominalsForm p U nominalsNP Q)))\<close>
        by (metis Un_insert_right add_simp set_equal_iff union_simp)
      moreover have \<open>set_equal ...  (
        add n (add (?fresh) (nominalsNA LA U nominalsNA RA U nominalsNN RN U
        nominalsNN LP U
        nominalsNN RP U nominalsNSNP R U
        add (?fresh) (nominalsForm p U nominalsNP Q))))\<close>
        by (smt (verit, del_insts) Un_assoc Un_insert_right add_simp insert_is_Un set_equal_iff
            union_simp)
      moreover have \<open>set_equal ... (
        add n (add ?fresh (nominalsNA LA U nominalsNA RA U nominalsNN RN U
        nominalsNN LP U
        nominalsNN RP U nominalsNSNP R U
        nominalsForm p U nominalsNP Q)))\<close>
        by (smt (z3) Un_insert_right add_def add_simp insertCI member_iff set_equal_iff union_simp)
      moreover have \<open>set_equal ... (
        add ?fresh (add n (nominalsNA LA U nominalsNA RA U nominalsNN RN U
        nominalsNN LP U
        nominalsNN RP U nominalsNSNP R U
        nominalsForm p U nominalsNP Q)))\<close>
        by (metis union.simps(1) union.simps(2) unionadd1)
      moreover have \<open>set_equal ... (add ?fresh ?ms)\<close> 
        by (metis Un_insert_right add_simp set_equal_iff union_simp)
      ultimately show ?thesis by blast
    qed

    then have \<open>missing R ?ns = missing R (add ?fresh ?ms)\<close> 
      by (simp add: missing_set_equal2 isset)
    moreover have "... \<le> missing R ?ms + (length R)"
      by (simp add: missing_add_length)
    ultimately have 1: "
      missing R ?ns \<le> missing R ?ms + (length R)"
      by simp
    have "
      length ?ns = length (add ?fresh ?ms)"  
      using isset set_size_equal setequal by auto
    moreover have"
      ... \<le> length ?ms + 1"
      using add_size by simp
    ultimately have 2:\<open>length ?ns \<le> length ?ms + 1\<close> by simp
    then have 3: \<open>?pn + length ?ns \<le> ?pm + (length ?ms + 1)\<close>
        using 2 by simp
    then have 4:\<open>?pn + (length R) + (length ?ns) \<le> (?pm + 1) + (length R) + length ?ms\<close> 
      by simp
    then have 5:"
      size_atom_form ?pn (length R) (length ?ns) p \<le> 
      size_atom_form (Suc (?pm)) (length R) (length ?ms) p" 
      by (simp add: size_atom_suc_dec2)
    have 6:"
      n1_0 Q ?pn R ?ns \<le> n1_0 Q (Suc (?pm)) R ?ms"  
    proof-
      have \<open>?pn + length ?ns \<le> (Suc (?pm)) + length ?ms\<close> 
        using 3 by simp
      then show ?thesis 
        using n1_0_suc_dec2 by (metis add_le_cancel_right)
    qed
    have 7:"
      n2_0 ?pn R ?ns \<le> n2_0 (Suc (?pm)) R ?ms" 
    proof-
      have \<open>?pn + length ?ns \<le> (Suc (?pm)) + length ?ms\<close>
        using 3 by simp
      then show ?thesis
        using n2_0_suc_dec2 by metis
    qed
    have "
      size_atom_form ?pn (length R) (length ?ns) p + 
      n1_0 Q ?pn R ?ns + n2_0 ?pn R ?ns + missing R ?ns \<le> 
      size_atom_form (Suc (?pm)) (length R) (length ?ms) p +
      n1_0 Q (Suc (?pm)) R ?ms + n2_0 (Suc (?pm)) R ?ms +
      missing R ?ms + (length R)" 
    proof-
      have \<open>
        size_atom_form ?pn (length R) (length ?ns) p + n1_0 Q ?pn R ?ns \<le>
        size_atom_form (Suc (?pm)) (length R) (length ?ms) p + n1_0 Q (Suc (?pm)) R ?ms\<close>
        using 5 6 by simp
      then show ?thesis 
        using 1 7 by simp
    qed
    then have \<open>
      size_atom_form ?pn (length R) (length ?ns) p + 
      n1_0 Q ?pn R ?ns + n2_0 ?pn R ?ns + missing R ?ns \<le> 
      ?pm + length R + length ?ms + 
      size_atom_form (Suc (?pm)) (length R) (length ?ms) p +
      n1_0 Q (Suc (?pm)) R ?ms +
      n2_0 (Suc (?pm)) R ?ms +
      missing R ?ms\<close> 
      by simp
    then show "?show_this"
      by (meson less_Suc_eq less_or_eq_imp_le not_less_eq not_less_eq_eq) 
  qed
next
  fix LA RA :: \<open>(nat \<times> 'a) list\<close>
  fix RN :: \<open>(nat \<times> nat) list\<close>
  fix LP RP :: \<open>(nat \<times> nat) list\<close>
  fix R Rrem :: \<open>(nat \<times> nat list \<times>'a hybr_form) list\<close>
  fix n m :: nat
  fix x2 y ya p yb yc
  let ?ns = \<open>
    nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U 
      add n (add m (nominalsNN RP)) U nominalsNSNP Rrem\<close>
  let ?ms = \<open>
    nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R\<close>
  assume a1:\<open>
    saturate R ?ms =
    Some x2\<close>
  assume \<open>(n, y) = x2\<close>
  moreover assume \<open>(m, ya) = y\<close>
  moreover assume \<open>(p, yb) = ya\<close>
  moreover assume \<open>(Rrem, yc) = yb\<close>
  ultimately have a2:\<open>x2 = (n,m,p,Rrem,yc)\<close> 
    by simp

  have \<open>\<exists>R1 R2 ms. [] @ R = R1 @ [(n,ms,p)] @ R2 \<and> Rrem = R1 @ R2\<close>
    using saturate_split a1 a2 by metis
  then obtain R1 R2 ms where Rdef:"R = R1 @ [(n,ms,p)] @ R2 \<and> Rrem = R1 @ R2" 
    by auto
  obtain R3 where R3def: \<open>R3 = R1 @ [(n,ms,p)]\<close> by simp

  have isset:\<open>is_set ?ns \<and> is_set ?ms\<close> 
    by (simp add: NA_is_set union_is_set)

  have subset:\<open>sub_set ?ns ?ms\<close>
  proof-
    have \<open>member n (nominalsNSNP R)\<close> 
      using a1 a2 saturate_nom_members by blast
    moreover have \<open>sub_set (nominalsNSNP Rrem) (nominalsNSNP R)\<close> 
    proof-
      have \<open>set_equal (nominalsNSNP Rrem) (nominalsNSNP R1 U nominalsNSNP R2)\<close> 
        using Rdef  nominals_con by blast
      moreover have \<open>
        set_equal (nominalsNSNP R) (nominalsNSNP R1 U nominalsNSNP [(n,ms,p)] U nominalsNSNP R2)\<close>
      proof-
        have \<open>set_equal (nominalsNSNP R3) (nominalsNSNP R1 U nominalsNSNP [(n,ms,p)])\<close>
          using R3def nominals_con by blast
        moreover have \<open>set_equal (nominalsNSNP R) (nominalsNSNP R3 U nominalsNSNP R2)\<close> 
          by (metis R3def Rdef append.assoc nominals_con)
        ultimately show ?thesis 
          by (metis (no_types, hide_lams) Rdef nominals_con set_equal_associative union_with_equal)
      qed
      moreover have \<open>sub_set (nominalsNSNP R1 U nominalsNSNP R2) ...\<close> 
        by (meson member_sub_set union_member)
      ultimately show ?thesis 
        by blast
    qed
    ultimately have 1:\<open>sub_set (add n (nominalsNSNP Rrem)) (nominalsNSNP R)\<close> 
      by (metis add_def remove.simps(2) sub_set_def)
    have 2:\<open>
      set_equal ?ns (add m (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U 
        nominalsNN RP U (add n (nominalsNSNP Rrem))))\<close> 
      by (smt (verit, best) set_equal_associative set_equal_commutative 
          union_with_equal unionadd1 unionadd2)

    have \<open>member m ?ms\<close> 
      using a1 a2 saturate_nom_members by blast
    moreover have \<open>
      sub_set (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U 
        nominalsNN RP U (add n (nominalsNSNP Rrem))) ?ms\<close>
      by (smt (z3) "1" member_sub_set union_member)
    ultimately have \<open>
      sub_set (add m (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U 
        nominalsNN RP U (add n (nominalsNSNP Rrem)))) ?ms\<close>
      by (metis add_def sub_set_union sub_set_union2 union.simps(1) union.simps(2))
    then show ?thesis 
      using 1 2 
      by blast
  qed
  moreover have \<open>missing Rrem ?ns = missing R1 ?ns + missing R2 ?ns\<close>
    by (simp add: Rdef miss_plus)
  moreover have \<open>missing R ?ms = missing R1 ?ms + missing [(n,ms,p)] ?ms + missing R2 ?ms\<close> 
    by (simp add: Rdef miss_plus)
  moreover have \<open>missing R1 ?ns \<le> missing R1 ?ms\<close> 
    by (meson NA_is_set calculation(1) missing_sub_set2 union_is_set)
  moreover have \<open>missing R2 ?ns \<le> missing R2 ?ms\<close>
    by (meson NA_is_set calculation(1) missing_sub_set2 union_is_set)
  ultimately have 1:\<open>missing Rrem ?ns \<le> missing R ?ms\<close>
    by linarith

  have q:\<open>pos_countNSNP Rrem \<le> pos_countNSNP R\<close>
  proof-
    have "pos_countNSNP Rrem = pos_countNSNP R1 + pos_countNSNP R2" 
      by (simp add: Rdef pos_count_con)
    moreover have \<open>pos_countNSNP R = pos_countNSNP R1 + pos_countNSNP [(n,ms,p)] + pos_countNSNP R2\<close>
      by (simp add: Rdef pos_count_con)
    ultimately show ?thesis 
      by simp
  qed
  have w:\<open>length Rrem < length R\<close> 
  proof-
    have \<open>length (R1 @ R2) < length (R1 @ [(n,ms,p)] @ R2)\<close> 
      by simp
    then show ?thesis
      by (simp add: Rdef)
  qed
  have e:\<open>length ?ns \<le> length ?ms\<close> 
    using isset sub_set_size subset by auto

  have 2: \<open>n2_0 (pos_countNSNP Rrem) Rrem ?ns < n2_0 (pos_countNSNP R) R ?ms\<close> 
  proof-
    let ?n2 = \<open>\<lambda> R ps Rl ns. 
      (\<Sum>(u, u', p)\<leftarrow>R. Suc (size_atom_form ps Rl ns p))\<close>
    have \<open>n2_0 (pos_countNSNP Rrem) Rrem ?ns = 
      ?n2 R1 (pos_countNSNP Rrem) (length Rrem) (length ?ns) + 
        ?n2 R2 (pos_countNSNP Rrem) (length Rrem) (length ?ns)\<close> 
      by (simp add: Rdef)
    moreover have \<open>n2_0 (pos_countNSNP R) R ?ms = 
      ?n2 R1 (pos_countNSNP R) (length R) (length ?ms) +
        ?n2 [(n,ms,p)] (pos_countNSNP R) (length R) (length ?ms) + 
          ?n2 R2 (pos_countNSNP R) (length R) (length ?ms)\<close>
      by (simp add: Rdef)
    moreover have \<open>
      ?n2 R1 (pos_countNSNP Rrem) (length Rrem) (length ?ns) \<le>
      ?n2 R1 (pos_countNSNP R) (length R) (length ?ms)\<close> 
      using q w e by (simp add: n2_0_lesser less_or_eq_imp_le)
    moreover have \<open>
      ?n2 R2 (pos_countNSNP Rrem) (length Rrem) (length ?ns) \<le>
      ?n2 R2 (pos_countNSNP R) (length R) (length ?ms)\<close>
      using q w e by (simp add: n2_0_lesser less_or_eq_imp_le)
    moreover have \<open>1 \<le> ?n2 [(n,ms,p)] (pos_countNSNP R) (length R) (length ?ms)\<close> 
    proof-
      have \<open>
        ?n2 [(n,ms,p)] (pos_countNSNP R) (length R) (length ?ms) =
        Suc (size_atom_form (pos_countNSNP R) (length R) (length ?ms) p)\<close> 
        by simp
      moreover have \<open>size_atom_form (pos_countNSNP R) (length R) (length ?ms) p \<ge> 0\<close> 
        by simp
      ultimately show ?thesis 
        by fastforce
    qed
    ultimately show ?thesis 
      by linarith
  qed

  then show \<open>
    (let ns = ?ns in 
      n2_0 (pos_countNSNP Rrem) Rrem ns + missing Rrem ns) < 
    (let ns = ?ms in 
      n2_0 (pos_countNSNP R) R ns + missing R ns)\<close> 
    using 1 2 by (metis add_less_le_mono)
next
  fix LA RA :: \<open>(nat \<times> 'a) list\<close>
  fix RN :: \<open>(nat \<times> nat) list\<close>
  fix LP RP :: \<open>(nat \<times> nat) list\<close>
  fix R Rrem :: \<open>(nat \<times> nat list \<times>'a hybr_form) list\<close>
  fix n m :: nat
  fix p :: \<open>'a hybr_form\<close>
  fix x2 y ya yb yc 
  let ?ns = \<open>
    nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U 
      nominalsNN RP U nominalsNSNP Rrem U [] U add m (nominalsForm p)\<close>
  let ?ms = \<open>
    nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R\<close>
  let ?ps = \<open>pos_countNSNP Rrem + pos_count p\<close>
  assume a1:\<open>
    saturate R ?ms =
    Some x2\<close>
  assume \<open>(n, y) = x2\<close>
  moreover assume \<open>(m, ya) = y\<close>
  moreover assume \<open>(p, yb) = ya\<close>
  moreover assume \<open>(Rrem, yc) = yb\<close>
  ultimately have a2:\<open>x2 = (n,m,p,Rrem,yc)\<close> 
    by simp


  have \<open>\<exists>R1 R2 ms. [] @ R = R1 @ [(n,ms,p)] @ R2 \<and> Rrem = R1 @ R2\<close>
    using saturate_split a1 a2 by metis
  then obtain R1 R2 ms where Rdef:"R = R1 @ [(n,ms,p)] @ R2 \<and> Rrem = R1 @ R2" 
    by auto
  obtain R3 where R3def: \<open>R3 = R1 @ [(n,ms,p)]\<close> by simp

  have isset:\<open>is_set ?ns \<and> is_set ?ms\<close> 
    by (simp add: NA_is_set union_is_set)

  have subset:\<open>sub_set ?ns ?ms\<close>
  proof-
    have 1:\<open>member m ?ms\<close> 
      using a1 a2 saturate_nom_members by blast

    have 2:\<open>
        set_equal (nominalsNSNP R) (nominalsNSNP R1 U nominalsNSNP [(n,ms,p)] U nominalsNSNP R2)\<close>
    proof-
      have \<open>set_equal (nominalsNSNP R3) (nominalsNSNP R1 U nominalsNSNP [(n,ms,p)])\<close>
        using R3def nominals_con by blast
      moreover have \<open>set_equal (nominalsNSNP R) (nominalsNSNP R3 U nominalsNSNP R2)\<close> 
        by (metis R3def Rdef append.assoc nominals_con)
      ultimately show ?thesis 
        by (metis (no_types, hide_lams) Rdef nominals_con set_equal_associative union_with_equal)
    qed

    have \<open>sub_set (nominalsNSNP Rrem) (nominalsNSNP R)\<close> 
    proof-
      have \<open>set_equal (nominalsNSNP Rrem) (nominalsNSNP R1 U nominalsNSNP R2)\<close> 
        using Rdef  nominals_con by blast
      moreover have \<open>sub_set (nominalsNSNP R1 U nominalsNSNP R2) 
        (nominalsNSNP R1 U nominalsNSNP [(n,ms,p)] U nominalsNSNP R2)\<close> 
        by (meson member_sub_set union_member)
      ultimately show ?thesis 
        using "2" by blast
    qed
    moreover have \<open>sub_set (nominalsForm p) (nominalsNSNP R)\<close>
    proof-
      have \<open>nominalsNSNP [(n,ms,p)] = nominalsNSNP [] U add n (ms U nominalsForm p)\<close> by simp
      then have \<open>sub_set (nominalsForm p) (nominalsNSNP [(n,ms,p)])\<close>
        by (smt (z3) ListSet.member.simps(2) add_def member_sub_set sub_set_union2)
      then have \<open>sub_set (nominalsForm p) 
        (nominalsNSNP R1 U nominalsNSNP [(n,ms,p)] U nominalsNSNP R2)\<close>
        by (meson member_sub_set union_member)
      then show ?thesis 
        using 2 by simp
    qed
    ultimately have 3:\<open>sub_set (nominalsNSNP Rrem U nominalsForm p) (nominalsNSNP R)\<close>
      by (meson sub_set_union)

    have \<open>set_equal ?ns (add m (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U 
      nominalsNN RP U nominalsNSNP Rrem U [] U nominalsForm p))\<close> 
      by (smt (verit, best) set_equal_associative set_equal_commutative 
          union_with_equal unionadd1 unionadd2)
    moreover have \<open>set_equal ... 
      (add m (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U 
        nominalsNN RP U (nominalsNSNP Rrem U nominalsForm p)))\<close> 
      by (meson equal_add union_with_equal unionaddnt)
    ultimately have 4:"set_equal ?ns ..."
      by simp
    have \<open>sub_set 
      (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U 
        nominalsNN RP U (nominalsNSNP Rrem U nominalsForm p))
      ?ms\<close> 
      by (smt (z3) 3 ListSet.member.simps(2) add_def member_sub_set sub_set_union sub_set_union1 
          sub_set_union2 union.simps(1) union.simps(2) union_member)
    then have \<open>sub_set (add m (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U 
        nominalsNN RP U (nominalsNSNP Rrem U nominalsForm p))) ?ms\<close> 
      by (metis (no_types, lifting) "1" add_def remove.simps(2) sub_set_def)
    then show ?thesis 
      using 4 by blast
  qed
  moreover have \<open>missing Rrem ?ns = missing R1 ?ns + missing R2 ?ns\<close>
    by (simp add: Rdef miss_plus)
  moreover have \<open>missing R ?ms = missing R1 ?ms + missing [(n,ms,p)] ?ms + missing R2 ?ms\<close> 
    by (simp add: Rdef miss_plus)
  moreover have \<open>missing R1 ?ns \<le> missing R1 ?ms\<close> 
    by (meson NA_is_set calculation(1) missing_sub_set2 union_is_set)
  moreover have \<open>missing R2 ?ns \<le> missing R2 ?ms\<close>
    by (meson NA_is_set calculation(1) missing_sub_set2 union_is_set)
  ultimately have miss:\<open>missing Rrem ?ns \<le> missing R ?ms\<close>
    by linarith

  have pos: \<open>pos_countNSNP Rrem + pos_count p \<le> pos_countNSNP R\<close>
    by (simp add: Rdef pos_count_con)

  have len: \<open>length ?ns \<le> length ?ms\<close>
    using isset sub_set_size subset by auto

  have rlen: \<open>length Rrem < length R\<close> 
  proof-
    have "length (R1 @ R2) < length (R1 @ [(n,ms,p)] @ R2)" 
      by simp
    then show ?thesis 
      by (simp add: Rdef)
  qed

  have n2: \<open>
    size_atom_form ?ps (length Rrem) (length ?ns) p + n2_0 ?ps Rrem ?ns <
    n2_0 (pos_countNSNP R) R ?ms\<close>
  proof-
    let ?n2 = \<open>\<lambda> R ps Rl ns. (\<Sum>(u, u', p)\<leftarrow>R. Suc (size_atom_form ps Rl ns p))\<close>
    have \<open>
      n2_0 ?ps Rrem ?ns = 
      ?n2 R1 ?ps (length Rrem) (length ?ns) +
        ?n2 R2 ?ps (length Rrem) (length ?ns)\<close> 
      by (simp add: Rdef)
    then have \<open>
      size_atom_form ?ps (length Rrem) (length ?ns) p + n2_0 ?ps Rrem ?ns =
      size_atom_form ?ps (length Rrem) (length ?ns) p +
        ?n2 R1 ?ps (length Rrem) (length ?ns) +
          ?n2 R2 ?ps (length Rrem) (length ?ns)\<close>
      by simp
    moreover have \<open>
      n2_0 (pos_countNSNP R) R ?ms = 
      ?n2 R1 (pos_countNSNP R) (length R) (length ?ms) +
        ?n2 [(n,ms,p)] (pos_countNSNP R) (length R) (length ?ms) +
          ?n2 R2 (pos_countNSNP R) (length R) (length ?ms)\<close> 
      by (simp add: Rdef)
    moreover have \<open>
      ?n2 R1 ?ps (length Rrem) (length ?ns) \<le>
      ?n2 R1 (pos_countNSNP R) (length R) (length ?ms)\<close> 
      using pos len rlen by (simp add: n2_0_lesser less_or_eq_imp_le)
    moreover have \<open>
      ?n2 R2 ?ps (length Rrem) (length ?ns) \<le>
      ?n2 R2 (pos_countNSNP R) (length R) (length ?ms)\<close>
      using pos len rlen by (simp add: n2_0_lesser less_or_eq_imp_le)
    moreover have \<open>
      ?n2 [(n,ms,p)] (pos_countNSNP R) (length R) (length ?ms) = 
      Suc (size_atom_form (pos_countNSNP R) (length R) (length ?ms) p)\<close> by simp
    moreover have \<open>... > size_atom_form ?ps (length Rrem) (length ?ns) p\<close> 
    proof-
      have "
        size_atom_form ?ps (length Rrem) (length ?ns) p \<le>
        size_atom_form (pos_countNSNP R) (length R) (length ?ms) p" 
        using pos len rlen 
        by (simp add: dual_order.strict_implies_order lesser_add size_atom_suc_dec2)
      then show ?thesis 
        by simp
    qed
    ultimately show ?thesis 
      by simp
  qed
  show \<open>
    (let ns = ?ns ;
         ps = ?ps in 
      size_atom_form ps (length Rrem) (length ns) p + n2_0 ps Rrem ns + missing Rrem ns) < 
    (let ns = ?ms in 
      n2_0 (pos_countNSNP R) R ns + missing R ns)\<close> 
    using n2 miss by (metis add_less_le_mono)
next
  fix LA RA :: \<open>(nat \<times> 'a) list\<close>
  fix RN :: \<open>(nat \<times> nat) list\<close>
  fix LP RP :: \<open>(nat \<times> nat) list\<close>
  fix R Rsat :: \<open>(nat \<times> nat list \<times>'a hybr_form) list\<close>
  fix n m :: nat
  fix p :: \<open>'a hybr_form\<close>
  fix x2 y ya yb xc 
  let ?ns = \<open>
    nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U 
      nominalsNN RP U nominalsNSNP Rsat\<close>
  let ?ms = \<open>
    nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U nominalsNSNP R\<close>
  assume a1:\<open>
    saturate R ?ms =
    Some x2\<close>
  assume \<open>(n, y) = x2\<close>
  moreover assume \<open>(m, ya) = y\<close>
  moreover assume \<open>(p, yb) = ya\<close>
  moreover assume \<open>(xc, Rsat) = yb\<close>
  ultimately have a2:\<open>saturate R ?ms = Some (n,m,p,xc,Rsat)\<close> 
    by (simp add: a1)

  have \<open>(\<exists> R1 R2 ms ms'. Rsat = R1 @ [(n,m # ms,p)] @ R2 \<and> [] @ R = R1 @ [(n,ms,p)] @ R2 \<and> 
      remove ?ms ms = m # ms')\<close>
    using saturate_split2 a2 by metis
  then obtain R1 R2 ms ms' where Rdef:\<open>Rsat = R1 @ [(n,m # ms,p)] @ R2 \<and> R = R1 @ [(n,ms,p)] @ R2\<and> 
      remove ?ms ms = m # ms'\<close>
    by auto

  have isset: \<open>is_set ?ns \<and> is_set ?ms\<close>
    by (simp add: NA_is_set union_is_set)

  have \<open>set_equal (nominalsNSNP Rsat) (add m (nominalsNSNP R))\<close>
  proof-
    obtain R3 where R3def:\<open>R3 = R1 @ [(n,m # ms,p)]\<close> by simp
    obtain R4 where R4def:\<open>R4 = R1 @ [(n,ms,p)]\<close> by simp
    have \<open>set_equal (nominalsNSNP R3) (nominalsNSNP R1 U nominalsNSNP [(n,m # ms,p)])\<close>
      by (metis R3def nominals_con)
    moreover have "
      set_equal (nominalsNSNP Rsat) 
        (nominalsNSNP R3 U nominalsNSNP R2)" 
      by (metis Rdef R3def append.assoc nominals_con)
    ultimately have 1:\<open>
      set_equal (nominalsNSNP Rsat) 
        (nominalsNSNP R1 U nominalsNSNP [(n,m # ms,p)] U nominalsNSNP R2)\<close> 
      by (metis (no_types, hide_lams) Rdef nominals_con set_equal_associative union_with_equal)
    
    have \<open>set_equal (nominalsNSNP R4) (nominalsNSNP R1 U nominalsNSNP [(n,ms,p)])\<close>
      by (metis R4def nominals_con)
    moreover have "
      set_equal (nominalsNSNP R) 
        (nominalsNSNP R4 U nominalsNSNP R2)" 
      by (metis Rdef R4def append.assoc nominals_con)
    ultimately have 2:\<open>
      set_equal (nominalsNSNP R) 
        (nominalsNSNP R1 U nominalsNSNP [(n,ms,p)] U nominalsNSNP R2)\<close> 
      by (metis (no_types, hide_lams) Rdef nominals_con set_equal_associative union_with_equal)

    have 3:\<open>set_equal (nominalsNSNP [(n,m # ms,p)]) (m # (nominalsNSNP [(n,ms,p)]))\<close>
    proof-
      have \<open>set_equal (nominalsNSNP [(n,m # ms,p)]) (add n ((m # ms) U nominalsForm p))\<close>
        using unionaddnt by force
      moreover have \<open>set_equal ... (add n (m # (ms U nominalsForm p)))\<close> 
        by (metis equal_add set_equal_append_add set_equal_associative set_equal_commutative 
            union.simps(2) union_commutative unionadd2)
      moreover have \<open>set_equal ... (m # (add n (ms U nominalsForm p)))\<close> 
        by (meson set_equal_add_con)
      moreover have \<open>set_equal ... (m # (nominalsNSNP [(n,ms,p)]))\<close> 
        by (metis nominalsNSNP.simps(1) nominalsNSNP.simps(2) set_equal_append_add 
            set_equal_associative set_equal_commutative unionadd2 unionaddnt)
      ultimately show ?thesis 
        by (meson set_equal_associative)
    qed
    then have \<open>set_equal (nominalsNSNP [(n,m # ms,p)] U nominalsNSNP R2)
        ((m # nominalsNSNP [(n,ms,p)]) U nominalsNSNP R2)\<close> 
      by (meson union_with_equal2)
    moreover have \<open>set_equal ... (add m (nominalsNSNP [(n,ms,p)] U nominalsNSNP R2))\<close> 
      by (meson set_equal_append_add set_equal_associative set_equal_commutative 
          union_with_equal2 unionadd1)
    ultimately have \<open>
      set_equal (nominalsNSNP [(n,m # ms,p)] U nominalsNSNP R2)
        (add m (nominalsNSNP [(n,ms,p)] U nominalsNSNP R2))\<close> 
      by simp
    then have \<open>
      set_equal (nominalsNSNP R1 U nominalsNSNP [(n,m # ms,p)] U nominalsNSNP R2)
        (nominalsNSNP R1 U (add m (nominalsNSNP [(n,ms,p)] U nominalsNSNP R2)))\<close>
      by (meson union_with_equal)
    then have \<open>
      set_equal (nominalsNSNP R1 U nominalsNSNP [(n,m # ms,p)] U nominalsNSNP R2)
        (add m (nominalsNSNP R1 U nominalsNSNP [(n,ms,p)] U nominalsNSNP R2))\<close> 
      by (meson set_equal_associative set_equal_commutative unionadd2)
    then show ?thesis
      using 1 2  
      by (meson equal_add set_equal_associative set_equal_commutative)
  qed
  then have \<open>set_equal ?ns (
    nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U 
      nominalsNN RP U (add m (nominalsNSNP R)))\<close> 
    by (meson double_union_equal set_equal_reflexive)
  moreover have \<open>set_equal ... (
    nominalsNA LA U nominalsNA RA U nominalsNN RN U add m (nominalsNN LP U 
      nominalsNN RP U nominalsNSNP R))\<close> 
    by (meson set_equal_associative set_equal_commutative union_with_equal unionadd2)
  moreover have \<open>set_equal ... (add m ?ms)\<close> 
    by (meson set_equal_associative set_equal_commutative union_with_equal unionadd2)
  ultimately have \<open>set_equal ?ns (add m ?ms)\<close> by simp
  moreover have \<open>member m ?ms\<close> 
    by (meson a2 saturate_nom_members) 
  then have subset: \<open>sub_set ?ns ?ms\<close> 
    by (metis add_def calculation set_equal_def sub_set_def)

  have \<open>missing Rsat ?ns \<le> missing Rsat ?ms\<close> 
    by (meson isset missing_sub_set2 subset)
  moreover have \<open>missing Rsat ?ms < missing ([] @ R) ?ms\<close>
    using saturate_size2 a2 by metis
  ultimately have miss:\<open>missing Rsat ?ns < missing R ?ms\<close>
    by fastforce

  have pos: \<open>pos_countNSNP Rsat \<le> pos_countNSNP R\<close>
    by (simp add: Rdef pos_count_con)

  have Rlen: \<open>length Rsat \<le> length R\<close> 
    using Rdef by simp

  have len: \<open>length ?ns \<le> length ?ms\<close>
    using isset subset sub_set_size by auto

  have n2:\<open>n2_0 (pos_countNSNP Rsat) Rsat ?ns \<le> n2_0 (pos_countNSNP R) R ?ms\<close>
  proof-
    let ?n2 = \<open>\<lambda> R ps Rl ns. (\<Sum>(u, u', p)\<leftarrow>R. Suc (size_atom_form ps Rl ns p))\<close>
    have \<open>
      n2_0 (pos_countNSNP Rsat) Rsat ?ns = 
      ?n2 R1 (pos_countNSNP Rsat) (length Rsat) (length ?ns) +
        ?n2 [(n,m # ms,p)] (pos_countNSNP Rsat) (length Rsat) (length ?ns) +
          ?n2 R2 (pos_countNSNP Rsat) (length Rsat) (length ?ns)\<close> 
      by (simp add: Rdef)
    moreover have \<open>
      n2_0 (pos_countNSNP R) R ?ms = 
      ?n2 R1 (pos_countNSNP R) (length R) (length ?ms) +
        ?n2 [(n,ms,p)] (pos_countNSNP R) (length R) (length ?ms) +
          ?n2 R2 (pos_countNSNP R) (length R) (length ?ms)\<close> 
      by (simp add: Rdef)
    moreover have \<open>
      ?n2 R1 (pos_countNSNP Rsat) (length Rsat) (length ?ns) \<le>
      ?n2 R1 (pos_countNSNP R) (length R) (length ?ms)\<close> 
      by (simp add: Rlen len n2_0_lesser pos)
    moreover have \<open>
      ?n2 R2 (pos_countNSNP Rsat) (length Rsat) (length ?ns) \<le>
      ?n2 R2 (pos_countNSNP R) (length R) (length ?ms)\<close>
      by (simp add: Rlen len n2_0_lesser pos)
    moreover have \<open>
      ?n2 [(n,m # ms,p)] (pos_countNSNP Rsat) (length Rsat) (length ?ns) \<le>
      ?n2 [(n,ms,p)] (pos_countNSNP R) (length R) (length ?ms)\<close> (is \<open>?L \<le> ?R\<close>)
    proof-
      have \<open>?L = Suc (size_atom_form (pos_countNSNP Rsat) (length Rsat) (length ?ns) p)\<close> by simp
      moreover have \<open>... \<le> Suc (size_atom_form (pos_countNSNP R) (length R) (length ?ms) p)\<close> 
        using len Rlen pos  
        by (simp add: dual_order.strict_implies_order lesser_add size_atom_suc_dec2)
      moreover have \<open>... = ?R\<close> by simp
      ultimately show ?thesis 
        by linarith
    qed
    ultimately show ?thesis 
      using lesser_add by presburger
  qed

  show \<open>
    (let ns = ?ns in
      n2_0 (pos_countNSNP Rsat) Rsat ns + missing Rsat ns) < 
    (let ns = ?ms in 
      n2_0 (pos_countNSNP R) R ns + missing R ns)\<close> 
    using n2 miss by (metis add_mono_thms_linordered_field(4))
qed 
end

hide_fact pos_count_con

(*tautology definition*)
definition prover where 
  \<open>prover p \<equiv> atomize [] [] [] [] [] [] [] [(fresh (nominalsForm p),p)]\<close>

(*abbreviations*)
abbreviation Imp (infixr "THEN"  180)
  where "Imp p q \<equiv> Neg (Con p (Neg q))" 

abbreviation Iff (infixr "IFF" 180)
  where "Iff p q \<equiv> Con (Imp p q) (Imp q p)"

abbreviation Dis (infixl "OR"  200)
  where "Dis p q \<equiv> Neg (Con (Neg p) (Neg q))" 

abbreviation Nes (\<open>\<box> _\<close> 800)
  where "Nes p \<equiv> Neg (Pos (Neg p))"

(*tests*)
datatype atoms = A | B | C | D | E | F | G | H | I | J | K | L | M | N 

(*valid tests*)
proposition \<open>prover (((Sat (1)  (Pos (Nom (2)))) AND (Sat (2) (Pro A))) 
                     THEN (Sat (1) (Pos (Pro A))))\<close>
  by eval

proposition \<open>prover (NOT (NOT Pro A AND Pro A))\<close>
  by eval

proposition \<open>prover ((NOM 1 AND PRO A) THEN (AT 1 (PRO A)))\<close>
  by eval

proposition \<open>prover (Pro A THEN (Pro B IFF Pro C) THEN Pro A)\<close>
  by eval

proposition \<open>prover ((Pro A OR Pro B) AND (Pro A OR NOT Pro B) THEN (Pro A))\<close>
  by eval

proposition \<open>prover (NOT (NOT(((Pro B OR (NOT Pro C AND Pro D)) IFF (Pro E OR (Pro C THEN Pro A))) 
  IFF (((Pro B OR (NOT Pro C AND Pro D)) THEN (Pro E OR
(Pro C THEN Pro A))) AND ((Pro E OR (Pro C THEN Pro A)) THEN (Pro B OR (NOT Pro C AND Pro D)))))))\<close>
  by eval

proposition \<open>prover (NOT (NOT ((Pro A AND Pro B) THEN ( ((Pro C IFF NOT Pro E) OR NOT Pro F) 
THEN ((Pro A AND Pro B) OR (Pro B OR NOT Pro B)) )) 
AND (Pro A OR Pro B) AND (Pro C IFF NOT Pro D)))\<close>
  by eval

proposition \<open>prover (NOT ((AT (1) (\<diamond> (NOM 2))) 
             AND (AT (2) (Pro A)) AND (AT (1) (\<box> NOT Pro A))))\<close>
  by eval

proposition \<open>prover 
 ((AT (1) (\<diamond>(NOM 3))) THEN 
  ((AT (2) (Pro A)) OR (AT (1) (\<diamond> (AT (2) (NOT Pro A))))))\<close>
  by eval

proposition \<open>prover ((AT (1) (\<diamond> NOM 2)) AND
                     (AT (2) (\<diamond> NOM 3)) AND 
                     (AT (3) (Pro A)) THEN 
                     (AT (1) (\<diamond>(\<diamond> (Pro A)))))\<close>
  by eval

proposition \<open>prover ((AT (1) (\<diamond>\<diamond>\<diamond>\<diamond> Pro A)) THEN (AT (1) (\<diamond>\<diamond>\<diamond>\<diamond> Pro A)))\<close>
  by eval

proposition \<open>prover ((AT (1) ( 
                     (AT (2) (
                     ((\<box>((Pro A) THEN ((NOT ((Pro A) THEN ((Pro B) THEN (Pro A)))) OR (Pro B)))) 
                      THEN ((\<box>(Pro A)) THEN \<box> (Pro B))))))))\<close>
  by eval

proposition \<open>prover ((\<diamond> NOT PRO A) OR (\<box> PRO A))\<close>
  by eval

proposition \<open>prover ((\<diamond> PRO A) OR (NOT (\<diamond> PRO A)))\<close>
  by eval

proposition \<open>prover ((NOT (\<diamond> PRO A)) OR (\<diamond> PRO A))\<close>
  by eval

proposition \<open>prover ((AT (1) (NOT (\<diamond> NOM (1)))) THEN 
                    ((AT (1) (NOM (2) AND (Pro A))) THEN 
                     (AT (1) (NOT (\<diamond> NOM (2))))))\<close>
  by eval

proposition \<open>prover ((\<diamond>PRO A) THEN (\<diamond>PRO A))\<close>
  by eval

proposition \<open>prover ((PRO A) AND (AT 1 (\<diamond> NOM 2)) AND (AT 2 (\<diamond> NOM 1)) THEN (AT 1 (\<diamond>\<diamond> NOM 1)))\<close>
  by eval

proposition \<open>prover ((\<diamond> PRO A) THEN (\<diamond> PRO B) OR (\<diamond> NOT PRO B))\<close>
  by eval

proposition \<open>prover ((\<diamond> PRO A) THEN (\<diamond> NOT PRO B) OR (\<diamond> PRO B))\<close>
  by eval

proposition \<open>prover ((\<diamond> PRO A) THEN (\<diamond> (AT 2 NOT (\<diamond> NOM 1))) OR (AT 2 \<diamond> NOM 1))\<close>
  by eval

proposition \<open>prover ((\<diamond> PRO A) THEN (AT 2 \<diamond> NOM 1 ) OR (\<diamond> (AT 2 NOT (\<diamond> NOM 1))))\<close>
  by eval

(*invalid tests*)
proposition \<open>\<not>(prover (Pro A))\<close>
  by eval

proposition \<open>\<not>(prover (Con (Pro A) (Pro A)))\<close>
  by eval

proposition \<open>\<not>(prover (Con (Neg (Pro A)) (Pro A)))\<close>
  by eval

proposition \<open>\<not>(prover (Sat (1) (Con (Neg (Pro A)) (Pro A))))\<close>
  by eval

proposition \<open>\<not>(prover ( 
  NOT (Pro A AND Pro A) 
  AND (Pro C THEN Pro B) AND NOT (NOT Pro E THEN (Pro C OR NOT NOT Pro D))))\<close>
  by eval

proposition \<open>\<not>(prover ( 
NOT (Pro A AND Pro A) AND (Pro C THEN Pro B) AND
 (AT (1) (NOT (NOT Pro E THEN (Pro C OR NOT NOT Pro D)))) AND
 (AT (2) (AT (3) (Pro C)))
))\<close> 
  by eval

proposition \<open>\<not>(prover (
(\<diamond>(Pro A)) AND (\<diamond>((Pro A) AND (\<diamond>(Pro A)))) AND (\<box>((Pro A) AND (\<diamond>(Pro A)) AND
 (\<diamond>((\<diamond>(NOT (Pro A))) AND (\<box>(Pro B)))))) AND
(\<box>(NOT Pro B)) AND ((Pro A) IFF (Pro C)) AND (\<box>((Pro A) IFF (Pro C))) AND
((Pro K) OR (Pro L) OR (Pro M) OR (Pro N) OR (Pro F)) AND
((NOT Pro K) OR (NOT Pro L) OR (NOT Pro M)) AND
(\<box>\<box>\<box>((Pro K) IFF (Pro L)))
))\<close> 
  by eval


proposition \<open>\<not>prover ((AT (2) (Pro A)) THEN (AT (1) (\<diamond> (AT (2) (Pro A)))))\<close>
  by eval

proposition \<open>\<not>prover ((Pro A) THEN (Sat (1) (Pro A)))\<close>
  by eval

proposition \<open>\<not>prover (AT 1 (\<diamond> ((NOT (AT 1 (\<diamond> NOM 2))) OR (PRO A OR NOT PRO A))))\<close>
  by eval

proposition \<open>\<not>prover ((\<diamond> NOT(\<diamond> PRO A)) OR \<diamond> NOT (\<diamond> PRO A))\<close>
  by eval

proposition \<open>\<not>prover (PRO A THEN \<diamond> PRO A)\<close>
  by eval

(*export
definition \<open>main \<equiv> prover (Sat 1 (Neg (Con (Pro A) (Neg (Pro A)))))\<close>
proposition main by eval
export_code main in Haskell*)

end