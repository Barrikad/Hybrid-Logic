theory HybridSequentCalculus imports Main ListSet
begin

datatype 'a hybr_form 
  =  Pro 'a (\<open>PRO _\<close> [999] 999)
  | Nom nat (\<open>NOM _\<close> [998] 998)
  | Neg \<open>'a hybr_form\<close> (\<open>NOT _\<close> [900] 900)
  | Con \<open>'a hybr_form\<close> \<open>'a hybr_form\<close> (infixl "AND" 300)
  | Sat nat \<open>'a hybr_form\<close> (\<open>AT _ _\<close> [899]  899)
  | Pos \<open>'a hybr_form\<close> (\<open>\<diamond> _\<close> [800] 800)

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
See last case of sv for use
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

lemma reflect_iff[iff]: \<open>reflect nn \<longleftrightarrow> (\<exists> n. (n,n) \<in> set nn)\<close> 
  apply (induct nn)
   apply simp
  by (metis list.set_intros(1) list.set_intros(2) reflect.simps(2) set_ConsD surj_pair)


abbreviation ns_0 where \<open>ns_0 LA RA RN LP RP R Q P \<equiv> 
  nominalsNA LA U nominalsNA RA U nominalsNN RN U
  nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U nominalsNP P\<close>

abbreviation ns_1 where \<open>ns_1 LA RA RN LP RP R Q \<equiv> 
  nominalsNA LA U nominalsNA RA U nominalsNN RN U
  nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q\<close>

context
begin
(*termination functions*)
private primrec pos_count where 
  \<open>pos_count (Pro a) = 0\<close> |
  \<open>pos_count (Nom n) = 0\<close> |
  \<open>pos_count (Neg p) = pos_count p\<close> |
  \<open>pos_count (Con p1 p2) = pos_count p1 + pos_count p2\<close> |
  \<open>pos_count (Sat n p) = pos_count p\<close> |
  \<open>pos_count (Pos p) = Suc (pos_count p)\<close>

private fun pos_countNP where
  \<open>pos_countNP [] = 0\<close> |                                          
  \<open>pos_countNP ((_,p) # NP) = pos_count p + pos_countNP NP\<close>

private fun pos_countNSNP where
  \<open>pos_countNSNP [] = 0\<close> |                                          
  \<open>pos_countNSNP ((_,_,p) # NSNP) = pos_count p + pos_countNSNP NSNP\<close>


private fun missing' where
  \<open>missing' ms [] = 0\<close> |
  \<open>missing' ms (n # ns) = (if \<not>member n ms then Suc (missing' ms ns) else missing' ms ns)\<close>

private fun missing :: "('a \<times> nat list \<times>'b) list \<Rightarrow> nat list \<Rightarrow> nat" where
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

function sv :: \<open>
  (nat \<times> 'a) list \<Rightarrow> (nat \<times> 'a) list \<Rightarrow> (nat \<times> nat) list \<Rightarrow> (nat \<times> nat) list \<Rightarrow> (nat \<times> nat) list \<Rightarrow>
  (nat \<times> (nat list) \<times> 'a hybr_form) list \<Rightarrow> (nat \<times> 'a hybr_form) list \<Rightarrow> (nat \<times> 'a hybr_form) list 
  \<Rightarrow> bool\<close> where
  (*match RHS*)
  \<open>sv LA RA RN LP RP R Q ((n,Pro a) # P) = 
    sv LA ((n,a) # RA) RN LP RP R Q P\<close> |

  \<open>sv LA RA RN LP RP R Q ((n1,Nom n2) # P) = 
    sv LA RA ((n1,n2) # RN) LP RP R Q P\<close> |

  \<open>sv LA RA RN LP RP R Q ((n,Neg p) # P) = 
    sv LA RA RN LP RP R ((n,p) # Q) P\<close> |

  \<open>sv LA RA RN LP RP R Q ((n,Con p1 p2) # P) =
    ((sv LA RA RN LP RP R Q ((n,p1) # P)) \<and> (sv LA RA RN LP RP R Q ((n,p2) # P)))\<close> |

  \<open>sv LA RA RN LP RP R Q ((n1,Sat n2 p) # P) = 
    sv LA RA RN LP RP R Q ((n2,p) # P)\<close> |
(*We need to try to find a nominal witnessing Pos later. See last case*)
  \<open>sv LA RA RN LP RP R Q ((n,Pos p) # P) = 
    sv LA RA RN LP RP ((n,[],p) # R) Q P\<close>|

  (*match LHS*)
  \<open>sv LA RA RN LP RP R ((n,Pro a) # Q) [] = 
    sv ((n,a) # LA) RA RN LP RP R Q []\<close> |
(*we assume/assert that n1=n2. therefore, remove one of them*)
  \<open>sv LA RA RN LP RP R ((n1,Nom n2) # Q) [] = 
    sv (mergeNA LA n1 n2) (mergeNA RA n1 n2) (mergeNN RN n1 n2) 
      (mergeNN LP n1 n2) (mergeNN RP n1 n2) (mergeNSNP R n1 n2) (mergeNP Q n1 n2) []\<close> |

  \<open>sv LA RA RN LP RP R ((n,Neg p) # Q) [] = 
    sv LA RA RN LP RP R Q [(n,p)]\<close> |

  \<open>sv LA RA RN LP RP R ((n,Con p1 p2) # Q) []= 
    sv LA RA RN LP RP R ((n,p1) # (n,p2) # Q) []\<close> |

  \<open>sv LA RA RN LP RP R ((n1,Sat n2 p) # Q) [] = 
    sv LA RA RN LP RP R ((n2,p) # Q) []\<close> |

  \<open>sv LA RA RN LP RP R ((n,Pos p) # Q) [] = (
    let nw = fresh (
      nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U 
      nominalsNN RP U nominalsNSNP R U nominalsNP ((n,Pos p) # Q)) 
    in (sv LA RA RN ((n,nw) # LP) RP R ((nw,p) # Q) []))\<close> |
(*-------Try all relevant assignments of nominals to possibility on RHS-----------
If no assignment can be made, check if current sequent is a tautology.
Else we can process a statement @n\<diamond>P.
  Find a nominal m to witness the statement
  Check if the sequent with @n\<diamond>P removed fulfills both @n\<diamond>m and @mP
Lastly, try another assignment. Remember that we already tried m.*)
  \<open>sv LA RA RN LP RP R [] [] = (
      case 
        saturate R (
          nominalsNA LA U nominalsNA RA U nominalsNN RN U 
          nominalsNN LP U nominalsNN RP U nominalsNSNP R)
      of
        None \<Rightarrow> (common LA RA \<or> common LP RP \<or> reflect RN)
      | Some (n,m,p,R',R'') \<Rightarrow> 
          (sv LA RA RN LP ((n,m) # RP) R' [] [] \<and> sv LA RA RN LP RP R' [] [(m,p)]) 
          \<or> sv LA RA RN LP RP R'' [] [])\<close> 
  by pat_completeness simp_all
(*size definition for proving termination of sv*)

private lemma merge_lengthNSNP: \<open>length nsnp = length (mergeNSNP nsnp n1 n2)\<close> 
  by (induct nsnp) auto

private lemma saturate_size1: \<open>
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
private lemma miss1: \<open>missing' (m # ms) ns \<le> missing' ms ns\<close>
proof (induct ns arbitrary: ms)
  case Nil
  then show ?case by simp
next
  case (Cons a ns)
  then show ?case 
    by (metis member.simps(2) Suc_leD Suc_le_mono missing'.simps(2))
qed  

private lemma miss2: \<open>remove ns ms = m' # ms' \<Longrightarrow> missing' ms ns > missing' (m' # ms) ns\<close>
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

private lemma miss_plus: \<open>missing (R1 @ R2) ns = missing R1 ns + missing R2 ns\<close>
  by (induct R1) auto

private lemma saturate_size2: \<open>
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

private lemma remove_add_missing: "
  is_set A \<Longrightarrow> member a A \<Longrightarrow> missing' X A = missing' X (a # (remove A [a]))"
  apply (induct A)
   apply simp
  by (smt (z3) member.simps(2) add_right_imp_eq is_set.simps(2) is_set_size 
      length_Cons less_not_refl list.size(4) missing'.simps(2) remove.simps(2) remove_size removent)

private lemma missing_set_equal1: \<open>is_set A \<and> is_set B \<Longrightarrow> set_equal A B \<Longrightarrow> missing' X A = missing' X B\<close>
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

private lemma missing_set_equal2: \<open>is_set A \<Longrightarrow> is_set B \<Longrightarrow> set_equal A B \<Longrightarrow> missing X A = missing X B\<close>
  apply (induct X)
   apply simp
  by (smt (verit, ccfv_threshold) Pair_inject list.distinct(1) 
      list.inject missing.elims missing_set_equal1)

private lemma missing_sub_set1: \<open>is_set A  \<Longrightarrow> sub_set A B \<Longrightarrow> missing' X A \<le> missing' X B\<close>
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

private lemma missing_sub_set2: \<open>is_set A \<Longrightarrow> sub_set A B \<Longrightarrow> missing X A \<le> missing X B\<close>
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

private lemma missing_naught: \<open>missing R [] = 0\<close> 
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

private lemma missing_merge1: \<open>missing' (mergeNS ms n1 n2) (mergeNS ns n1 n2) \<le> missing' ms ns\<close>
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
  

private lemma missing_merge: \<open>missing (mergeNSNP R n1 n2) (mergeNS ns n1 n2) \<le> missing R ns\<close> 
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

private lemma pos_merge: \<open>pos_count (mergeP p n1 n2) = pos_count p\<close> 
  by (induct p) simp_all

private lemma pos_mergeNP: \<open>pos_countNP (mergeNP Q n1 n2) = pos_countNP Q\<close>
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

private lemma pos_mergeNSNP: \<open>pos_countNSNP (mergeNSNP R n1 n2) = pos_countNSNP R\<close>
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

private primrec size_atom_form :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a hybr_form \<Rightarrow> nat\<close> where
  \<open>size_atom_form ps r ns (Pro a) = Suc 0\<close> |
  \<open>size_atom_form ps r ns (Nom n) = Suc 0\<close> |
  \<open>size_atom_form ps r ns (Neg p) = Suc (size_atom_form ps r ns p)\<close> |
  \<open>size_atom_form ps r ns (Con p1 p2) = Suc (
    size_atom_form ps r ns p1 + 
    size_atom_form ps r ns p2)\<close> |
  \<open>size_atom_form ps r ns (Sat n p) = Suc (size_atom_form ps r ns p)\<close> |
  \<open>size_atom_form ps r ns (Pos p) = ps + r + ns + Suc (Suc (size_atom_form ps r ns p))\<close>

private lemma size_atom_form_size_ns: \<open>
  ns \<le> ms \<Longrightarrow> psn \<le> psm \<Longrightarrow> size_atom_form psn r ns p \<le> size_atom_form psm r ms p\<close> 
  by (induct p) auto

private lemma lesser_sum: \<open>(\<forall>x. 
    (f :: 'a \<Rightarrow> nat) x \<le> (f' :: 'a \<Rightarrow> nat) x) \<Longrightarrow> 
    (\<Sum> x \<leftarrow> (X :: 'a list). f x) \<le> (\<Sum> x \<leftarrow> X. f' x)\<close>
  by (simp add: sum_list_mono)

private lemma lesser_add: \<open>(a :: nat) \<le> b \<Longrightarrow> c \<le> d \<Longrightarrow> a + c \<le> b + d\<close>
  by simp

private abbreviation ps_0 where \<open>ps_0 R Q P \<equiv> pos_countNSNP R + pos_countNP Q + pos_countNP P\<close>

private abbreviation n1_0 where 
  \<open>n1_0 Q ps R ns \<equiv> \<Sum>(u, p)\<leftarrow>Q. size_atom_form ps (length R) (length ns) p\<close>

private abbreviation n2_0 where 
  \<open>n2_0 ps R ns \<equiv> \<Sum>(u, u', p)\<leftarrow>R. Suc (size_atom_form ps (length R) (length ns) p)\<close>

private lemma n1_0_ps_less: \<open>
  length ns \<le> length ns' \<Longrightarrow> ps \<le> ps' \<Longrightarrow> 
  n1_0 Q ps R ns \<le> n1_0 Q ps' R ns'\<close>
  by (simp add: lesser_sum size_atom_form_size_ns)

private lemma n2_0_ps_less: \<open>length ns \<le> length ns' \<Longrightarrow> ps \<le> ps' \<Longrightarrow> n2_0 ps R ns \<le> n2_0 ps' R ns'\<close>
  by (simp add: lesser_sum size_atom_form_size_ns)

private lemma size_atom_suc_dec: \<open>
  ns + ps + R = ns' + ps' + R' \<Longrightarrow> size_atom_form ps R ns p = size_atom_form ps' R' ns' p\<close> 
  by (induct p) simp_all

private lemma size_atom_suc_dec2: \<open>
  ns + ps + R \<le> ns' + ps' + R' \<Longrightarrow> size_atom_form ps R ns p \<le> size_atom_form ps' R' ns' p\<close> 
  by (induct p) simp_all

private lemma n1_0_suc_dec: \<open>ps + ns + r \<le> ps' + ns' + r' \<Longrightarrow>
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

private lemma n1_0_suc_dec2: \<open>ps + length ns + length R \<le> ps' + length ns' + length R' \<Longrightarrow>
  n1_0 Q ps R ns \<le>
  n1_0 Q ps' R' ns'\<close> 
  using n1_0_suc_dec by blast

private lemma n2_0_suc_dec: \<open>ps + ns + r \<le> ps' + ns' + r' \<Longrightarrow>
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

private lemma n2_0_suc_dec2: \<open>ps + length ns \<le> ps' + length ns' \<Longrightarrow>
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

private lemma sum_suc: "(\<Sum>(u, u', p)\<leftarrow>R. Suc (f p)) = (\<Sum>(u, u', p)\<leftarrow>R. f p) + length R" 
  by (induct R) auto

private lemma missing_less: \<open>missing' ms ns \<le> length ns\<close>
  by (induct ns)  auto

private lemma merge_size_atom:\<open>ns \<le> ns' \<Longrightarrow> R \<le> R' \<Longrightarrow> ps \<le> ps' \<Longrightarrow>
  size_atom_form ps R ns (mergeP p n1 n2) \<le> 
  size_atom_form ps' R' ns' p\<close> 
  by (induct p) simp_all

private lemma missing_add_length: \<open>missing R (add n ns) \<le> missing R ns + length R\<close> 
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

private lemma merge_n1_0: \<open>length ns \<le> length ns' \<Longrightarrow> length R \<le> length R' \<Longrightarrow> ps \<le> ps' \<Longrightarrow>
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

private lemma merge_n2_0_1:\<open>ns \<le> ns' \<Longrightarrow> ps \<le> ps' \<Longrightarrow> 
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

private lemma merge_n2_0: \<open>length ns \<le> length ns' \<Longrightarrow> ps \<le> ps' \<Longrightarrow> 
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

private lemma n2_0_lesser:\<open>(ps \<le> ps' \<Longrightarrow> Rl \<le> Rl' \<Longrightarrow> ns \<le> ns' \<Longrightarrow> 
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

private lemma pos_count_con: \<open>pos_countNSNP (A @ B) = pos_countNSNP A + pos_countNSNP B\<close> 
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

(*auxiliary*)
definition agrees where \<open>agrees f x y = (\<lambda> x'. if x' = x then y else f x')\<close>

lemma exi_pop: \<open>(\<exists> x' \<in> set (x # xs). P x') \<longleftrightarrow> ((\<exists> x' \<in> set xs. P x') \<or> P x)\<close> 
  by (metis list.set_intros(1) list.set_intros(2) set_ConsD)

lemma fa_pop: \<open>(\<forall> x' \<in> set (x # xs). P x') \<longleftrightarrow> ((\<forall> x' \<in> set xs. P x') \<and> P x)\<close> 
  by (metis list.set_intros(1) list.set_intros(2) set_ConsD)

lemma merge_NS_exi_1: \<open>
  n \<in> set (mergeNS ns n1 n2) \<longrightarrow> 
    (\<exists> n' \<in> set ns. (if n' = n1 then n = n2 else n = n'))\<close> 
proof (induct ns)
  case Nil
  then show ?case by simp
next
  case (Cons n' ns)
  show ?case 
  proof
    assume "n \<in> set (mergeNS (n' # ns) n1 n2)"
    then have 
      \<open>n \<in> set (mergeNS [n'] n1 n2) \<or> n \<in> set (mergeNS ns n1 n2)\<close>
      using last_ConsL set_ConsD by fastforce
    moreover have \<open>n \<in> set (mergeNS [n'] n1 n2) \<Longrightarrow> 
      (if n' = n1 then n = n2 else n = n')\<close> 
      by auto
    moreover have \<open>n' \<in> set (n' # ns)\<close> 
      by (metis list.set_intros(1))
    moreover have \<open>n \<in> set (mergeNS ns n1 n2) \<Longrightarrow> \<exists>n'' \<in> set (n' # ns).
       (if n'' = n1 then n = n2 else n = n'')\<close> 
      by (meson Cons.hyps list.set_intros(2))
    ultimately show "\<exists>n' \<in> set (n' # ns).
       (if n' = n1 then n = n2 else n = n')" 
      by blast
  qed
qed

lemma merge_NS_exi_2: \<open>
  n' \<in> set ns \<longrightarrow> 
    (\<exists> n \<in> set (mergeNS ns n1 n2). (if n' = n1 then n = n2 else n = n'))\<close> 
proof (induct ns)
  case Nil
  then show ?case by simp
next
  case (Cons n ns)
  show ?case 
  proof
    assume a:"n' \<in> set (n # ns)"
    then have 
      \<open>n' = n \<or> n' \<in> set ns\<close>
      using last_ConsL set_ConsD by fastforce
    moreover have \<open>n = n' \<Longrightarrow> 
      (\<exists> n \<in> set (mergeNS (n # ns) n1 n2). (if n' = n1 then n = n2 else n = n'))\<close> 
      by (metis ListSet.member.simps(2) member_iff member_mergeNS2 member_mergeNS3)
    ultimately show "
      (\<exists> n \<in> set (mergeNS (n # ns) n1 n2). (if n' = n1 then n = n2 else n = n'))" 
      by (metis a member_iff member_mergeNS2 member_mergeNS3) 
  qed
qed

lemma merge_NSNP_exi_1: \<open>
  (n,ns,p) \<in> set (mergeNSNP nsnp n1 n2) \<longrightarrow> 
    (\<exists> (n',ns',p') \<in> set nsnp. (if n' = n1 then n = n2 else n = n') \<and> 
      ns = mergeNS ns' n1 n2 \<and> p = mergeP p' n1 n2)\<close> 
proof (induct nsnp arbitrary: n ns p)
  case Nil
  then show ?case by simp
next
  case (Cons a nsnp)
  obtain n' ns' p' where adef:\<open>a = (n',ns',p')\<close> 
    using prod_cases3 by blast
  show ?case 
  proof
    assume "(n, ns, p) \<in> set (mergeNSNP (a # nsnp) n1 n2)"
    then have 
      \<open>(n,ns,p) \<in> set (mergeNSNP [a] n1 n2) \<or> (n,ns,p) \<in> set (mergeNSNP nsnp n1 n2)\<close>
      using adef last_ConsL set_ConsD by fastforce
    moreover have \<open>(n,ns,p) \<in> set (mergeNSNP [a] n1 n2) \<Longrightarrow> 
      (if n' = n1 then n = n2 else n = n') \<and> ns = mergeNS ns' n1 n2 \<and> p = mergeP p' n1 n2\<close> 
      using adef by auto
    moreover have \<open>(n', ns', p') \<in> set (a # nsnp)\<close> 
      by (metis adef list.set_intros(1))
    moreover have \<open>(n,ns,p) \<in> set (mergeNSNP nsnp n1 n2) \<Longrightarrow> \<exists>(n', ns', p')\<in>set (a # nsnp).
       (if n' = n1 then n = n2 else n = n') \<and> ns = mergeNS ns' n1 n2 \<and> p = mergeP p' n1 n2\<close> 
      by (metis (no_types, lifting) Cons.hyps exi_pop)
    ultimately show "\<exists>(n', ns', p')\<in>set (a # nsnp).
       (if n' = n1 then n = n2 else n = n') \<and> ns = mergeNS ns' n1 n2 \<and> p = mergeP p' n1 n2"
      by auto
  qed
qed

lemma merge_NSNP_exi_2: \<open>
  (n',ns',p') \<in> set nsnp \<Longrightarrow> 
    \<exists> (n,ns,p) \<in> set (mergeNSNP nsnp n1 n2). 
      (if n' = n1 then n = n2 else n = n') \<and> ns = mergeNS ns' n1 n2 \<and> p = mergeP p' n1 n2\<close> 
proof (induct nsnp)
  case Nil
  then show ?case by simp
next
  case (Cons a nsnp)
  consider \<open>(n',ns',p') = a\<close> | \<open>(n',ns',p') \<in> set nsnp\<close>  
    by (metis Cons.prems set_ConsD)
  then show ?case 
  proof cases
    case 1
    then show ?thesis 
      using list.set_intros(1) by fastforce
  next
    case 2
    then have \<open>\<exists> (n, ns, p) \<in> set (mergeNSNP nsnp n1 n2).
       (if n' = n1 then n = n2 else n = n') \<and> ns = mergeNS ns' n1 n2 \<and> p = mergeP p' n1 n2\<close> 
      using Cons.hyps by auto
    then obtain n ns p where 
      \<open>(n, ns, p) \<in> set (mergeNSNP nsnp n1 n2) \<and> 
        (if n' = n1 then n = n2 else n = n') \<and> ns = mergeNS ns' n1 n2 \<and> p = mergeP p' n1 n2\<close> 
      by blast
    moreover have \<open>(n, ns, p) \<in> set (mergeNSNP (a # nsnp) n1 n2)\<close>
      by (metis calculation list.set_intros(2) mergeNSNP.simps(2) prod_cases3)
    ultimately show ?thesis 
      by blast
  qed
qed

lemma merge_NN_exi_1: \<open>
  (na,nb) \<in> set (mergeNN nn n1 n2) \<longrightarrow> 
    (\<exists> (na',nb') \<in> set nn. (if na' = n1 then na = n2 else na = na') \<and> 
      (if nb' = n1 then nb = n2 else nb = nb'))\<close> 
proof (induct nn)
  case Nil
  then show ?case by simp
next
  case (Cons a nn)
  obtain na' nb' where adef:\<open>a = (na',nb')\<close> 
    using prod.exhaust_sel by blast
  show ?case 
  proof
    assume "(na, nb) \<in> set (mergeNN (a # nn) n1 n2)"
    then have 
      \<open>(na,nb) \<in> set (mergeNN [a] n1 n2) \<or> (na,nb) \<in> set (mergeNN nn n1 n2)\<close>
      using adef last_ConsL set_ConsD by fastforce
    moreover have \<open>(na,nb) \<in> set (mergeNN [a] n1 n2) \<Longrightarrow> 
      (if na' = n1 then na = n2 else na = na') \<and> (if nb' = n1 then nb = n2 else nb = nb')\<close> 
      using adef by auto
    moreover have \<open>(na', nb') \<in> set (a # nn)\<close> 
      by (metis adef list.set_intros(1))
    moreover have \<open>(na,nb) \<in> set (mergeNN nn n1 n2) \<Longrightarrow> \<exists>(na', nb')\<in>set (a # nn).
      (if na' = n1 then na = n2 else na = na') \<and> (if nb' = n1 then nb = n2 else nb = nb')\<close> 
      by (metis (no_types, lifting) Cons.hyps exi_pop)
    ultimately show "\<exists>(na', nb')\<in>set (a # nn).
      (if na' = n1 then na = n2 else na = na') \<and> (if nb' = n1 then nb = n2 else nb = nb')"
      by blast
  qed
qed

lemma merge_NN_exi_2: \<open>
  (na',nb') \<in> set nn \<Longrightarrow> 
    \<exists> (na,nb) \<in> set (mergeNN nn n1 n2). 
      (if na' = n1 then na = n2 else na = na') \<and> (if nb' = n1 then nb = n2 else nb = nb')\<close> 
proof (induct nn)
  case Nil
  then show ?case by simp
next
  case (Cons a nn)
  consider \<open>(na',nb') = a\<close> | \<open>(na',nb') \<in> set nn\<close>  
    by (metis Cons.prems set_ConsD)
  then show ?case 
  proof cases
    case 1
    then show ?thesis 
      using list.set_intros(1) by fastforce
  next
    case 2
    then have \<open>\<exists> (na, nb) \<in> set (mergeNN nn n1 n2).
       (if na' = n1 then na = n2 else na = na') \<and> (if nb' = n1 then nb = n2 else nb = nb')\<close> 
      using Cons.hyps by auto
    then obtain na nb where 
      \<open>(na, nb) \<in> set (mergeNN nn n1 n2) \<and> 
        (if na' = n1 then na = n2 else na = na') \<and> (if nb' = n1 then nb = n2 else nb = nb')\<close> 
      by blast
    moreover have \<open>(na, nb) \<in> set (mergeNN (a # nn) n1 n2)\<close>
      by (metis List.insert_def calculation list.inject list.set_intros(2) mergeNN.simps(2) 
          neq_Nil_conv nominalsNN.cases old.prod.exhaust)
    ultimately show ?thesis 
      by blast
  qed
qed

lemma merge_NA_exi_1: \<open>
  (n,a) \<in> set (mergeNA na n1 n2) \<longrightarrow> 
    (\<exists> (n',a') \<in> set na. (if n' = n1 then n = n2 else n = n') \<and> a' = a)\<close> 
proof (induct na)
  case Nil
  then show ?case by simp
next
  case (Cons b na)
  obtain n' a' where adef:\<open>b = (n',a')\<close> 
    using prod.exhaust_sel by blast
  show ?case 
  proof
    assume "(n, a) \<in> set (mergeNA (b # na) n1 n2)"
    then have 
      \<open>(n,a) \<in> set (mergeNA [b] n1 n2) \<or> (n,a) \<in> set (mergeNA na n1 n2)\<close>
      using adef last_ConsL set_ConsD by fastforce
    moreover have \<open>(n,a) \<in> set (mergeNA [b] n1 n2) \<Longrightarrow> 
      (if n' = n1 then n = n2 else n = n') \<and> a' = a\<close> 
      using adef by auto
    moreover have \<open>(n', a') \<in> set (b # na)\<close> 
      by (metis adef list.set_intros(1))
    moreover have \<open>(n,a) \<in> set (mergeNA na n1 n2) \<Longrightarrow> \<exists>(n', a')\<in>set (b # na).
      (if n' = n1 then n = n2 else n = n') \<and> a' = a\<close> 
      by (metis (no_types, lifting) Cons.hyps exi_pop)
    ultimately show "\<exists>(n', a')\<in>set (b # na).
      (if n' = n1 then n = n2 else n = n') \<and> a' = a"
      by blast
  qed
qed

lemma merge_NA_exi_2: \<open>
  (n',a') \<in> set na \<Longrightarrow> 
    \<exists> (n,a) \<in> set (mergeNA na n1 n2). 
      (if n' = n1 then n = n2 else n = n') \<and> a = a'\<close> 
proof (induct na)
  case Nil
  then show ?case by simp
next
  case (Cons a na)
  consider \<open>(n',a') = a\<close> | \<open>(n',a') \<in> set na\<close>  
    by (metis Cons.prems set_ConsD)
  then show ?case 
  proof cases
    case 1
    then show ?thesis 
      using list.set_intros(1) by fastforce
  next
    case 2
    then have \<open>\<exists> (n, a) \<in> set (mergeNA na n1 n2).
       (if n' = n1 then n = n2 else n = n') \<and> a = a'\<close> 
      using Cons.hyps by auto
    then obtain n a'' where 
      \<open>(n, a'') \<in> set (mergeNA na n1 n2) \<and> 
        (if n' = n1 then n = n2 else n = n') \<and> a'' = a'\<close> 
      by blast
    moreover have \<open>(n, a'') \<in> set (mergeNA (a # na) n1 n2)\<close> 
      by (metis calculation list.distinct(1) list.inject list.set_intros(2) mergeNA.elims)
    ultimately show ?thesis 
      by blast
  qed
qed

lemma merge_NP_exi_1: \<open>
  (n,p) \<in> set (mergeNP np n1 n2) \<longrightarrow> 
    (\<exists> (n',p') \<in> set np. (if n' = n1 then n = n2 else n = n') \<and> p = mergeP p' n1 n2)\<close> 
proof (induct np)
  case Nil
  then show ?case by simp
next
  case (Cons a np)
  obtain n' p' where adef:\<open>a = (n',p')\<close> 
    using prod.exhaust_sel by blast
  show ?case 
  proof
    assume "(n, p) \<in> set (mergeNP (a # np) n1 n2)"
    then have 
      \<open>(n,p) \<in> set (mergeNP [a] n1 n2) \<or> (n,p) \<in> set (mergeNP np n1 n2)\<close>
      using adef last_ConsL set_ConsD by fastforce
    moreover have \<open>(n,p) \<in> set (mergeNP [a] n1 n2) \<Longrightarrow> 
      (if n' = n1 then n = n2 else n = n') \<and> p = mergeP p' n1 n2\<close> 
      using adef by auto
    moreover have \<open>(n', p') \<in> set (a # np)\<close> 
      by (metis adef list.set_intros(1))
    moreover have \<open>(n,p) \<in> set (mergeNP np n1 n2) \<Longrightarrow> \<exists>(n', p')\<in>set (a # np).
      (if n' = n1 then n = n2 else n = n') \<and> p = mergeP p' n1 n2\<close> 
      by (metis (no_types, lifting) Cons.hyps exi_pop)
    ultimately show "\<exists>(n', p')\<in>set (a # np).
      (if n' = n1 then n = n2 else n = n') \<and> p = mergeP p' n1 n2"
      by blast
  qed
qed

lemma merge_NP_exi_2: \<open>
  (n',p') \<in> set np \<Longrightarrow> 
    \<exists> (n,p) \<in> set (mergeNP np n1 n2). 
      (if n' = n1 then n = n2 else n = n') \<and> p = mergeP p' n1 n2\<close> 
proof (induct np)
  case Nil
  then show ?case by simp
next
  case (Cons a np)
  consider \<open>(n',p') = a\<close> | \<open>(n',p') \<in> set np\<close>  
    by (metis Cons.prems set_ConsD)
  then show ?case 
  proof cases
    case 1
    then show ?thesis 
      using list.set_intros(1) by fastforce
  next
    case 2
    then have \<open>\<exists> (n, p) \<in> set (mergeNP np n1 n2).
       (if n' = n1 then n = n2 else n = n') \<and> p = mergeP p' n1 n2\<close> 
      using Cons.hyps by auto
    then obtain n p where 
      \<open>(n, p) \<in> set (mergeNP np n1 n2) \<and> 
        (if n' = n1 then n = n2 else n = n') \<and> p = mergeP p' n1 n2\<close> 
      by blast
    moreover have \<open>(n, p) \<in> set (mergeNP (a # np) n1 n2)\<close> 
      by (metis calculation list.distinct(1) list.inject list.set_intros(2) mergeNP.elims)
    ultimately show ?thesis 
      by blast
  qed
qed

lemma nomNP_member: \<open>(n,p) \<in> set np \<Longrightarrow> 
  member n (nominalsNP np) \<and> sub_set (nominalsForm p) (nominalsNP np)\<close> 
proof (induct np)
  case Nil
then show ?case by simp
next
  case (Cons a np)
  then obtain n' p' where adef:\<open>a = (n',p')\<close> 
    by (metis surj_pair)
  consider \<open>n = n' \<and> p = p'\<close> | \<open>(n,p) \<in> set np\<close> 
    by (metis Cons.prems adef prod.inject set_ConsD)
  then show ?case 
  proof cases
    case 1
    then show ?thesis 
      by (metis ListSet.member.simps(2) add_def add_sub_set adef nominalsNP.simps(2) sub_set_union1)
  next
    case 2
    then have 3:\<open>member n (nominalsNP np) \<and> sub_set (nominalsForm p) (nominalsNP np)\<close> 
      using Cons.hyps by blast
    then have \<open>member n (nominalsNP (a # np))\<close> 
      by (smt (verit, ccfv_threshold) ListSet.member.simps(2) add_def list.discI list.inject 
          nominalsNP.elims union_member)
    moreover have \<open>sub_set (nominalsForm p) (nominalsNP (a # np))\<close>
      using 3 by (metis add_sub_set adef member_sub_set nominalsNP.simps(2) sub_set_union2)
    ultimately show ?thesis by simp
  qed
qed

lemma nomNN_member: \<open>(n1,n2) \<in> set nn \<Longrightarrow> member n1 (nominalsNN nn) \<and> member n2 (nominalsNN nn)\<close>
  apply (induct nn)
   apply simp
  using ListSet.member.simps(2) set_ConsD by fastforce

lemma nomNA_member: \<open>(n,a) \<in> set na \<Longrightarrow> member n (nominalsNA na)\<close>
  apply (induct na)
   apply simp
  using ListSet.member.simps(2) set_ConsD by fastforce

lemma nomNSNP_member: \<open>
  (n,ns,p) \<in> set nsnp \<Longrightarrow> member n (nominalsNSNP nsnp) \<and> sub_set ns (nominalsNSNP nsnp) \<and> 
      sub_set (nominalsForm p) (nominalsNSNP nsnp)\<close>
proof (induct nsnp)
  case Nil
  then show ?case by simp
next
  case (Cons a nsnp)
  then obtain n' ns' p' where adef:\<open>a = (n',ns',p')\<close> 
    by (metis surj_pair)
  consider \<open>n = n' \<and> ns = ns' \<and> p = p'\<close> | \<open>(n,ns,p) \<in> set nsnp\<close> 
    by (metis Cons.prems adef prod.inject set_ConsD)
  then show ?case 
  proof cases
    case 1
    then show ?thesis 
      by (smt (verit, ccfv_SIG) ListSet.member.simps(2) add_def adef member_sub_set 
          nominalsNSNP.simps(2) sub_set_union1 sub_set_union2)
  next
    case 2
    then have 3:\<open>member n (nominalsNSNP nsnp)\<and> sub_set ns (nominalsNSNP nsnp) \<and> 
      sub_set (nominalsForm p) (nominalsNSNP nsnp)\<close> 
      using Cons.hyps by blast
    then have \<open>member n (nominalsNSNP (a # nsnp))\<close> 
      by (smt (verit, ccfv_threshold) ListSet.member.simps(2) add_def list.discI list.inject 
          nominalsNSNP.elims union_member)
    moreover have \<open>sub_set ns (nominalsNSNP (a # nsnp))\<close>
      using "3" adef union_member by fastforce
    moreover have \<open>sub_set (nominalsForm p) (nominalsNSNP (a # nsnp))\<close> 
      using "3" adef union_member by fastforce
    ultimately show ?thesis by simp
  qed
qed
(*\auxiliary*)

(*truthiness*)
definition prover where 
  \<open>prover p \<equiv> sv [] [] [] [] [] [] [] [(fresh (nominalsForm p),p)]\<close>

primrec semantics :: \<open>('c \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
                  (nat \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> 'a hybr_form \<Rightarrow> bool\<close> where
  \<open>semantics RE V G w (Pro a) = V w a\<close> |
  \<open>semantics RE V G w (Nom n) = ((G n) = w)\<close> |
  \<open>semantics RE V G w (Neg p) = (\<not> semantics RE V G w p)\<close> |
  \<open>semantics RE V G w (Con p1 p2) = (semantics RE V G w p1 \<and> semantics RE V G w p2)\<close> |
  \<open>semantics RE V G w (Sat n p) = semantics RE V G (G n) p\<close> |
  \<open>semantics RE V G w (Pos p) = (\<exists> v. (RE w v) \<and> (semantics RE V G v p))\<close>

definition \<open>sc RE V G LA RA RN LP RP R Q P \<equiv> 
  (
    (\<forall> (n,p) \<in> set Q. semantics RE V G (G n) p) \<and> 
    (\<forall> (n1,n2) \<in> set LP. RE (G n1) (G n2)) \<and>
    (\<forall> (n,a) \<in> set LA. V (G n) a)
  ) \<longrightarrow> (
    (\<exists> (n,p) \<in> set P. semantics RE V G (G n) p) \<or>
    (\<exists> (n,ns,p) \<in> set R. (\<exists> w. RE (G n) w \<and> semantics RE V G w p)) \<or>
    (\<exists> (n1,n2) \<in> set RP. RE (G n1) (G n2)) \<or>
    (\<exists> (n1,n2) \<in> set RN. (G n1) = (G n2)) \<or>
    (\<exists> (n,a) \<in> set RA. V (G n) a)
  )\<close>

lemma agrees_semantics: \<open>
  \<not>member n (nominalsForm p) \<Longrightarrow> semantics RE V G w p = semantics RE V (agrees G n w') w p\<close>
proof (induct p arbitrary: w)
  case (Nom x)
  then show ?case 
    by (metis ListSet.member.simps(2) agrees_def nominalsForm.simps(2) semantics.simps(2))
next
  case (Con p1 p2)
  then show ?case 
    by (metis nominalsForm.simps(4) semantics.simps(4) union_member)
next
  case (Sat n' p)
  have \<open>n' \<noteq> n\<close> 
    by (metis ListSet.member.simps(2) Sat.prems add_def nominalsForm.simps(5))
  then have \<open>
    semantics RE V (agrees G n w') w (AT n' p) = 
      semantics RE V (agrees G n w') (G n') p\<close> 
    by (simp add: agrees_def)
  moreover have \<open>\<not> member n (nominalsForm p)\<close>
    by (metis ListSet.member.simps(2) Sat.prems add_def nominalsForm.simps(5))
  ultimately show ?case 
    by (metis Sat.hyps semantics.simps(5))
qed auto

lemma sc_semantics_iff: \<open>
  semantics RE V G w p \<longleftrightarrow> 
  (let n = fresh (nominalsForm p) in sc RE V (agrees G n w) [] [] [] [] [] [] [] [(n,p)])\<close> 
(is "?L \<longleftrightarrow> ?R")
proof-
  let ?n = \<open>fresh (nominalsForm p)\<close>
  let ?D = \<open>(\<lambda>n1. (\<exists> w'. RE ((agrees G ?n w) n1) w' \<and> semantics RE V (agrees G ?n w) w' p))\<close>
  have "(\<forall> p \<in> set []. semantics RE V (agrees G ?n w) w p)" (is ?A)
    by simp
  moreover have \<open>\<forall> (n1,n2) \<in> set []. RE ((agrees G ?n w) n1) ((agrees G ?n w) n2)\<close> (is ?B)
    by simp
  moreover have \<open>\<forall> (n,a) \<in> set []. V ((agrees G ?n w) n) a\<close> (is ?C)
    by simp
  moreover have \<open>\<not>(\<exists> (n1,u,p) \<in> set []. ?D n1)\<close>
    by simp
  moreover have \<open>\<not>(\<exists> (n1,n2) \<in> set []. RE ((agrees G ?n w) n1) ((agrees G ?n w) n2))\<close> (is "\<not>?E")
    by simp
  moreover have \<open>\<not>(\<exists> (n1,n2) \<in> set []. ((agrees G ?n w) n1) = ((agrees G ?n w) n2))\<close> (is "\<not>?F")
    by simp
  moreover have \<open>\<not>(\<exists> (n,a) \<in> set []. V ((agrees G ?n w) n) a)\<close> (is "\<not>?G")
    by simp
  moreover have \<open>
    ?R \<longleftrightarrow> (?A \<and> ?B \<and> ?C \<longrightarrow>  
      (\<exists> (n',p') \<in> set [(?n,p)]. 
        semantics RE V (agrees G ?n w) ((agrees G ?n w) n') p') \<or> 
      (\<exists> (n1,u,p) \<in> set []. ?D n1) \<or> ?E \<or> ?F \<or> ?G)\<close> 
    by (simp add: sc_def Let_def)
  ultimately have \<open>?R \<longleftrightarrow> semantics RE V (agrees G ?n w) w p\<close> 
    by (simp add: agrees_def)
  then show ?thesis 
    using agrees_semantics fresh_new by fast
qed

lemma sc_pop_P:\<open>
  sc RE V G LA RA RN LP RP R Q ((n,p) # P) \<longleftrightarrow> 
    sc RE V G LA RA RN LP RP R Q P \<or> semantics RE V G (G n) p\<close> (is \<open>?L1 \<longleftrightarrow> ?R1 \<or> ?R2\<close>)
proof-
  have \<open>?L1 \<longleftrightarrow> (
    (\<forall> (n,p) \<in> set Q. semantics RE V G (G n) p) \<and> 
    (\<forall> (n1,n2) \<in> set LP. RE (G n1) (G n2)) \<and>
    (\<forall> (n,a) \<in> set LA. V (G n) a)
  ) \<longrightarrow> (
    (\<exists> (n,p) \<in> set ((n,p) # P). semantics RE V G (G n) p) \<or>
    (\<exists> (n1,u,p) \<in> set R. 
      (\<exists> w. RE (G n1) w \<and> semantics RE V G w p)) \<or>
    (\<exists> (n1,n2) \<in> set RP. RE (G n1) (G n2)) \<or>
    (\<exists> (n1,n2) \<in> set RN. (G n1) = (G n2)) \<or>
    (\<exists> (n,a) \<in> set RA. V (G n) a)
  )\<close> (is \<open>?L1 \<longleftrightarrow> (?L2 \<longrightarrow> ?EXP \<or> ?R3)\<close>)
    by (simp add: sc_def)
  then have \<open>?L1 \<longleftrightarrow> (?L2 \<longrightarrow> ?R3) \<or> ?EXP\<close>
    by meson
  moreover have \<open>?EXP = ((\<exists> (n,p) \<in> set P. semantics RE V G (G n) p) \<or> ?R2)\<close> 
    (is \<open>?EXP = (?R4 \<or> ?R2)\<close>) 
    using exi_pop by (smt (verit) case_prod_conv) 
  moreover have \<open>?R1 = (?L2 \<longrightarrow> ?R4 \<or> ?R3)\<close> 
    by (simp add: sc_def)
  ultimately show ?thesis 
    by meson 
qed

lemma sc_pop_R:\<open>
  sc RE V G LA RA RN LP RP ((n,ns,p) # R) Q P \<longleftrightarrow> 
    sc RE V G LA RA RN LP RP R Q P \<or> (
      (\<exists> w. RE (G n) w \<and> semantics RE V G w p))\<close> 
(is \<open>?L1 \<longleftrightarrow> ?R1 \<or> ?R2\<close>)
proof-
  have \<open>?L1 \<longleftrightarrow> (
    (\<forall> (n,p) \<in> set Q. semantics RE V G (G n) p) \<and> 
    (\<forall> (n1,n2) \<in> set LP. RE (G n1) (G n2)) \<and>
    (\<forall> (n,a) \<in> set LA. V (G n) a)
  ) \<longrightarrow> (
    (\<exists> (n,p) \<in> set P. semantics RE V G (G n) p) \<or>
    (\<exists> (n1,u,p) \<in> set ((n,ns,p) # R). 
      (\<exists> w. RE (G n1) w \<and> semantics RE V G w p)) \<or>
    (\<exists> (n1,n2) \<in> set RP. RE (G n1) (G n2)) \<or>
    (\<exists> (n1,n2) \<in> set RN. (G n1) = (G n2)) \<or>
    (\<exists> (n,a) \<in> set RA. V (G n) a)
  )\<close> (is \<open>?L1 \<longleftrightarrow> (?L2 \<longrightarrow> ?Q1 \<or> ?EXR \<or> ?R3)\<close>)
    by (simp add: sc_def)
  then have \<open>?L1 \<longleftrightarrow> (?L2 \<longrightarrow> ?Q1 \<or> ?R3) \<or> ?EXR\<close>
    by meson
  moreover have \<open>
    ?EXR = ((\<exists> (n1,u,p) \<in> set R.
      (\<exists> w. RE (G n1) w \<and> semantics RE V G w p)) \<or> ?R2)\<close> 
    (is \<open>?EXP = (?R4 \<or> ?R2)\<close>) 
    using exi_pop by (smt (verit) case_prod_conv) 
  moreover have \<open>?R1 = (?L2 \<longrightarrow> ?Q1 \<or> ?R4 \<or> ?R3)\<close> 
    by (simp add: sc_def)
  ultimately show ?thesis 
    by meson 
qed

lemma sc_pop_RP:\<open>
  sc RE V G LA RA RN LP ((n1,n2) # RP) R Q P \<longleftrightarrow> 
    sc RE V G LA RA RN LP RP R Q P \<or> RE (G n1) (G n2)\<close> 
(is \<open>?L1 \<longleftrightarrow> ?R1 \<or> ?R2\<close>)
proof-
  have \<open>?L1 \<longleftrightarrow> (
    (\<forall> (n,p) \<in> set Q. semantics RE V G (G n) p) \<and> 
    (\<forall> (n1,n2) \<in> set LP. RE (G n1) (G n2)) \<and>
    (\<forall> (n,a) \<in> set LA. V (G n) a)
  ) \<longrightarrow> (
    (\<exists> (n,p) \<in> set P. semantics RE V G (G n) p) \<or>
    (\<exists> (n1,u,p) \<in> set R. 
      (\<exists> w. RE (G n1) w \<and> semantics RE V G w p)) \<or>
    (\<exists> (n1,n2) \<in> set ((n1,n2) # RP). RE (G n1) (G n2)) \<or>
    (\<exists> (n1,n2) \<in> set RN. (G n1) = (G n2)) \<or>
    (\<exists> (n,a) \<in> set RA. V (G n) a)
  )\<close> (is \<open>?L1 \<longleftrightarrow> (?L2 \<longrightarrow> ?Q1 \<or> ?Q2 \<or> ?EXRP \<or> ?R3)\<close>)
    by (simp add: sc_def)
  then have \<open>?L1 \<longleftrightarrow> (?L2 \<longrightarrow> ?Q1 \<or> ?Q2 \<or> ?R3) \<or> ?EXRP\<close>
    by meson
  moreover have \<open>
    ?EXRP = ((\<exists> (n1,n2) \<in> set RP. RE (G n1) (G n2)) \<or> ?R2)\<close> 
    (is \<open>?EXP = (?R4 \<or> ?R2)\<close>) 
    using exi_pop by (smt (verit) case_prod_conv) 
  moreover have \<open>?R1 = (?L2 \<longrightarrow> ?Q1 \<or> ?Q2 \<or> ?R4 \<or> ?R3)\<close> 
    by (simp add: sc_def)
  ultimately show ?thesis 
    by meson 
qed

lemma sc_pop_RN:\<open>
  sc RE V G LA RA ((n1,n2) # RN) LP RP R Q P \<longleftrightarrow> 
    sc RE V G LA RA RN LP RP R Q P \<or> (G n1) = (G n2)\<close> 
(is \<open>?L1 \<longleftrightarrow> ?R1 \<or> ?R2\<close>)
proof-
  have \<open>?L1 \<longleftrightarrow> (
    (\<forall> (n,p) \<in> set Q. semantics RE V G (G n) p) \<and> 
    (\<forall> (n1,n2) \<in> set LP. RE (G n1) (G n2)) \<and>
    (\<forall> (n,a) \<in> set LA. V (G n) a)
  ) \<longrightarrow> (
    (\<exists> (n,p) \<in> set P. semantics RE V G (G n) p) \<or>
    (\<exists> (n1,u,p) \<in> set R. 
      (\<exists> w. RE (G n1) w \<and> semantics RE V G w p)) \<or>
    (\<exists> (n1,n2) \<in> set RP. RE (G n1) (G n2)) \<or>
    (\<exists> (n1,n2) \<in> set ((n1,n2) # RN). (G n1) = (G n2)) \<or>
    (\<exists> (n,a) \<in> set RA. V (G n) a)
  )\<close> (is \<open>?L1 \<longleftrightarrow> (?L2 \<longrightarrow> ?Q1 \<or> ?Q2 \<or> ?Q3 \<or> ?EXRP \<or> ?R3)\<close>)
    by (simp add: sc_def)
  then have \<open>?L1 \<longleftrightarrow> (?L2 \<longrightarrow> ?Q1 \<or> ?Q2 \<or> ?Q3 \<or> ?R3) \<or> ?EXRP\<close>
    by meson
  moreover have \<open>
    ?EXRP = ((\<exists> (n1,n2) \<in> set RN. (G n1) = (G n2)) \<or> ?R2)\<close> 
    (is \<open>?EXP = (?R4 \<or> ?R2)\<close>) 
    using exi_pop by (smt (verit) case_prod_conv) 
  moreover have \<open>?R1 = (?L2 \<longrightarrow> ?Q1 \<or> ?Q2 \<or> ?Q3 \<or> ?R4 \<or> ?R3)\<close> 
    by (simp add: sc_def)
  ultimately show ?thesis 
    by meson 
qed

lemma sc_pop_RA:\<open>
  sc RE V G LA ((n,a) # RA) RN LP RP R Q P \<longleftrightarrow> 
    sc RE V G LA RA RN LP RP R Q P \<or> V (G n) a\<close> 
(is \<open>?L1 \<longleftrightarrow> ?R1 \<or> ?R2\<close>)
proof-
  have \<open>?L1 \<longleftrightarrow> (
    (\<forall> (n,p) \<in> set Q. semantics RE V G (G n) p) \<and> 
    (\<forall> (n1,n2) \<in> set LP. RE (G n1) (G n2)) \<and>
    (\<forall> (n,a) \<in> set LA. V (G n) a)
  ) \<longrightarrow> (
    (\<exists> (n,p) \<in> set P. semantics RE V G (G n) p) \<or>
    (\<exists> (n1,u,p) \<in> set R. 
      (\<exists> w. RE (G n1) w \<and> semantics RE V G w p)) \<or>
    (\<exists> (n1,n2) \<in> set RP. RE (G n1) (G n2)) \<or>
    (\<exists> (n1,n2) \<in> set RN. (G n1) = (G n2)) \<or>
    (\<exists> (n,a) \<in> set ((n,a) # RA). V (G n) a)
  )\<close> (is \<open>?L1 \<longleftrightarrow> (?L2 \<longrightarrow> ?Q1 \<or> ?Q2 \<or> ?Q3 \<or> ?Q4 \<or> ?EXRP)\<close>)
    by (simp add: sc_def)
  then have \<open>?L1 \<longleftrightarrow> (?L2 \<longrightarrow> ?Q1 \<or> ?Q2 \<or> ?Q3 \<or> ?Q4) \<or> ?EXRP\<close>
    by meson
  moreover have \<open>
    ?EXRP = ((\<exists> (n,a) \<in> set RA. V (G n) a) \<or> ?R2)\<close> 
    (is \<open>?EXP = (?R4 \<or> ?R2)\<close>) 
    using exi_pop by (smt (verit) case_prod_conv) 
  moreover have \<open>?R1 = (?L2 \<longrightarrow> ?Q1 \<or> ?Q2 \<or> ?Q3 \<or> ?Q4\<or> ?R4)\<close> 
    by (simp add: sc_def)
  ultimately show ?thesis 
    by meson 
qed

lemma sc_pop_Q:\<open>
  sc RE V G LA RA RN LP RP R ((n,p) # Q) P \<longleftrightarrow> 
    (semantics RE V G (G n) p \<longrightarrow> sc RE V G LA RA RN LP RP R Q P)\<close> 
(is \<open>?L1 \<longleftrightarrow> (?L2 \<longrightarrow> ?R1)\<close>)
proof-
  have \<open>?L1 \<longleftrightarrow> (
    (\<forall> (n,p) \<in> set ((n,p) # Q). semantics RE V G (G n) p) \<and> 
    (\<forall> (n1,n2) \<in> set LP. RE (G n1) (G n2)) \<and>
    (\<forall> (n,a) \<in> set LA. V (G n) a)
  ) \<longrightarrow> (
    (\<exists> (n,p) \<in> set P. semantics RE V G (G n) p) \<or>
    (\<exists> (n1,u,p) \<in> set R. 
      (\<exists> w. RE (G n1) w \<and> semantics RE V G w p)) \<or>
    (\<exists> (n1,n2) \<in> set RP. RE (G n1) (G n2)) \<or>
    (\<exists> (n1,n2) \<in> set RN. (G n1) = (G n2)) \<or>
    (\<exists> (n,a) \<in> set RA. V (G n) a)
  )\<close> (is \<open>?L1 \<longleftrightarrow> (?FAQ \<and> ?L3 \<longrightarrow> ?R2)\<close>)
    by (simp add: sc_def)
  then have \<open>?L1 \<longleftrightarrow> (?FAQ \<longrightarrow> (?L3 \<longrightarrow> ?R2))\<close>
    by meson
  moreover have \<open>
    ?FAQ = ((\<forall> (n,p) \<in> set Q. semantics RE V G (G n) p) \<and> ?L2)\<close> 
    (is \<open>?FAQ = (?L4 \<and> ?L2)\<close>) 
    using fa_pop  by (smt (verit, ccfv_threshold) Pair_inject case_prodD case_prodI2)
  moreover have \<open>?R1 = (?L4 \<and> ?L3 \<longrightarrow> ?R2)\<close>
    by (simp add: sc_def)
  ultimately show ?thesis 
    by meson 
qed

lemma sc_pop_LP:\<open>
  sc RE V G LA RA RN ((n1,n2) # LP) RP R Q P \<longleftrightarrow> 
    (RE (G n1) (G n2) \<longrightarrow> sc RE V G LA RA RN LP RP R Q P)\<close> 
(is \<open>?L1 \<longleftrightarrow> (?L2 \<longrightarrow> ?R1)\<close>)
proof-
  have \<open>?L1 \<longleftrightarrow> (
    (\<forall> (n,p) \<in> set Q. semantics RE V G (G n) p) \<and> 
    (\<forall> (n1,n2) \<in> set ((n1,n2) # LP). RE (G n1) (G n2)) \<and>
    (\<forall> (n,a) \<in> set LA. V (G n) a)
  ) \<longrightarrow> (
    (\<exists> (n,p) \<in> set P. semantics RE V G (G n) p) \<or>
    (\<exists> (n1,u,p) \<in> set R. 
      (\<exists> w. RE (G n1) w \<and> semantics RE V G w p)) \<or>
    (\<exists> (n1,n2) \<in> set RP. RE (G n1) (G n2)) \<or>
    (\<exists> (n1,n2) \<in> set RN. (G n1) = (G n2)) \<or>
    (\<exists> (n,a) \<in> set RA. V (G n) a)
  )\<close> (is \<open>?L1 \<longleftrightarrow> (?Q1 \<and> ?FALP \<and> ?L3 \<longrightarrow> ?R2)\<close>)
    by (simp add: sc_def)
  then have \<open>?L1 \<longleftrightarrow> (?FALP \<longrightarrow> (?Q1 \<and> ?L3 \<longrightarrow> ?R2))\<close>
    by meson
  moreover have \<open>
    ?FALP = ((\<forall> (n1,n2) \<in> set LP. RE (G n1) (G n2)) \<and> ?L2)\<close> 
    (is \<open>?FAQ = (?L4 \<and> ?L2)\<close>) 
    using fa_pop  by (smt (verit, ccfv_threshold) Pair_inject case_prodD case_prodI2)
  moreover have \<open>?R1 = (?Q1 \<and> ?L4 \<and> ?L3 \<longrightarrow> ?R2)\<close>
    by (simp add: sc_def)
  ultimately show ?thesis 
    by meson 
qed

lemma sc_pop_LA:\<open>
  sc RE V G ((n,a) # LA) RA RN LP RP R Q P \<longleftrightarrow> 
    (V (G n) a \<longrightarrow> sc RE V G LA RA RN LP RP R Q P)\<close> 
(is \<open>?L1 \<longleftrightarrow> (?L2 \<longrightarrow> ?R1)\<close>)
proof-
  have \<open>?L1 \<longleftrightarrow> (
    (\<forall> (n,p) \<in> set Q. semantics RE V G (G n) p) \<and> 
    (\<forall> (n1,n2) \<in> set LP. RE (G n1) (G n2)) \<and>
    (\<forall> (n,a) \<in> set ((n,a) # LA). V (G n) a)
  ) \<longrightarrow> (
    (\<exists> (n,p) \<in> set P. semantics RE V G (G n) p) \<or>
    (\<exists> (n1,u,p) \<in> set R. 
      (\<exists> w. RE (G n1) w \<and> semantics RE V G w p)) \<or>
    (\<exists> (n1,n2) \<in> set RP. RE (G n1) (G n2)) \<or>
    (\<exists> (n1,n2) \<in> set RN. (G n1) = (G n2)) \<or>
    (\<exists> (n,a) \<in> set RA. V (G n) a)
  )\<close> (is \<open>?L1 \<longleftrightarrow> (?Q1 \<and> ?Q2 \<and> ?FALP \<longrightarrow> ?R2)\<close>)
    by (simp add: sc_def)
  then have \<open>?L1 \<longleftrightarrow> (?FALP \<longrightarrow> (?Q1 \<and> ?Q2 \<longrightarrow> ?R2))\<close>
    by meson
  moreover have \<open>
    ?FALP = ((\<forall> (n,a) \<in> set LA. V (G n) a) \<and> ?L2)\<close> 
    (is \<open>?FAQ = (?L4 \<and> ?L2)\<close>) 
    using fa_pop  by (smt (verit, ccfv_threshold) Pair_inject case_prodD case_prodI2)
  moreover have \<open>?R1 = (?Q1 \<and> ?Q2 \<and> ?L4 \<longrightarrow> ?R2)\<close>
    by (simp add: sc_def)
  ultimately show ?thesis 
    by meson 
qed

definition consistent where \<open>
  consistent LA RA RN LP RP R Q P (T :: 'a itself) \<equiv> 
    (\<forall> (n,ns,p) \<in> set R. \<forall> m \<in> set ns. \<not>(
      \<forall> RE (V :: 'a \<Rightarrow> 'b \<Rightarrow> bool) G. sc RE V G LA RA RN LP ((n,m) # RP) R Q ((m,p) # P)))\<close>
(*/truth-definitions*)

(*soundness*)

lemma P_Pro:
  \<open>sc RE V G LA RA RN LP RP R Q ((n, PRO a) # P) \<longleftrightarrow> sc RE V G LA ((n, a) # RA) RN LP RP R Q P\<close>
proof-
  have \<open>
    sc RE V G LA RA RN LP RP R Q ((n, PRO a) # P) \<longleftrightarrow> 
      sc RE V G LA RA RN LP RP R Q P \<or> semantics RE V G (G n) (Pro a)\<close> 
    by (simp add: sc_pop_P)
  moreover have \<open>
    sc RE V G LA ((n, a) # RA) RN LP RP R Q P \<longleftrightarrow>
      sc RE V G LA RA RN LP RP R Q P \<or> V (G n) a\<close> 
    by (simp add: sc_pop_RA)
  ultimately show ?thesis 
    by simp
qed

lemma P_Pro_cons: \<open>
  consistent LA RA RN LP RP R Q ((n, PRO a) # P) (T :: 'a itself) \<Longrightarrow>
  consistent LA ((n, a) # RA) RN LP RP R Q P T\<close> (is \<open>?L \<Longrightarrow> ?R\<close>)
proof-
  assume l: ?L
  have \<open>\<forall> n' m p RE (V :: 'a \<Rightarrow> 'b \<Rightarrow> bool) G.
    (sc RE V G LA RA RN LP ((n', m) # RP) R Q ((m, p) # (n, PRO a) # P)) \<longleftrightarrow>
    (sc RE V G LA ((n, a) # RA) RN LP ((n', m) # RP) R Q ((m, p) # P))\<close> 
    by (meson P_Pro sc_pop_P)
  then show ?R 
    by (smt (z3) case_prodD case_prodI2 l consistent_def)
qed

lemma P_Nom: \<open>
  sc RE V G LA RA RN LP RP R Q ((n1, NOM n2) # P) \<longleftrightarrow> 
    sc RE V G LA RA ((n1,n2) # RN) LP RP R Q P\<close>
proof-
  have \<open>
    sc RE V G LA RA RN LP RP R Q ((n1, NOM n2) # P) \<longleftrightarrow> 
      sc RE V G LA RA RN LP RP R Q P \<or> semantics RE V G (G n1) (Nom n2)\<close> 
    by (simp add: sc_pop_P)
  moreover have \<open>
    sc RE V G LA RA ((n1,n2) # RN) LP RP R Q P \<longleftrightarrow>
      sc RE V G LA RA RN LP RP R Q P \<or> (G n1) = (G n2)\<close> 
    by (simp add: sc_pop_RN)
  ultimately show ?thesis 
    by auto 
qed

lemma P_Nom_cons: \<open>
  consistent LA RA RN LP RP R Q ((na, NOM nb) # P) (T :: 'a itself) \<Longrightarrow>
  consistent LA RA ((na, nb) # RN) LP RP R Q P T\<close> (is \<open>?L \<Longrightarrow> ?R\<close>)
proof-
  assume l: ?L
  have \<open>\<forall> n' m p RE (V :: 'a \<Rightarrow> 'b \<Rightarrow> bool) G.
    (sc RE V G LA RA RN LP ((n', m) # RP) R Q ((m, p) # (na, NOM nb) # P)) \<longleftrightarrow>
    (sc RE V G LA RA ((na, nb) # RN) LP ((n', m) # RP) R Q ((m, p) # P))\<close> 
    by (meson P_Nom sc_pop_P)
  then show ?R 
    by (smt (z3) case_prodD case_prodI2 l consistent_def)
qed

lemma P_Neg: \<open>
  sc RE V G LA RA RN LP RP R Q ((n, NOT p) # P) \<longleftrightarrow> 
    sc RE V G LA RA RN LP RP R ((n,p) # Q) P\<close>
proof-
  have \<open>
    sc RE V G LA RA RN LP RP R Q ((n, NOT p) # P) \<longleftrightarrow> 
      sc RE V G LA RA RN LP RP R Q P \<or> semantics RE V G (G n) (NOT p)\<close> 
    by (simp add: sc_pop_P)
  moreover have \<open>
    sc RE V G LA RA RN LP RP R ((n,p) # Q) P \<longleftrightarrow>
      (semantics RE V G (G n) p \<longrightarrow> sc RE V G LA RA RN LP RP R Q P)\<close> 
    by (simp add: sc_pop_Q)
  ultimately show ?thesis 
    by auto 
qed

lemma P_Neg_cons: \<open>
  consistent LA RA RN LP RP R Q ((n, NOT p) # P) (T :: 'a itself) \<Longrightarrow>
  consistent LA RA RN LP RP R ((n,p) # Q) P T\<close> (is \<open>?L \<Longrightarrow> ?R\<close>)
proof-
  assume l: ?L
  have \<open>\<forall> n' m p RE (V :: 'a \<Rightarrow> 'b \<Rightarrow> bool) G.
    (sc RE V G LA RA RN LP ((n', m) # RP) R Q ((m, p) # ((n, NOT p) # P))) \<longleftrightarrow>
    (sc RE V G LA RA RN LP ((n', m) # RP) R ((n,p) # Q) ((m, p) # P))\<close> 
    by (meson P_Neg sc_pop_P)
  then show ?R 
    by (smt (z3) P_Neg case_prodD case_prodI2 l sc_pop_P consistent_def)
qed

lemma P_Con: \<open>
  sc RE V G LA RA RN LP RP R Q ((n, p1 AND p2) # P) \<longleftrightarrow> 
    sc RE V G LA RA RN LP RP R Q ((n, p1) # P) \<and> 
    sc RE V G LA RA RN LP RP R Q ((n, p2) # P)\<close>
proof-
  have \<open>
    sc RE V G LA RA RN LP RP R Q ((n, p1 AND p2) # P) \<longleftrightarrow> 
      sc RE V G LA RA RN LP RP R Q P \<or> semantics RE V G (G n) (p1 AND p2)\<close> 
    by (simp add: sc_pop_P)
  moreover have \<open>
    sc RE V G LA RA RN LP RP R Q ((n, p1) # P) \<longleftrightarrow>
      (sc RE V G LA RA RN LP RP R Q P \<or> semantics RE V G (G n) p1)\<close> 
    by (simp add: sc_pop_P)
  moreover have \<open>
    sc RE V G LA RA RN LP RP R Q ((n, p2) # P) \<longleftrightarrow>
      (sc RE V G LA RA RN LP RP R Q P \<or> semantics RE V G (G n) p2)\<close> 
    by (simp add: sc_pop_P)
  ultimately show ?thesis 
    by auto 
qed
(*
lemma P_Con_cons: \<open>
  (\<forall> RE (V :: 'a \<Rightarrow> 'b \<Rightarrow> bool) G. sc RE V G LA RA RN LP RP R Q ((n, p1 AND p2) # P)) \<Longrightarrow>
  consistent LA RA RN LP RP R Q ((n, p1 AND p2) # P) (T :: 'a itself) \<Longrightarrow>
  consistent LA RA RN LP RP R Q ((n, p1) # P) T \<and>
  consistent LA RA RN LP RP R Q ((n, p2) # P) T\<close> (is \<open>?L1 \<Longrightarrow> ?L2 \<Longrightarrow> ?R\<close>) 
proof-
  assume l1: ?L1
  assume l2: ?L2
  have \<open>consistent LA RA RN LP RP R Q ((n, p1) # P) T\<close>
  proof (rule ccontr)
    assume a1:\<open>\<not>consistent LA RA RN LP RP R Q ((n, p1) # P) T\<close>
    then obtain n' ns p m where 
      \<open>(n',ns,p) \<in> set R \<and> m \<in> set ns \<and> 
      (\<forall> RE (V :: 'a \<Rightarrow> 'b \<Rightarrow> bool) G. 
        sc RE V G LA RA RN LP ((n',m) # RP) R Q ((m,p) # (n, p1) # P))\<close> 
      using consistent_def by blast

  have 1:\<open>\<forall> n' m p RE (V :: 'a \<Rightarrow> 'b \<Rightarrow> bool) G.
    sc RE V G LA RA RN LP ((n', m) # RP) R Q ((m, p) # (n, p1 AND p2) # P) \<longleftrightarrow>
    sc RE V G LA RA RN LP ((n', m) # RP) R Q ((n,p1) # (m, p) # P) \<and>
    sc RE V G LA RA RN LP ((n', m) # RP) R Q ((n,p2) # (m, p) # P)\<close> 
    by (smt (z3) P_Con sc_pop_P)
  have \<open>
    (\<forall> (n',ns,p) \<in> set R. \<forall> m \<in> set ns. \<not>(
    \<forall> RE (V :: 'a \<Rightarrow> 'b \<Rightarrow> bool) G. sc RE V G LA RA RN LP ((n',m) # RP) R Q ((m,p) # (n, p1) # P)))\<close> 
  proof (safe)
    fix n' ns p m
    assume \<open>(n',ns,p) \<in> set R\<close>
    assume \<open>m \<in> set ns\<close>
    assume \<open>\<forall> RE (V :: 'a \<Rightarrow> 'b \<Rightarrow> bool) G. 
      sc RE V G LA RA RN LP ((n',m) # RP) R Q ((m,p) # (n, p1) # P)\<close>
    show False sorry
  qed
  moreover have \<open>
    (\<forall> (n',ns,p) \<in> set R. \<forall> m \<in> set ns. \<not>(
    \<forall> RE (V :: 'a \<Rightarrow> 'b \<Rightarrow> bool) G. sc RE V G LA RA RN LP ((n',m) # RP) R Q ((m,p) # (n, p2) # P)))\<close> sorry
  ultimately show ?R 
    by (simp add: consistent_def)
qed*)

lemma P_Sat: \<open>
  sc RE V G LA RA RN LP RP R Q ((n1, AT n2 p) # P) \<longleftrightarrow> 
    sc RE V G LA RA RN LP RP R Q ((n2, p) # P)\<close>
proof-
  have \<open>
    sc RE V G LA RA RN LP RP R Q ((n1, AT n2 p) # P) \<longleftrightarrow> 
      sc RE V G LA RA RN LP RP R Q P \<or> semantics RE V G (G n1) (AT n2 p)\<close> 
    by (simp add: sc_pop_P)
  moreover have \<open>
    sc RE V G LA RA RN LP RP R Q ((n2, p) # P) \<longleftrightarrow>
      (sc RE V G LA RA RN LP RP R Q P \<or> semantics RE V G (G n2) p)\<close> 
    by (simp add: sc_pop_P)
  ultimately show ?thesis 
    by auto 
qed

lemma P_Pos: \<open>
  sc RE V G LA RA RN LP RP R Q ((n, Pos p) # P) \<longleftrightarrow> 
    sc RE V G LA RA RN LP RP ((n,[],p) # R) Q P\<close>
proof-
  have \<open>
    sc RE V G LA RA RN LP RP R Q ((n, Pos p) # P) \<longleftrightarrow> 
      sc RE V G LA RA RN LP RP R Q P \<or> semantics RE V G (G n) (Pos p)\<close> 
    by (simp add: sc_pop_P)
  moreover have \<open>
    sc RE V G LA RA RN LP RP ((n,[],p) # R) Q P \<longleftrightarrow>
      (sc RE V G LA RA RN LP RP R Q P \<or> (\<exists> w'. RE (G n) w' \<and> semantics RE V G w' p))\<close> 
    by (simp add: sc_pop_R)
  ultimately show ?thesis 
    by auto 
qed

lemma Q_Pro : \<open>
  sc RE V G LA RA RN LP RP R ((n, PRO a) # Q) [] \<longleftrightarrow> 
  sc RE V G ((n, a) # LA) RA RN LP RP R Q []\<close>
proof-
  have \<open>
    sc RE V G LA RA RN LP RP R ((n, PRO a) # Q) [] \<longleftrightarrow> 
      (semantics RE V G (G n) (Pro a) \<longrightarrow> sc RE V G LA RA RN LP RP R Q [])\<close> 
    by (simp add: sc_pop_Q)
  moreover have \<open>
    sc RE V G ((n, a) # LA) RA RN LP RP R Q [] \<longleftrightarrow>
      (V (G n) a \<longrightarrow> sc RE V G LA RA RN LP RP R Q [])\<close> 
    by (simp add: sc_pop_LA)
  ultimately show ?thesis 
    by auto
qed

lemma merge_G_eq_semantics_1: \<open>G n1 = G n2 \<Longrightarrow> mergeP p' n1 n2 = p \<Longrightarrow> 
  semantics RE V G w p = semantics RE V G w p'\<close>
proof (induct p' arbitrary: p w)
  case (Sat n p')
  show ?case 
    using Sat.hyps Sat.prems(1) Sat.prems(2) by force
qed auto

lemma merge_G_eq_1: \<open>
  G n1 = G n2 \<Longrightarrow> 
    sc RE V G (mergeNA LA n1 n2) (mergeNA RA n1 n2) (mergeNN RN n1 n2) (mergeNN LP n1 n2) 
        (mergeNN RP n1 n2) (mergeNSNP R n1 n2) (mergeNP Q n1 n2) [] \<Longrightarrow> 
      sc RE V G LA RA RN LP RP R Q []\<close> (is \<open>?L1 \<Longrightarrow> ?L2 \<Longrightarrow> ?R\<close>) 
proof-
  assume l1:?L1
  assume l2:?L2
  have \<open>
    (
      (\<forall> (n,p) \<in> set Q. semantics RE V G (G n) p) \<and> 
      (\<forall> (n1,n2) \<in> set LP. RE (G n1) (G n2)) \<and>
      (\<forall> (n,a) \<in> set LA. V (G n) a)
    ) \<longrightarrow> (
      (\<exists> (n,u,p) \<in> set R. 
        (\<exists> w. RE (G n) w \<and> semantics RE V G w p)) \<or>
      (\<exists> (n1,n2) \<in> set RP. RE (G n1) (G n2)) \<or>
      (\<exists> (n1,n2) \<in> set RN. (G n1) = (G n2)) \<or>
      (\<exists> (n,a) \<in> set RA. V (G n) a)
    )\<close>(is \<open>?RL \<longrightarrow> ?RR\<close>)
  proof
    assume 1:?RL
    have 2:\<open>
      (\<forall> (n,p) \<in> set (mergeNP Q n1 n2). semantics RE V G (G n) p) \<and> 
      (\<forall> (n1,n2) \<in> set (mergeNN LP n1 n2). RE (G n1) (G n2)) \<and>
      (\<forall> (n,a) \<in> set (mergeNA LA n1 n2). V (G n) a)\<close> 
      (is \<open>?mrg1 \<and> ?mrg2 \<and> ?mrg3\<close>)
    proof-
      have \<open>?mrg1\<close> 
      proof (safe)
        fix n p
        assume \<open>(n,p) \<in> set (mergeNP Q n1 n2)\<close>
        then obtain n' p' where \<open>(n',p') \<in> set Q \<and> (if n' = n1 then n = n2 else n = n')  \<and>
          mergeP p' n1 n2 = p\<close> 
          using merge_NP_exi_1 by blast
        moreover have \<open>semantics RE V G (G n') p'\<close> 
          using "1" calculation by fastforce
        ultimately show \<open>semantics RE V G (G n) p\<close> 
          by (metis l1 merge_G_eq_semantics_1)
      qed
      moreover have \<open>?mrg2\<close>
      proof (safe) 
        fix na nb
        assume \<open>(na,nb) \<in> set (mergeNN LP n1 n2)\<close>
        then obtain na' nb' where \<open>(na',nb') \<in> set LP \<and> (if na' = n1 then na = n2 else na = na') \<and>
          (if nb' = n1 then nb = n2 else nb = nb')\<close> 
          using merge_NN_exi_1 by (smt (z3) case_prodE)
        moreover have \<open>RE (G na') (G nb')\<close> 
          using "1" calculation by fastforce
        ultimately show \<open>RE (G na) (G nb)\<close> 
          by (metis l1)
      qed
      moreover have \<open>?mrg3\<close>
      proof (safe)
        fix n a
        assume \<open>(n,a) \<in> set (mergeNA LA n1 n2)\<close>
        then obtain n' a' where \<open>(n',a') \<in> set LA \<and> (if n' = n1 then n = n2 else n = n') \<and> a' = a\<close> 
          using merge_NA_exi_1 by (smt (z3) case_prodE)
        moreover have \<open>V (G n') a'\<close> 
          using "1" calculation by fastforce
        ultimately show \<open>V (G n) a\<close> 
          by (metis l1)
      qed
      ultimately show ?thesis 
        by simp
    qed
    then have \<open>
      (\<exists> (n,u,p) \<in> set (mergeNSNP R n1 n2). 
        (\<exists> w. RE (G n) w \<and> semantics RE V G w p)) \<or>
      (\<exists> (n1,n2) \<in> set (mergeNN RP n1 n2). RE (G n1) (G n2)) \<or>
      (\<exists> (n1,n2) \<in> set (mergeNN RN n1 n2). (G n1) = (G n2)) \<or>
      (\<exists> (n,a) \<in> set (mergeNA RA n1 n2). V (G n) a)\<close> (is \<open>?mrg4 \<or> ?mrg5 \<or> ?mrg6 \<or> ?mrg7\<close>)
      using l2 by (auto simp add: sc_def)
    then consider "?mrg4" | "?mrg5" | "?mrg6" | "?mrg7" 
      by blast
    then show ?RR 
    proof cases
      case 1
      then obtain n u p w where nup_def:
        "(n,u,p) \<in> set (mergeNSNP R n1 n2) \<and> (RE (G n) w \<and> semantics RE V G w p)" 
        by auto
      then obtain n' u' p' where nup'_def:
        \<open>(n',u',p') \<in> set R \<and> (if n' = n1 then n = n2 else n = n') \<and> mergeNS u' n1 n2 = u \<and>
          mergeP p' n1 n2 = p\<close> 
        using merge_NSNP_exi_1 by blast
      then have G_eq:\<open>G n' = G n\<close>
        using l1 by metis
      moreover have \<open>semantics RE V G w p = semantics RE V G w p'\<close> 
        by (metis l1 merge_G_eq_semantics_1 nup'_def)
      ultimately have \<open>
        RE (G n') w \<and> semantics RE V G w p'\<close> 
        using nup_def by auto
      then show ?thesis
        using nup'_def nup_def old.prod.case by blast
    next
      case 2
      then obtain na nb where nn_def:
        "(na,nb) \<in> set (mergeNN RP n1 n2) \<and> (RE (G na) (G nb))" 
        by auto
      then obtain na' nb' where nn'_def:
        \<open>(na',nb') \<in> set RP \<and> (if na' = n1 then na = n2 else na = na') \<and>
          (if nb' = n1 then nb = n2 else nb = nb')\<close> 
        using merge_NN_exi_1 by (smt (z3) case_prodE)
      then have G_eq:\<open>G na' = G na \<and> G nb' = G nb\<close>
        using l1 by metis
      then show ?thesis
        using nn'_def nn_def by fastforce
    next
      case 3
      then show ?thesis 
        by (smt (z3) case_prodD case_prodE case_prodI2 l1 merge_NN_exi_1)
    next
      case 4
      then show ?thesis
        by (smt (z3) case_prodE case_prod_conv l1 merge_NA_exi_1)
    qed
  qed
  then show ?R 
    by (simp add: sc_def)
qed

lemma merge_G_eq_2: \<open>
  G n1 = G n2 \<Longrightarrow> sc RE V G LA RA RN LP RP R Q [] \<Longrightarrow> 
    sc RE V G (mergeNA LA n1 n2) (mergeNA RA n1 n2) (mergeNN RN n1 n2) (mergeNN LP n1 n2) 
      (mergeNN RP n1 n2) (mergeNSNP R n1 n2) (mergeNP Q n1 n2) []\<close> (is \<open>?L1 \<Longrightarrow> ?L2 \<Longrightarrow> ?R1\<close>) 
proof-
  assume l1:?L1
  assume l2:?L2 
  have \<open>
    (\<forall> (n,p) \<in> set (mergeNP Q n1 n2). semantics RE V G (G n) p) \<and> 
    (\<forall> (n1,n2) \<in> set (mergeNN LP n1 n2). RE (G n1) (G n2)) \<and>
    (\<forall> (n,a) \<in> set (mergeNA LA n1 n2). V (G n) a) \<Longrightarrow>
    (\<exists> (n,u,p) \<in> set (mergeNSNP R n1 n2). 
      (\<exists> w. RE (G n) w \<and> semantics RE V G w p)) \<or>
    (\<exists> (n1,n2) \<in> set (mergeNN RP n1 n2). RE (G n1) (G n2)) \<or>
    (\<exists> (n1,n2) \<in> set (mergeNN RN n1 n2). (G n1) = (G n2)) \<or>
    (\<exists> (n,a) \<in> set (mergeNA RA n1 n2). V (G n) a)\<close> (is "?L3 \<Longrightarrow> ?R2")
  proof-
    assume l3:\<open>?L3\<close>
    have \<open>
      (\<forall> (n,p) \<in> set Q. semantics RE V G (G n) p) \<and> 
      (\<forall> (n1,n2) \<in> set LP. RE (G n1) (G n2)) \<and>
      (\<forall> (n,a) \<in> set LA. V (G n) a)\<close> (is \<open>?Q \<and> ?LP \<and> ?LA\<close>)
    proof -
      have ?Q
      proof (safe)
        fix n p
        assume \<open>(n,p) \<in> set Q\<close>
        then obtain n' p' where np_def:\<open>(n',p') \<in> set (mergeNP Q n1 n2) \<and> 
          (if n = n1 then n' = n2 else n = n') \<and> p' = mergeP p n1 n2\<close> 
          using merge_NP_exi_2 by force
        then have \<open>semantics RE V G (G n') p'\<close> 
          using l3 by fastforce
        then show \<open>semantics RE V G (G n) p\<close> 
          by (metis l1 merge_G_eq_semantics_1 np_def)
      qed
      moreover have ?LP
      proof (safe)
        fix na nb
        assume \<open>(na,nb) \<in> set LP\<close>
        then obtain na' nb' where na_def:\<open>(na',nb') \<in> set (mergeNN LP n1 n2) \<and> 
          (if na = n1 then na' = n2 else na = na') \<and> (if nb = n1 then nb' = n2 else nb = nb')\<close> 
          using merge_NN_exi_2 by fastforce
        then have \<open>RE (G na') (G nb')\<close> 
          using l3 by blast
        then show \<open>RE (G na) (G nb)\<close> 
          by (metis l1 na_def)
      qed
      moreover have ?LA
      proof (safe)
        fix n a
        assume \<open>(n,a) \<in> set LA\<close>
        then obtain n' a' where na_def:\<open>(n',a') \<in> set (mergeNA LA n1 n2) \<and> 
          (if n = n1 then n' = n2 else n = n') \<and> a = a'\<close>  
          using merge_NA_exi_2 by fastforce
        then show \<open>V (G n) a\<close>
          by (metis case_prod_conv l1 l3)
      qed
      ultimately show ?thesis 
        by blast
    qed
    then have \<open>
      (\<exists> (n,u,p) \<in> set R. 
        (\<exists> w. RE (G n) w \<and> semantics RE V G w p)) \<or>
      (\<exists> (n1,n2) \<in> set RP. RE (G n1) (G n2)) \<or>
      (\<exists> (n1,n2) \<in> set RN. (G n1) = (G n2)) \<or>
      (\<exists> (n,a) \<in> set RA. V (G n) a)\<close> (is \<open>?R \<or> ?RP \<or> ?RN \<or> ?RA\<close>)
      using l2 by (auto simp add: sc_def)
    then consider ?R | ?RP | ?RN | ?RA 
      by blast
    then show \<open>?R2\<close> 
    proof cases
      case 1
      then obtain n' u' p' w where nup_def:
        \<open>(n',u',p') \<in> set R \<and> RE (G n') w \<and> semantics RE V G w p'\<close> 
        by auto
      then obtain n u p where nup'_def: \<open>
        (n,u,p) \<in> set (mergeNSNP R n1 n2) \<and> (if n' = n1 then n = n2 else n = n') \<and> 
        mergeNS u' n1 n2 = u \<and> mergeP p' n1 n2 = p\<close> 
        using merge_NSNP_exi_2 by blast
      then have G_eq:\<open>G n' = G n\<close>
        using l1 by metis
      moreover have \<open>semantics RE V G w p = semantics RE V G w p'\<close> 
        by (metis l1 merge_G_eq_semantics_1 nup'_def)
      ultimately have \<open>RE (G n) w \<and> semantics RE V G w p\<close> 
        using nup_def by auto
      then show ?thesis 
        using nup_def nup'_def old.prod.case by fastforce
    next
      case 2
      then obtain na nb where nanb_def: \<open>(na,nb) \<in> set RP \<and> RE (G na) (G nb)\<close>
        by blast
      then obtain na' nb' where nanb'_def:\<open>(na',nb') \<in> set (mergeNN RP n1 n2) \<and> 
        (if na = n1 then na' = n2 else na = na') \<and> (if nb = n1 then nb' = n2 else nb = nb')\<close> 
        using merge_NN_exi_2 by fastforce
      then show ?thesis
        by (metis (no_types, lifting) case_prodI l1 nanb_def)
    next
      case 3
      then obtain na nb where nanb_def: \<open>(na,nb) \<in> set RN \<and> G na = G nb\<close>
        by blast
      then obtain na' nb' where nanb'_def:\<open>(na',nb') \<in> set (mergeNN RN n1 n2) \<and> 
        (if na = n1 then na' = n2 else na = na') \<and> (if nb = n1 then nb' = n2 else nb = nb')\<close> 
        using merge_NN_exi_2 by fastforce
      then show ?thesis 
        by (smt (verit, best) case_prodI l1 nanb_def)
    next
      case 4
      then obtain n a where na_def: \<open>(n,a) \<in> set RA \<and> V (G n) a\<close>
        by blast
      then obtain n' a' where na'_def:\<open>(n',a') \<in> set (mergeNA RA n1 n2) \<and> 
        (if n = n1 then n' = n2 else n = n') \<and> a' = a\<close> 
        using merge_NA_exi_2 by fastforce
      then show ?thesis 
        by (metis case_prodI l1 na_def)
    qed
  qed
  then show ?R1 
    by (simp add: sc_def)
qed

lemma agrees_merge_semantics: \<open>p = mergeP p' n1 n2 \<Longrightarrow> G' = agrees G n1 (G n2) \<Longrightarrow>
  semantics RE V G w p = semantics RE V G' w p\<close> 
proof (induct p' arbitrary: p w)
  case (Nom n)
  then show ?case 
    by (simp add: agrees_def)
next
  case (Sat n p')
  then show ?case 
      by (simp add: Sat.hyps Sat.prems(1) Sat.prems(2) agrees_def)
qed auto

lemma agrees_merge: \<open>G' = agrees G n1 (G n2) \<Longrightarrow> 
  sc RE V G' (mergeNA LA n1 n2) (mergeNA RA n1 n2) (mergeNN RN n1 n2) 
    (mergeNN LP n1 n2) (mergeNN RP n1 n2) (mergeNSNP R n1 n2) (mergeNP Q n1 n2) [] \<Longrightarrow>
  sc RE V G (mergeNA LA n1 n2) (mergeNA RA n1 n2) (mergeNN RN n1 n2) 
    (mergeNN LP n1 n2) (mergeNN RP n1 n2) (mergeNSNP R n1 n2) (mergeNP Q n1 n2) []\<close>
(is \<open>?L1 \<Longrightarrow> ?L2 \<Longrightarrow> ?R1\<close>)
proof-
  assume l1: ?L1
  assume l2: ?L2
  then have \<open>
    (\<forall> (n,p) \<in> set (mergeNP Q n1 n2). semantics RE V G (G n) p) \<and> 
    (\<forall> (n1,n2) \<in> set (mergeNN LP n1 n2). RE (G n1) (G n2)) \<and>
    (\<forall> (n,a) \<in> set (mergeNA LA n1 n2). V (G n) a) \<Longrightarrow>
    (\<exists> (n,u,p) \<in> set (mergeNSNP R n1 n2). 
        (\<exists> w. RE (G n) w \<and> semantics RE V G w p)) \<or>
    (\<exists> (n1,n2) \<in> set (mergeNN RP n1 n2). RE (G n1) (G n2)) \<or>
    (\<exists> (n1,n2) \<in> set (mergeNN RN n1 n2). (G n1) = (G n2)) \<or>
    (\<exists> (n,a) \<in> set (mergeNA RA n1 n2). V (G n) a)\<close> (is "?L3 \<Longrightarrow> ?R2")
  proof-
    assume l3: ?L3
    then have \<open>
      (\<forall> (n,p) \<in> set (mergeNP Q n1 n2). semantics RE V G' (G' n) p) \<and> 
      (\<forall> (n1,n2) \<in> set (mergeNN LP n1 n2). RE (G' n1) (G' n2)) \<and>
      (\<forall> (n,a) \<in> set (mergeNA LA n1 n2). V (G' n) a)\<close> (is \<open>?Q \<and> ?LP \<and> ?LA\<close>)
    proof-
      have ?Q
      proof (safe)
        fix n p
        assume a:\<open>(n,p) \<in> set (mergeNP Q n1 n2)\<close>
        have \<open>G n = G' n\<close> 
        proof cases
          assume \<open>n = n2\<close>
          then show ?thesis 
            by (simp add: agrees_def l1)
        next
          assume \<open>n \<noteq> n2\<close>
          then have \<open>n \<noteq> n1\<close> 
            by (smt (z3) a case_prodE merge_NP_exi_1)
          then show ?thesis 
            by (simp add: agrees_def l1)
        qed
        moreover have \<open>semantics RE V G (G n) p = semantics RE V G' (G n) p\<close> 
          by (smt (z3) a agrees_merge_semantics case_prodE l1 merge_NP_exi_1)
        ultimately show \<open>semantics RE V G' (G' n) p\<close>  
          by (metis a case_prodD l3)
      qed
      moreover have ?LP
      proof (safe)
        fix na nb
        assume a: \<open>(na,nb) \<in> set (mergeNN LP n1 n2)\<close>
        have \<open>G na = G' na\<close> 
        proof cases
          assume \<open>na = n2\<close>
          then show ?thesis 
            by (simp add: agrees_def l1)
        next
          assume \<open>na \<noteq> n2\<close>
          then have \<open>na \<noteq> n1\<close> 
            by (smt (z3) a case_prodE merge_NN_exi_1)
          then show ?thesis 
            by (simp add: agrees_def l1)
        qed
        moreover have \<open>G nb = G' nb\<close> 
        proof cases
          assume \<open>nb = n2\<close>
          then show ?thesis 
            by (simp add: agrees_def l1)
        next
          assume \<open>nb \<noteq> n2\<close>
          then have \<open>nb \<noteq> n1\<close> 
            by (smt (z3) a case_prodE merge_NN_exi_1)
          then show ?thesis 
            by (simp add: agrees_def l1)
        qed
        ultimately show \<open>RE (G' na) (G' nb)\<close> 
          by (metis a case_prodD l3)
      qed
      moreover have ?LA
      proof (safe)
        fix n a
        assume a:\<open>(n,a) \<in> set (mergeNA LA n1 n2)\<close>
        have \<open>G n = G' n\<close> 
        proof cases
          assume \<open>n = n2\<close>
          then show ?thesis 
            by (simp add: agrees_def l1)
        next
          assume \<open>n \<noteq> n2\<close>
          then have \<open>n \<noteq> n1\<close> 
            by (smt (z3) a case_prodE merge_NA_exi_1)
          then show ?thesis 
            by (simp add: agrees_def l1)
        qed
        then show \<open>V (G' n) a\<close>
          by (metis a case_prodD l3)
      qed
      ultimately show ?thesis 
        by blast
    qed
    then have \<open>
      (\<exists> (n,u,p) \<in> set (mergeNSNP R n1 n2). 
        (\<exists> w. RE (G' n) w \<and> semantics RE V G' w p)) \<or>
      (\<exists> (n1,n2) \<in> set (mergeNN RP n1 n2). RE (G' n1) (G' n2)) \<or>
      (\<exists> (n1,n2) \<in> set (mergeNN RN n1 n2). (G' n1) = (G' n2)) \<or>
      (\<exists> (n,a) \<in> set (mergeNA RA n1 n2). V (G' n) a)\<close> (is \<open>?R \<or> ?RP \<or> ?RN \<or> ?RA\<close>)
      using l2 by (auto simp add: sc_def)
    then consider ?R | ?RP | ?RN | ?RA 
      by blast
    then show \<open>?R2\<close> 
    proof cases
      case 1
      then obtain n u p w where nup_def:"
        (n,u,p) \<in> set (mergeNSNP R n1 n2) \<and> RE (G' n) w \<and> semantics RE V G' w p"
        by blast
      then obtain n' u' p' where nup'_def:
        \<open>(n',u',p') \<in> set R \<and> (if n' = n1 then n = n2 else n = n') \<and> u = mergeNS u' n1 n2 \<and>
        p = mergeP p' n1 n2\<close>
        by (smt (z3) case_prodE merge_NSNP_exi_1)
      have u_def: \<open>\<exists> u'. u = mergeNS u' n1 n2\<close> 
        using nup_def merge_NSNP_exi_1 case_prodE by fastforce
      moreover have \<open>RE (G n) w\<close> 
      proof-
        have \<open>n = n1 \<Longrightarrow> n1 = n2\<close> 
          by (smt (z3) case_prodE merge_NSNP_exi_1 nup_def)
        then have \<open>G n = G' n\<close>
          by (metis agrees_def l1)
        then show ?thesis 
          by (simp add: nup_def)
      qed
      moreover have \<open>semantics RE V G w p\<close> 
        by (smt (z3) nup_def agrees_merge_semantics case_prodE l1 merge_NSNP_exi_1)
      ultimately show ?thesis 
        using nup_def by blast
    next
      case 2
      obtain na nb where nanb_def: \<open>(na,nb) \<in> set (mergeNN RP n1 n2) \<and> RE (G' na) (G' nb)\<close> 
        using "2" by blast
      moreover have \<open>na = n1 \<Longrightarrow> n1 = n2\<close> 
        by (smt (z3) case_prodE merge_NN_exi_1 nanb_def)
      moreover have \<open>nb = n1 \<Longrightarrow> n1 = n2\<close> 
        by (smt (z3) case_prodE merge_NN_exi_1 nanb_def)
      ultimately show ?thesis 
        by (metis (no_types, lifting) agrees_def case_prodI l1)
    next
      case 3
      then obtain na nb where nanb_def: \<open>(na,nb) \<in> set (mergeNN RN n1 n2) \<and> G' na = G' nb\<close> 
        by blast
      moreover have \<open>na = n1 \<Longrightarrow> n1 = n2\<close> 
        by (smt (z3) case_prodE merge_NN_exi_1 nanb_def)
      moreover have \<open>nb = n1 \<Longrightarrow> n1 = n2\<close> 
        by (smt (z3) case_prodE merge_NN_exi_1 nanb_def)
      ultimately show ?thesis 
        by (metis (mono_tags, lifting) agrees_def case_prodI l1)
    next
      case 4
      then obtain n a where na_def: \<open>(n,a) \<in> set (mergeNA RA n1 n2) \<and> V (G' n) a\<close> 
        by blast
      moreover have \<open>n = n1 \<Longrightarrow> n1 = n2\<close> 
        by (smt (z3) case_prodE merge_NA_exi_1 na_def)
      ultimately show ?thesis 
        by (metis (mono_tags, lifting) agrees_def case_prodI l1)
    qed
  qed
  then show ?R1 
    by (simp add: sc_def)
qed

lemma Q_Nom: \<open>
  (\<forall> (RE :: 'a \<Rightarrow> 'a \<Rightarrow> bool) V G. sc RE V G LA RA RN LP RP R ((n1, NOM n2) # Q) []) \<longleftrightarrow> 
  (\<forall> (RE :: 'a \<Rightarrow> 'a \<Rightarrow> bool) V G. sc RE V G (mergeNA LA n1 n2) (mergeNA RA n1 n2) 
    (mergeNN RN n1 n2) (mergeNN LP n1 n2) (mergeNN RP n1 n2) 
    (mergeNSNP R n1 n2) (mergeNP Q n1 n2) [])\<close> 
(is "?L \<longleftrightarrow> ?R")
proof-
  let ?cre = \<open>\<lambda> RE V G. sc RE V G LA RA RN LP RP R Q []\<close>
  let ?nom = \<open>\<lambda> RE V G. sc RE V G LA RA RN LP RP R ((n1, NOM n2) # Q) []\<close>
  let ?mrg = \<open>\<lambda> RE V G. 
      sc RE V G (mergeNA LA n1 n2) (mergeNA RA n1 n2) (mergeNN RN n1 n2) (mergeNN LP n1 n2) 
        (mergeNN RP n1 n2) (mergeNSNP R n1 n2) (mergeNP Q n1 n2) []\<close> 
  have ldef:\<open>?L \<longleftrightarrow> (\<forall> (RE :: 'a \<Rightarrow> 'a \<Rightarrow> bool) V G. 
    semantics RE V G (G n1) (Nom n2) \<longrightarrow> ?cre RE V G)\<close> 
    by (simp add: sc_pop_Q) 
  moreover have \<open>\<forall>  (RE :: 'a \<Rightarrow> 'a \<Rightarrow> bool) V G. (G n1 = G n2 \<longrightarrow> ?mrg RE V G \<longrightarrow> ?cre RE V G)\<close> 
    by (meson merge_G_eq_1)
  ultimately have "?R \<longrightarrow> ?L" 
    by simp
  moreover have \<open>\<forall>  RE V G. (G n1 = G n2 \<longrightarrow> ?cre RE V G \<longrightarrow> ?mrg RE V G)\<close> 
    by (meson merge_G_eq_2)
  moreover have \<open>?L \<longrightarrow> ?R\<close>
  proof (rule ccontr)
    assume a:\<open>\<not>(?L \<longrightarrow> ?R)\<close>
    from a have l:\<open>?L\<close>
      by simp
    from a have r:\<open>\<not>?R\<close>
      by simp
    then obtain RE V G where counter_model:\<open>\<not>(?mrg  (RE :: 'a \<Rightarrow> 'a \<Rightarrow> bool) V G)\<close>
      by blast
    obtain G' where Gdef:\<open>G' = agrees G n1 (G n2)\<close>
      by simp
    then have \<open>?cre RE V G'\<close> 
      by (metis agrees_def l ldef semantics.simps(2))
    then have \<open>?mrg RE V G'\<close> 
      by (simp add: Gdef agrees_def merge_G_eq_2)
    then have \<open>?mrg RE V G\<close> 
      by (metis Gdef agrees_merge)
    then show False 
      using counter_model by blast
  qed
  ultimately show ?thesis 
    by auto
qed

lemma Q_Neg: \<open>
  sc RE V G LA RA RN LP RP R ((n, NOT p) # Q) [] \<longleftrightarrow> sc RE V G LA RA RN LP RP R Q [(n,p)]\<close>
proof-
  have \<open>
    sc RE V G LA RA RN LP RP R ((n, NOT p) # Q) [] \<longleftrightarrow> 
      (semantics RE V G (G n) (NOT p) \<longrightarrow> sc RE V G LA RA RN LP RP R Q [])\<close> 
    by (simp add: sc_pop_Q)
  moreover have \<open>
    sc RE V G LA RA RN LP RP R Q [(n,p)] \<longleftrightarrow>
      sc RE V G LA RA RN LP RP R Q [] \<or> semantics RE V G (G n) p\<close> 
    by (simp add: sc_pop_P)
  ultimately show ?thesis 
    by auto
qed

lemma Q_Con: \<open>
  sc RE V G LA RA RN LP RP R ((n, p1 AND p2) # Q) [] \<longleftrightarrow> 
  sc RE V G LA RA RN LP RP R ((n, p1) # (n, p2) # Q) []\<close>
proof-
  have \<open>
    sc RE V G LA RA RN LP RP R ((n, p1 AND p2) # Q) [] \<longleftrightarrow> 
      (semantics RE V G (G n) (p1 AND p2) \<longrightarrow> sc RE V G LA RA RN LP RP R Q [])\<close> 
    by (simp add: sc_pop_Q)
  moreover have \<open>
    sc RE V G LA RA RN LP RP R ((n, p1) # (n, p2) # Q) [] \<longleftrightarrow>
      (semantics RE V G (G n) p1 \<longrightarrow> semantics RE V G (G n) p2 \<longrightarrow> 
        sc RE V G LA RA RN LP RP R Q [])\<close> 
    by (simp add: sc_pop_Q)
  ultimately show ?thesis 
    by auto
qed

lemma Q_Sat: \<open>
  sc RE V G LA RA RN LP RP R ((n1, AT n2 p) # Q) [] \<longleftrightarrow> 
  sc RE V G LA RA RN LP RP R ((n2, p) # Q) []\<close>
proof-
  have \<open>
    sc RE V G LA RA RN LP RP R ((n1, AT n2 p) # Q) [] \<longleftrightarrow> 
      (semantics RE V G (G n1) (AT n2 p) \<longrightarrow> sc RE V G LA RA RN LP RP R Q [])\<close> 
    by (simp add: sc_pop_Q)
  moreover have \<open>
    sc RE V G LA RA RN LP RP R ((n2, p) # Q) [] \<longleftrightarrow>
      (semantics RE V G (G n2) p \<longrightarrow> sc RE V G LA RA RN LP RP R Q [])\<close> 
    by (simp add: sc_pop_Q)
  ultimately show ?thesis 
    by auto
qed

lemma semantics_fresh_agree: \<open>sub_set (nominalsForm p) ns \<Longrightarrow> 
  G' = agrees G (fresh ns) w \<Longrightarrow> semantics RE V G w p \<Longrightarrow> semantics RE V G' w p\<close> 
by (induct p) (metis agrees_semantics fresh_new member_sub_set)+

lemma sc_fresh_agree: \<open>
  G' = agrees G (fresh (ns_1 LA RA RN LP RP R ((n, \<diamond> p) # Q))) w \<Longrightarrow>
  sc RE V G' LA RA RN LP RP R Q [] \<Longrightarrow> sc RE V G LA RA RN LP RP R Q []\<close> (is \<open>?L1 \<Longrightarrow> ?L2 \<Longrightarrow> ?R1\<close>)
proof-
  let ?x = \<open>fresh (ns_1 LA RA RN LP RP R ((n, \<diamond> p) # Q))\<close>
  assume l1:?L1
  assume l2:?L2
  have \<open>(
      (\<forall> (n,p) \<in> set Q. semantics RE V G (G n) p) \<and> 
      (\<forall> (n1,n2) \<in> set LP. RE (G n1) (G n2)) \<and>
      (\<forall> (n,a) \<in> set LA. V (G n) a)
    ) \<Longrightarrow> (
      (\<exists> (n,u,p) \<in> set R. 
        (\<exists> w. RE (G n) w \<and> semantics RE V G w p)) \<or>
      (\<exists> (n1,n2) \<in> set RP. RE (G n1) (G n2)) \<or>
      (\<exists> (n1,n2) \<in> set RN. (G n1) = (G n2)) \<or>
      (\<exists> (n,a) \<in> set RA. V (G n) a)
    )\<close> (is \<open>?L3 \<Longrightarrow> ?R2\<close>)
  proof-
    assume l3:?L3
    have \<open>(
        (\<forall> (n,p) \<in> set Q. semantics RE V G' (G' n) p) \<and> 
        (\<forall> (n1,n2) \<in> set LP. RE (G' n1) (G' n2)) \<and>
        (\<forall> (n,a) \<in> set LA. V (G' n) a)
      )\<close> (is \<open>?Q \<and> ?LP \<and> ?LA\<close>)
    proof-
      have ?Q 
      proof safe
        fix n' p'
        assume Q_def: \<open>(n',p') \<in> set Q\<close>
        have G_eq: \<open>G n' = G' n'\<close> 
        proof-
          have \<open>member n' (nominalsNP Q)\<close> 
            using Q_def nomNP_member by auto
          then have \<open>member n' (nominalsNP ((n, \<diamond> p) # Q))\<close> 
            by (meson Q_def list.set_intros(2) nomNP_member)
          then have \<open>member n' (ns_1 LA RA RN LP RP R ((n, \<diamond> p) # Q))\<close> 
            by (metis union_member)
          then show ?thesis 
            by (smt (z3) agrees_def fresh_new l1)
        qed
        have p_sub: \<open>sub_set (nominalsForm p') (ns_1 LA RA RN LP RP R ((n, \<diamond> p) # Q))\<close> 
        proof-
          have \<open>sub_set (nominalsForm p') (nominalsNP Q)\<close>
            using Q_def nomNP_member by auto
          then have \<open>sub_set (nominalsForm p') (nominalsNP ((n, \<diamond> p) # Q))\<close> 
            by (meson Q_def list.set_intros(2) nomNP_member)
          then show ?thesis 
            by (metis (no_types, lifting) member_sub_set union_member)
        qed
        from Q_def have "semantics RE V G (G n') p'" 
          using l3 by fastforce
        then show \<open>semantics RE V G' (G' n') p'\<close> 
          using G_eq p_sub by (metis (full_types) agrees_semantics fresh_new l1 member_sub_set)
      qed
      moreover have ?LP 
        by (smt (z3) agrees_def case_prodD case_prodI2 fresh_new l1 l3 member_sub_set 
            nomNN_member sub_set_union1 sub_set_union2)
      moreover have ?LA 
        by (smt (z3) agrees_def case_prodD case_prodI2 fresh_new l1 l3 member_sub_set 
            nomNA_member sub_set_union1)
      ultimately show ?thesis
        by simp
    qed
    then have \<open>(
        (\<exists> (n,u,p) \<in> set R. 
          (\<exists> w. RE (G' n) w \<and> semantics RE V G' w p)) \<or>
        (\<exists> (n1,n2) \<in> set RP. RE (G' n1) (G' n2)) \<or>
        (\<exists> (n1,n2) \<in> set RN. (G' n1) = (G' n2)) \<or>
        (\<exists> (n,a) \<in> set RA. V (G' n) a)
      )\<close> (is \<open>?R \<or> ?RP \<or> ?RN \<or> ?RA\<close>)
      using l2 by (auto simp add: sc_def)
    then consider ?R | ?RP | ?RN | ?RA
      by blast
    then show ?R2 
    proof cases
      case 1
      then obtain n' u' p' w' where nup_def':
        \<open>(n',u',p') \<in> set R \<and> RE (G' n') w' \<and> semantics RE V G' w' p'\<close> 
        by auto
      have \<open>RE (G n') w' \<and> semantics RE V G w' p'\<close>  
      proof-
        have ndef: \<open>member n' (ns_1 LA RA RN LP RP R ((n, \<diamond> p) # Q))\<close> 
          by (meson member_sub_set nomNSNP_member nup_def' sub_set_union1 sub_set_union2)
        have udef: \<open>sub_set u' (ns_1 LA RA RN LP RP R ((n, \<diamond> p) # Q))\<close> 
          by (metis (no_types, lifting) member_sub_set nomNSNP_member nup_def' union_member)
        have pdef: \<open>sub_set (nominalsForm p') (ns_1 LA RA RN LP RP R ((n, \<diamond> p) # Q))\<close>
          by (metis (no_types, lifting) member_sub_set nomNSNP_member nup_def' union_member)
        moreover have \<open>RE (G n') w'\<close> 
          using ndef by (smt (verit, best) agrees_def fresh_new l1 nup_def')
        moreover have \<open>semantics RE V G w' p'\<close> 
          using pdef by (metis (no_types, lifting) agrees_semantics 
              fresh_new l1 member_sub_set nup_def')
        ultimately show ?thesis 
          by simp
      qed
      then show ?thesis 
        using nup_def' by fastforce
    next
      case 2
      obtain n1 n2 where n1n2_def:\<open>(n1,n2) \<in> set RP \<and> RE (G' n1) (G' n2)\<close> 
        using "2" by auto
      moreover have \<open>member n1 (ns_1 LA RA RN LP RP R ((n, \<diamond> p) # Q))\<close> 
        by (metis n1n2_def nomNN_member union_member)
      moreover have \<open>member n2 (ns_1 LA RA RN LP RP R ((n, \<diamond> p) # Q))\<close> 
        by (metis n1n2_def nomNN_member union_member)
      ultimately show ?thesis 
        by (smt (z3) agrees_def case_prodI fresh_new l1)
    next
      case 3
      obtain n1 n2 where n1n2_def:\<open>(n1,n2) \<in> set RN \<and> (G' n1) = (G' n2)\<close> 
        using "3" by auto
      moreover have \<open>member n1 (ns_1 LA RA RN LP RP R ((n, \<diamond> p) # Q))\<close> 
        by (metis n1n2_def nomNN_member union_member)
      moreover have \<open>member n2 (ns_1 LA RA RN LP RP R ((n, \<diamond> p) # Q))\<close> 
        by (metis n1n2_def nomNN_member union_member)
      ultimately show ?thesis 
        by (smt (z3) agrees_def case_prodI fresh_new l1)
    next
      case 4
      obtain n' a' where n1n2_def:\<open>(n',a') \<in> set RA \<and> V (G' n') a'\<close> 
        using "4" by auto
      moreover have \<open>member n' (ns_1 LA RA RN LP RP R ((n, \<diamond> p) # Q))\<close> 
        by (metis n1n2_def nomNA_member union_member)
      ultimately show ?thesis 
        by (smt (z3) agrees_def case_prodI fresh_new l1)
    qed
  qed

  then show ?R1 
    by (simp add: sc_def)
qed

lemma semantic_exi_iff_fresh: \<open>
  let x = fresh (ns_1 LA RA RN LP RP R ((n, \<diamond> p) # Q)) in 
  (\<forall> (RE :: 'a \<Rightarrow> 'a \<Rightarrow> bool) V G. (\<exists> v. (RE (G n) v) \<and> (semantics RE V G v p))
    \<longrightarrow> sc RE V G LA RA RN LP RP R Q []) \<longleftrightarrow> 
  (\<forall> (RE :: 'a \<Rightarrow> 'a \<Rightarrow> bool) V G. RE (G n) (G x) \<and> semantics RE V G (G x) p
    \<longrightarrow> sc RE V G LA RA RN LP RP R Q [])\<close>
proof-
  let ?x = "fresh (ns_1 LA RA RN LP RP R ((n, \<diamond> p) # Q))"
  have \<open>
    (\<forall>  (RE :: 'a \<Rightarrow> 'a \<Rightarrow> bool) V G. (\<exists> v. (RE (G n) v) \<and> (semantics RE V G v p))
      \<longrightarrow> sc RE V G LA RA RN LP RP R Q []) \<longleftrightarrow> 
    (\<forall>  (RE :: 'a \<Rightarrow> 'a \<Rightarrow> bool) V G. RE (G n) (G ?x) \<and> semantics RE V G (G ?x) p
      \<longrightarrow> sc RE V G LA RA RN LP RP R Q [])\<close> (is \<open>?L \<longleftrightarrow> ?R\<close>)
  proof
    assume l: ?L
    show ?R 
    proof (safe)
      fix RE :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
      fix V G
      assume a1:\<open>RE (G n) (G ?x)\<close>
      assume a2:\<open>semantics RE V G (G ?x) p\<close>
      show \<open>sc RE V G LA RA RN LP RP R Q []\<close> 
        using a1 a2 l by blast
    qed
  next
    assume r: ?R
    show ?L 
    proof (safe)
      fix RE :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
      fix V G w
      assume a1:\<open>RE (G n) w\<close>
      assume a2:\<open>semantics RE V G w p\<close>
      have sub:\<open>sub_set (nominalsForm p) (ns_1 LA RA RN LP RP R ((n, \<diamond> p) # Q))\<close> 
        by (metis (no_types, lifting) list.set_intros(1) member_sub_set nomNP_member 
            nominalsForm.simps(6) union_member)
      obtain G' where G_def': \<open>G' = agrees G ?x w\<close> 
        by simp
      then have \<open>RE (G' n) (G' ?x)\<close>
        using a1 by (smt (z3) ListSet.member.simps(2) add_def agrees_def fresh_new 
            member_sub_set nominalsNP.simps(2) sub_set_union2)
      moreover have \<open>semantics RE V G' (G' ?x) p\<close> 
        by (metis G_def' a2 agrees_def semantics_fresh_agree sub)
      ultimately have \<open>sc RE V G' LA RA RN LP RP R Q []\<close> 
        using r by simp
      then show \<open>sc RE V G LA RA RN LP RP R Q []\<close> 
        by (metis G_def' sc_fresh_agree)
    qed
  qed
  then show ?thesis 
    by auto
qed


lemma Q_Pos: \<open>
  let x = fresh (ns_1 LA RA RN LP RP R ((n, \<diamond> p) # Q)) in
  (\<forall>  (RE :: 'a \<Rightarrow> 'a \<Rightarrow> bool) V G. sc RE V G LA RA RN LP RP R ((n, Pos p) # Q) []) \<longleftrightarrow> (
    \<forall>  (RE :: 'a \<Rightarrow> 'a \<Rightarrow> bool) V G. sc RE V G LA RA RN ((n,x) # LP) RP R ((x,p) # Q) [])\<close> 
proof-
  let ?x = "fresh (ns_1 LA RA RN LP RP R ((n, \<diamond> p) # Q))"
  let ?A = \<open>\<lambda> RE V G. sc RE V G LA RA RN LP RP R ((n, Pos p) # Q) []\<close>
  let ?B = \<open>\<lambda> RE V G. semantics RE V G (G n) (Pos p)\<close>
  let ?C = \<open>\<lambda> RE V G. sc RE V G LA RA RN LP RP R Q []\<close>
  let ?D = \<open>\<lambda> RE V G. (\<exists> v. (RE (G n) v) \<and> (semantics RE V G v p))\<close>
  let ?E = \<open>\<lambda> RE V G. RE (G n) (G ?x)\<close>
  let ?F = \<open>\<lambda> RE V G. semantics RE V G (G ?x) p\<close>
  let ?G = \<open>\<lambda> RE V G. sc RE V G LA RA RN ((n,?x) # LP) RP R ((?x, p) # Q) []\<close>

  have 1:\<open>
    (\<forall> RE V G. ?A RE V G \<longleftrightarrow> (?B RE V G \<longrightarrow> ?C RE V G))\<close> 
    by (simp add: sc_pop_Q)
  have 2:\<open>(\<forall> RE V G. (?B RE V G) \<longleftrightarrow> (?D RE V G))\<close> 
    by simp
  have 3:\<open>\<forall> RE V G. (?E RE V G \<and> ?F RE V G \<longrightarrow> ?C RE V G) \<longleftrightarrow> ?G RE V G\<close> 
    by (auto simp add: sc_pop_Q sc_pop_LP)
  have \<open>
    (\<forall> (RE :: 'a \<Rightarrow> 'a \<Rightarrow> bool) V G. ?A RE V G) \<longleftrightarrow> 
    (\<forall> (RE :: 'a \<Rightarrow> 'a \<Rightarrow> bool) V G. ?B RE V G \<longrightarrow> ?C RE V G)\<close> 
    by (simp add: 1)
  moreover have \<open>
    ... \<longleftrightarrow> (\<forall> (RE :: 'a \<Rightarrow> 'a \<Rightarrow> bool) V G. ?D RE V G \<longrightarrow> ?C RE V G)\<close> 
    using 2 by (smt (z3))
  moreover have \<open>
    ... \<longleftrightarrow> (\<forall> (RE :: 'a \<Rightarrow> 'a \<Rightarrow> bool) V G. ?E RE V G \<and> ?F RE V G \<longrightarrow> ?C RE V G)\<close>
    by (metis semantic_exi_iff_fresh)
  moreover have \<open>
    ... \<longleftrightarrow> (\<forall> (RE :: 'a \<Rightarrow> 'a \<Rightarrow> bool) V G. ?G RE V G)\<close> 
    using 3 by (smt (z3))
  ultimately show ?thesis 
     by simp
 qed

lemma unique_G: \<open>
  (\<forall> (A :: 'a set). finite A \<longrightarrow> (\<exists> (a :: 'a). a \<notin> A)) \<Longrightarrow> 
  \<exists> (G :: nat \<Rightarrow> 'a). \<forall> n1 n2. member n1 ns \<longrightarrow> member n2 ns \<longrightarrow> n1 \<noteq> n2 \<longrightarrow> G n1 \<noteq> G n2\<close>
proof (induct ns)
  case Nil
  then show ?case by simp
next
  case (Cons n ns)
  then obtain G where G_def:
    \<open>\<forall>n1 n2. member n1 ns \<longrightarrow> member n2 ns \<longrightarrow> n1 \<noteq> n2 \<longrightarrow> (G :: nat \<Rightarrow> 'a) n1 \<noteq> G n2\<close> 
    by blast
  obtain Gns where Gns_def: \<open>Gns = map G ns\<close>
    by simp
  then show ?case 
  proof cases
    assume \<open>n \<in> set ns\<close>
    then show ?thesis
      by (metis G_def ListSet.member.simps(2) member_iff)
  next
    assume a:\<open>n \<notin> set ns\<close>
    then obtain G' where G_def':\<open>\<exists> w. G' = agrees G n w \<and> (w \<notin> set Gns)\<close> 
      by (metis Cons.prems List.finite_set) 
    have \<open>\<forall> n' \<in> set ns. G' n \<noteq> G' n'\<close> 
        by (metis G_def' Gns_def a agrees_def image_eqI list.set_map)
    then have \<open>\<forall> n1 n2. member n1 (n # ns) \<longrightarrow> member n2 (n # ns) \<longrightarrow> n1 \<noteq> n2 \<longrightarrow> G' n1 \<noteq> G' n2\<close> 
      by (metis G_def ListSet.member.simps(2) G_def' agrees_def member_iff)
    then show ?thesis 
      by blast
  qed
qed

definition agrees2 where \<open>agrees2 f x y \<equiv> (\<lambda> a b. (a = x \<and> b = y) \<or> f a b)\<close>

lemma unique_RE: "
  \<forall> n1 n2. member n1 ns \<longrightarrow> member n2 ns \<longrightarrow> n1 \<noteq> n2 \<longrightarrow> (G :: nat \<Rightarrow> 'a) n1 \<noteq> G n2 \<Longrightarrow>
  sub_set (nominalsNN lp) ns \<Longrightarrow>
  \<exists> RE. \<forall> n1 n2. member n1 ns \<longrightarrow> member n2 ns \<longrightarrow> (RE (G n1) (G n2) \<longleftrightarrow> (n1,n2) \<in> set lp)"
proof (induct lp)
  case Nil
  then show ?case 
    by auto
next
  case (Cons x lp)
  then obtain na nb where nanb_def: \<open>x = (na,nb)\<close> 
    by (metis nat_gcd.cases)
  have 1:\<open>
    (\<forall> n1 n2. member n1 ns \<longrightarrow> member n2 ns \<longrightarrow> n1 \<noteq> n2 \<longrightarrow> (G :: nat \<Rightarrow> 'a) n1 \<noteq> G n2) \<and>
    sub_set (nominalsNN lp) ns\<close>
    by (metis (no_types, hide_lams) Cons.prems(1) Cons.prems(2) add_sub_set member_sub_set 
        nominalsNN.simps(2) old.prod.exhaust)
  then obtain RE where RE_def: \<open>
    \<forall> n1 n2. member n1 ns \<longrightarrow> member n2 ns \<longrightarrow> (RE (G n1) (G n2) \<longleftrightarrow> (n1,n2) \<in> set lp)\<close> 
    using Cons.hyps by presburger
  obtain RE' where RE'_def: \<open>RE' = agrees2 RE (G na) (G nb)\<close>
    by simp
  have \<open>
    \<forall> n1 n2. member n1 ns \<longrightarrow> member n2 ns \<longrightarrow> (RE' (G n1) (G n2) \<longleftrightarrow> (n1,n2) \<in> set (x # lp))\<close>
  proof (intro allI impI iffI)
    fix n1 n2
    assume a1:\<open>member n1 ns\<close>
    assume a2:\<open>member n2 ns\<close>
    assume a3:\<open>RE' (G n1) (G n2)\<close>
    show \<open>(n1,n2) \<in> set (x # lp)\<close> 
      by (metis Cons.prems(1) Cons.prems(2) RE'_def RE_def a1 a2 a3 agrees2_def list.set_intros(1) 
          list.set_intros(2) member_sub_set nanb_def nomNN_member)
  next
    fix n1 n2
    assume a1:\<open>member n1 ns\<close>
    assume a2:\<open>member n2 ns\<close>
    assume a3:\<open>(n1,n2) \<in> set (x # lp)\<close>
    then consider \<open>(n1 = na \<and> n2 = nb)\<close> | \<open>(n1,n2) \<in> set lp\<close> 
      by (metis nanb_def prod.inject set_ConsD)
    then show \<open>RE' (G n1) (G n2)\<close> 
    proof cases
      case 1
      then show ?thesis 
        by (simp add: RE'_def agrees2_def)
    next
      case 2
      then have \<open>RE (G n1) (G n2)\<close>  
        using RE_def a1 a2 by blast
      then show ?thesis 
        by (simp add: RE'_def agrees2_def)
    qed
  qed
  then show ?case 
    by blast
qed

lemma unique_V: \<open>
  \<forall> n1 n2. member n1 ns \<longrightarrow> member n2 ns \<longrightarrow> n1 \<noteq> n2 \<longrightarrow> (G :: nat \<Rightarrow> 'a) n1 \<noteq> G n2 \<Longrightarrow>
  sub_set (nominalsNA la) ns \<Longrightarrow>
  \<exists> V. \<forall> n a. member n ns \<longrightarrow> (n,a) \<in> set la \<longleftrightarrow> V (G n) a\<close>
proof (induct la)
  case Nil
  then show ?case by auto
next
  case (Cons x la)
  then obtain n a where nanb_def: \<open>x = (n,a)\<close> 
    by (metis surj_pair)
  have 1:\<open>
    (\<forall> n1 n2. member n1 ns \<longrightarrow> member n2 ns \<longrightarrow> n1 \<noteq> n2 \<longrightarrow> (G :: nat \<Rightarrow> 'a) n1 \<noteq> G n2) \<and>
    sub_set (nominalsNA la) ns\<close> 
    using Cons.prems(1) Cons.prems(2) ListSet.member.simps(2) add_def nanb_def by fastforce
  then obtain V where V_def: \<open>
    \<forall> n a. member n ns \<longrightarrow> (n,a) \<in> set la \<longleftrightarrow> V (G n) a\<close> 
    using Cons.hyps by presburger
  obtain V' where V'_def: \<open>V' = agrees2 V (G n) a\<close>
    by simp
  have \<open>
    \<forall> n a. member n ns \<longrightarrow> (V' (G n) a \<longleftrightarrow> (n,a) \<in> set (x # la))\<close>
  proof (intro allI impI iffI)
    fix n' a'
    assume a1:\<open>member n' ns\<close>
    assume a2:\<open>V' (G n') a'\<close>
    show \<open>(n',a') \<in> set (x # la)\<close> 
      by (metis Cons.prems(1) Cons.prems(2) V'_def V_def a1 a2 agrees2_def list.set_intros(1) 
          list.set_intros(2) member_sub_set nanb_def nomNA_member)
  next
    fix n' a'
    assume a1:\<open>member n' ns\<close>
    assume a2:\<open>(n',a') \<in> set (x # la)\<close>
    then consider \<open>(n = n' \<and> a = a')\<close> | \<open>(n',a') \<in> set la\<close> 
      by (metis nanb_def prod.inject set_ConsD)
    then show \<open>V' (G n') a'\<close> 
    proof cases
      case 1
      then show ?thesis 
        by (simp add: V'_def agrees2_def)
    next
      case 2
      then have \<open>V (G n') a'\<close>  
        using V_def a1 a2 by blast
      then show ?thesis 
        by (simp add: V'_def agrees2_def)
    qed
  qed
  then show ?case 
    by blast
qed

lemma R_satted: \<open>
  consistent LA RA RN LP RP R [] [] (T :: 'a itself) \<Longrightarrow>
  \<forall> (n,ns,p) \<in> set R. 
  \<forall> m \<in> set (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U 
      nominalsNSNP R). 
    member m ns \<Longrightarrow>
  (\<forall> RE V G. sc RE (V :: 'a \<Rightarrow> 'b \<Rightarrow> bool) G LA RA RN LP RP R [] []) \<Longrightarrow>
  (\<forall> RE V G. sc RE (V :: 'a \<Rightarrow> 'b \<Rightarrow> bool) G LA RA RN LP RP [] [] [])\<close> 
proof (intro allI)
  let ?noms = \<open>nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U 
      nominalsNSNP R\<close>
  fix V :: \<open>'a \<Rightarrow> 'b \<Rightarrow> bool\<close>
  fix RE G 
  assume a0:\<open>consistent LA RA RN LP RP R [] [] (T :: 'a itself)\<close>
  assume a1:\<open>
    \<forall> (n,ns,p) \<in> set R. 
    \<forall> m \<in> set ?noms. member m ns\<close>
  assume a2:\<open>
    (\<forall> RE V G. sc RE (V :: 'a \<Rightarrow> 'b \<Rightarrow> bool) G LA RA RN LP RP R [] [])\<close>
  have \<open>(
      (\<forall> (n1,n2) \<in> set LP. RE (G n1) (G n2)) \<and>
      (\<forall> (n,a) \<in> set LA. V (G n) a)
    ) \<Longrightarrow> (
      (\<exists> (n1,n2) \<in> set RP. RE (G n1) (G n2)) \<or>
      (\<exists> (n1,n2) \<in> set RN. (G n1) = (G n2)) \<or>
      (\<exists> (n,a) \<in> set RA. V (G n) a)
    )\<close> (is \<open>?L \<Longrightarrow> ?R\<close>)
  proof-
    assume l:?L
    show ?R
    proof (rule ccontr)
      assume not_r:\<open>\<not>?R\<close>
      obtain RE' where RE'_def:
        \<open>RE' = (\<lambda> x y. (\<exists> n \<in> set ?noms. G n = x) \<and> (\<exists> n \<in> set ?noms. G n = y) \<and> RE x y)\<close>
        by simp
      have \<open>
        (\<forall> (n1,n2) \<in> set LP. RE' (G n1) (G n2)) \<and>
        (\<forall> (n,a) \<in> set LA. V (G n) a)\<close>
        by (smt (verit, del_insts) RE'_def case_prodD case_prodI2 l member_iff nomNN_member 
            sub_set_union2 union_member)
      then have \<open>
        (\<exists> (n,ns,p) \<in> set R. (\<exists> w. RE' (G n) w \<and> semantics RE' V G w p)) \<or>
        (\<exists> (n1,n2) \<in> set RP. RE' (G n1) (G n2)) \<or>
        (\<exists> (n1,n2) \<in> set RN. (G n1) = (G n2)) \<or>
        (\<exists> (n,a) \<in> set RA. V (G n) a)\<close>
        using a2 by (simp add: sc_def)
      then obtain n ns p w where nsnp_def: \<open>(n,ns,p) \<in> set R \<and> RE' (G n) w \<and> semantics RE' V G w p\<close> 
        using RE'_def not_r by blast
      then obtain m where mdef: \<open>G m = w \<and> m \<in> set ?noms\<close> 
        using RE'_def by auto
      then have 1:\<open>\<forall> RE G (V :: 'a \<Rightarrow> 'b \<Rightarrow> bool). sc RE V G LA RA RN LP ((n,m) # RP) R [] [(m,p)]\<close> 
        by (simp add: a2 sc_pop_P sc_pop_RP)
      have \<open>m \<in> set ns\<close> 
        using mdef a1 nsnp_def by fastforce 
      then show False 
        using 1 by (smt (z3) a0 case_prodD consistent_def nsnp_def)
    qed
  qed
  then show \<open>sc RE V G LA RA RN LP RP [] [] []\<close> 
    by (simp add: sc_def)
qed

lemma R_none: "
  consistent LA RA RN LP RP R [] [] (T :: 'a itself) \<Longrightarrow>
  (\<forall> (A :: 'a set). finite A \<longrightarrow> (\<exists> (a :: 'a). a \<notin> A)) \<Longrightarrow>
  saturate R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U 
      nominalsNSNP R) = None \<Longrightarrow>
    (\<forall> RE (V :: 'a \<Rightarrow> 'b \<Rightarrow> bool) G. sc RE V G LA RA RN LP RP R [] []) \<longleftrightarrow> 
    common LA RA \<or> common LP RP \<or> reflect RN" (is \<open>?cons \<Longrightarrow> ?axiom \<Longrightarrow> ?sat \<Longrightarrow> ?L \<longleftrightarrow> ?R\<close>)
proof -
  let ?noms = \<open>nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U 
      nominalsNSNP R\<close>
  assume cons:\<open>consistent LA RA RN LP RP R [] [] (T :: 'a itself)\<close>
  assume axi:?axiom
  assume sat:?sat
  then have satnone: \<open>\<forall> (n,ns,p) \<in> set R. \<forall> m \<in> set ?noms. member m ns\<close>
    by (smt (z3) ListSet.member.simps(1) case_prodI2 member_iff removent2 sat_iff)
  show "?L \<longleftrightarrow> ?R"
  proof
    assume l:?L
    from R_satted have sc_satted:"
      (\<forall> RE V G. sc RE (V :: 'a \<Rightarrow> 'b \<Rightarrow> bool) G LA RA RN LP RP [] [] [])" 
      using satnone l cons by blast
    show ?R 
    proof (rule ccontr)
      assume a:\<open>\<not> (common LA RA \<or> common LP RP \<or> reflect RN)\<close>
      have \<open>\<exists> (RE :: 'a \<Rightarrow> 'a \<Rightarrow> bool) (V :: 'a \<Rightarrow> 'b \<Rightarrow> bool) G. ((
        (\<forall> (n1,n2) \<in> set LP. RE (G n1) (G n2)) \<and>
        (\<forall> (n,a) \<in> set LA. V (G n) a)
      ) \<and> \<not>(
        (\<exists> (n1,n2) \<in> set RP. RE (G n1) (G n2)) \<or>
        (\<exists> (n1,n2) \<in> set RN. (G n1) = (G n2)) \<or>
        (\<exists> (n,a) \<in> set RA. V (G n) a)
      ))\<close>  
      proof-
        obtain G where Gdef: \<open>\<forall> n1 n2. 
          member n1 ?noms \<longrightarrow> member n2 ?noms \<longrightarrow> n1 \<noteq> n2 \<longrightarrow> (G :: nat \<Rightarrow> 'a) n1 \<noteq> G n2\<close> 
          using axi unique_G by blast
        then have 1:\<open>\<not> (\<exists> (n1,n2) \<in> set RN. (G n1) = (G n2))\<close>
          by (smt (verit, best) a case_prodE nomNN_member reflect_iff union_member)
        have \<open>sub_set (nominalsNN LP) ?noms\<close>
          by (meson member_sub_set union_member)
        then obtain RE where RE_def:\<open>\<forall> n1 n2. member n1 ?noms \<longrightarrow> member n2 ?noms \<longrightarrow>
          ((n1,n2) \<in> set LP \<longleftrightarrow> RE (G n1) (G n2))\<close> 
          using unique_RE Gdef by metis
        have 2:\<open>\<not>(\<exists> (n1,n2) \<in> set RP. RE (G n1) (G n2))\<close> 
        proof (rule ccontr)
          assume \<open>\<not> \<not> (\<exists> (n1,n2) \<in> set RP. RE (G n1) (G n2))\<close>
          then obtain n1 n2 where n1n2_def:\<open>(n1,n2) \<in> set RP \<and> RE (G n1) (G n2)\<close> 
            by blast
          then have \<open>member n1 ?noms \<and> member n2 ?noms\<close> 
            by (metis nomNN_member union_member)
          then have \<open>(n1,n2) \<in> set LP\<close>
            using RE_def n1n2_def by blast
          then have \<open>common RP LP\<close> 
            using n1n2_def by auto
          then show False 
            using a by blast
        qed
        have \<open>sub_set (nominalsNA LA) ?noms\<close>
          by (meson member_sub_set union_member)
        then obtain V where V_def: \<open>\<forall> n a. member n ?noms \<longrightarrow> (n,a) \<in> set LA \<longleftrightarrow> V (G n) a\<close> 
          using unique_V Gdef by metis
        have 3:\<open>\<not>(\<exists> (n,a) \<in> set RA. V (G n) a)\<close>
        proof (rule ccontr)
          assume \<open>\<not>\<not>(\<exists> (n,a) \<in> set RA. V (G n) a)\<close>
          then obtain n a where na_def: \<open>(n,a) \<in> set RA \<and> V (G n) a\<close>
            by blast
          moreover have \<open>member n ?noms\<close> 
            by (meson calculation nomNA_member union_member)
          ultimately have \<open>(n,a) \<in> set LA\<close> 
            using V_def by blast
          then have \<open>common LA RA\<close> 
            using na_def by auto 
          then show False 
            using a by simp
        qed
        have 4: \<open>(\<forall> (n1,n2) \<in> set LP. RE (G n1) (G n2))\<close> 
        proof (safe)
          fix n1 n2
          assume \<open>(n1,n2) \<in> set LP\<close>
          then have \<open>member n1 ?noms \<and> member n2 ?noms\<close> 
            by (metis nomNN_member union_member)
          then show \<open>RE (G n1) (G n2)\<close> 
            using RE_def \<open>(n1, n2) \<in> set LP\<close> by blast
        qed
        have 5: \<open>(\<forall> (n,a) \<in> set LA. V (G n) a)\<close>
        proof (safe)
          fix n a
          assume \<open>(n,a) \<in> set LA\<close>
          then have \<open>member n ?noms\<close> 
            by (meson nomNA_member union_member)
          then show \<open>V (G n) a\<close> 
            using V_def \<open>(n, a) \<in> set LA\<close> by blast
        qed
        show ?thesis 
          using 1 2 3 4 5 by auto
      qed

      moreover have "\<forall> (RE :: 'a \<Rightarrow> 'a \<Rightarrow> bool) (V :: 'a \<Rightarrow> 'b \<Rightarrow> bool) G. ((
        (\<forall> (n1,n2) \<in> set LP. RE (G n1) (G n2)) \<and>
        (\<forall> (n,a) \<in> set LA. V (G n) a)
      ) \<longrightarrow> (
        (\<exists> (n1,n2) \<in> set RP. RE (G n1) (G n2)) \<or>
        (\<exists> (n1,n2) \<in> set RN. (G n1) = (G n2)) \<or>
        (\<exists> (n,a) \<in> set RA. V (G n) a)
      ))"
      proof-
        have "\<forall> (RE :: 'a \<Rightarrow> 'a \<Rightarrow> bool) (V :: 'a \<Rightarrow> 'b \<Rightarrow> bool) G. ((
          (\<forall> (n,p) \<in> set []. semantics RE V G (G n) p) \<and> 
          (\<forall> (n1,n2) \<in> set LP. RE (G n1) (G n2)) \<and>
          (\<forall> (n,a) \<in> set LA. V (G n) a)
        ) \<longrightarrow> (
          (\<exists> (n,p) \<in> set []. semantics RE V G (G n) p) \<or>
          (\<exists> (n,u,p) \<in> set []. 
            (\<exists> w. RE (G n) w \<and> semantics RE V G w p)) \<or>
          (\<exists> (n1,n2) \<in> set RP. RE (G n1) (G n2)) \<or>
          (\<exists> (n1,n2) \<in> set RN. (G n1) = (G n2)) \<or>
          (\<exists> (n,a) \<in> set RA. V (G n) a)
        ))"
          using sc_def sc_satted by (smt (verit))
        then show ?thesis 
          by simp
      qed
      ultimately show False 
        by presburger
    qed
  next
    assume ?R
    then consider \<open>common LA RA\<close> | \<open>common LP RP\<close> | \<open>reflect RN\<close> 
      by blast
    then show ?L
    proof cases
      case 1
      then have \<open>\<exists> n a. (n,a) \<in> set LA \<and> (n,a) \<in> set RA\<close> 
        by auto
      then show ?thesis 
        using sc_def by blast
    next
      case 2
      then have \<open>\<exists> n1 n2. (n1,n2) \<in> set LP \<and> (n1,n2) \<in> set RP\<close> 
        by auto
      then show ?thesis 
        using sc_def by blast
    next
      case 3
      then have \<open>\<exists> n. (n,n) \<in> set RN\<close>
        by auto
      then show ?thesis 
        using sc_def by blast
    qed
  qed
qed

lemma member_split: \<open>member a (A @ B) \<Longrightarrow> member a A \<or> member a B\<close> 
  apply (induct A)
   apply simp 
  by (metis ListSet.member.simps(2) append_Cons)

lemma sat_exi: \<open>
  saturate R ns = Some (n,m,p,R',R'') \<Longrightarrow>
  member (n',u',p') R'' \<Longrightarrow>
  \<exists> u''. member (n',u'',p') R \<and> sub_set u'' u'\<close> 
proof-
  assume \<open>saturate R ns = Some (n,m,p,R',R'')\<close>
  then obtain R1 R2 ms where R1R2_def: \<open>R = R1 @ [(n,ms,p)] @ R2 \<and> R'' = R1 @ [(n,m # ms,p)] @ R2\<close> 
    by (smt (verit, ccfv_SIG) append_self_conv2 saturate_split2)
  assume \<open>member (n',u',p') R''\<close>
  then have \<open>member (n',u',p') (R1 @ [(n,m # ms,p)] @ R2)\<close>
    by (simp add: R1R2_def)
  then have \<open>member (n',u',p') (R1) \<or> member (n',u',p') ((n,m # ms,p) # R2)\<close>  
    using member_split by force
  then consider \<open>member (n',u',p') (R1) \<or> member (n',u',p') (R2)\<close> | \<open>(n',u',p') = (n,m # ms,p)\<close> 
    by (metis ListSet.member.simps(2))
  then show \<open>\<exists> u''. member (n',u'',p') R \<and> sub_set u'' u'\<close> 
  proof cases
    case 1
    then have "member (n',u',p') R" 
      using R1R2_def by (metis append.left_neutral append_Nil2 member_sub_set sub_remove_middle)
    then show ?thesis 
      by auto
  next
    case 2
    then show ?thesis 
      by (metis ListSet.member.simps(2) R1R2_def append.left_neutral append_Cons member_sub_set 
          prod.inject sub_remove_middle)
  qed
qed

lemma ms_exi: \<open>
  saturate R ns = Some (n,m,p,R',R'') \<Longrightarrow>
  \<exists> ms. (n,ms,p) \<in> set R \<and> \<not>member m ms\<close>
proof-
  assume "saturate R ns = Some (n,m,p,R',R'')"
  then obtain R1 R2 ms ms' where 
    "R = R1 @ [(n,ms,p)] @ R2 \<and> remove ns ms = m # ms'" 
    by (smt (verit, ccfv_threshold) append_self_conv2 saturate_split2)
  then show \<open>\<exists> ms. (n,ms,p) \<in> set R \<and> \<not>member m ms\<close> 
    by (metis ListSet.member.simps(2) ListSet.member_remove append_Cons in_set_conv_decomp)
qed

lemma ms_exi2: \<open>
  saturate R ns = Some (n,m,p,R',R'') \<Longrightarrow>
  (n,ms,p) \<in> set R' \<Longrightarrow>
  \<exists> ms'. (n,ms',p) \<in> set R\<close> 
  by (meson ms_exi)

lemma sat_sub_set: \<open>saturate R ns = Some (n,m,p,R',R'') \<Longrightarrow> sub_set R' R\<close> 
  by (metis saturate_split self_append_conv2 sub_remove_middle)

(*
function sv' where
  (*match RHS*)
  \<open>sv' CLCT LA RA RN LP RP R Q ((n,Pro a) # P) (T :: 'b) = 
    sv' CLCT LA ((n,a) # RA) RN LP RP R Q P (T :: 'b)\<close> |

  \<open>sv' CLCT LA RA RN LP RP R Q ((n1,Nom n2) # P) (T :: 'b) = 
    sv' CLCT LA RA ((n1,n2) # RN) LP RP R Q P (T :: 'b)\<close> |

  \<open>sv' CLCT LA RA RN LP RP R Q ((n,Neg p) # P) (T :: 'b) = 
    sv' CLCT LA RA RN LP RP R ((n,p) # Q) P (T :: 'b)\<close> |

  \<open>sv' CLCT LA RA RN LP RP R Q ((n,Con p1 p2) # P) (T :: 'b) =
    ((sv' CLCT LA RA RN LP RP R Q ((n,p1) # P) (T :: 'b)) \<and> 
    (sv' CLCT LA RA RN LP RP R Q ((n,p2) # P)) (T :: 'b))\<close> |

  \<open>sv' CLCT LA RA RN LP RP R Q ((n1,Sat n2 p) # P) (T :: 'b) = 
    sv' CLCT LA RA RN LP RP R Q ((n2,p) # P) (T :: 'b)\<close> |
(*We need to try to find a nominal witnessing Pos later. See last case*)
  \<open>sv' CLCT LA RA RN LP RP R Q ((n,Pos p) # P) (T :: 'b) = 
    sv' CLCT LA RA RN LP RP ((n,[],p) # R) Q P (T :: 'b)\<close>|

  (*match LHS*)
  \<open>sv' CLCT LA RA RN LP RP R ((n,Pro a) # Q) [] (T :: 'b) = 
    sv' CLCT ((n,a) # LA) RA RN LP RP R Q [] (T :: 'b)\<close> |
(*we assume/assert that n1=n2. therefore, remove one of them*)
  \<open>sv' CLCT LA RA RN LP RP R ((n1,Nom n2) # Q) [] (T :: 'b) = 
    sv' CLCT (mergeNA LA n1 n2) (mergeNA RA n1 n2) (mergeNN RN n1 n2) 
      (mergeNN LP n1 n2) (mergeNN RP n1 n2) (mergeNSNP R n1 n2) (mergeNP Q n1 n2) [] (T :: 'b)\<close> |

  \<open>sv' CLCT LA RA RN LP RP R ((n,Neg p) # Q) [] (T :: 'b) = 
    sv' CLCT LA RA RN LP RP R Q [(n,p)] (T :: 'b)\<close> |

  \<open>sv' CLCT LA RA RN LP RP R ((n,Con p1 p2) # Q) [] (T :: 'b) = 
    sv' CLCT LA RA RN LP RP R ((n,p1) # (n,p2) # Q) [] (T :: 'b)\<close> |

  \<open>sv' CLCT LA RA RN LP RP R ((n1,Sat n2 p) # Q) [] (T :: 'b) = 
    sv' CLCT LA RA RN LP RP R ((n2,p) # Q) [] (T :: 'b)\<close> |

  \<open>sv' CLCT LA RA RN LP RP R ((n,Pos p) # Q) [] (T :: 'b) = (
    let nw = fresh (
      nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U 
      nominalsNN RP U nominalsNSNP R U nominalsNP ((n,Pos p) # Q)) 
    in (sv' CLCT LA RA RN ((n,nw) # LP) RP R ((nw,p) # Q) []) (T :: 'b))\<close> |
(*-------Try all relevant assignments of nominals to possibility on RHS-----------
If no assignment can be made, check if current sequent is a tautology.
Else we can process a statement @n\<diamond>P.
  Find a nominal m to witness the statement
  Check if the sequent with @n\<diamond>P removed fulfills both @n\<diamond>m and @mP
Lastly, try another assignment. Remember that we already tried m.*)
  \<open>sv' CLCT LA (RA :: (nat \<times> 'a) list) RN LP RP R [] [] (T :: 'b) = 
      ((\<forall> (LA,RA,RN,LP,RP,R) \<in> CLCT. \<forall> RE (V :: 'b \<Rightarrow> 'a \<Rightarrow> bool) G. 
        sc RE V G LA RA RN LP RP R [] []) \<and> (
      case 
        saturate R (
          nominalsNA LA U nominalsNA RA U nominalsNN RN U 
          nominalsNN LP U nominalsNN RP U nominalsNSNP R)
      of
        None \<Rightarrow> (common LA RA \<or> common LP RP \<or> reflect RN)
      | Some (n,m,p,R',R'') \<Rightarrow> 
          (if (sv' CLCT LA RA RN LP ((n,m) # RP) R' [] [] (T :: 'b) \<and> 
            sv' CLCT LA RA RN LP RP R' [] [(m,p)] (T :: 'b)) 
          then True 
          else  sv' ({(LA, RA, RN, LP, RP, R)} \<union> CLCT) LA RA RN LP RP R'' [] [] (T :: 'b))))\<close> 
  by pat_completeness simp_all
termination sorry

lemma \<open>\<close>

lemma \<open>sv' CLCT LA RA RN LP RP R Q P T \<Longrightarrow> sv LA RA RN LP RP R Q P\<close>
proof (induct LA RA RN LP RP R Q P arbitrary: CLCT rule: sv.induct) 
  case (13 LA RA RN LP RP R)
  let ?sat = \<open>
    saturate R (
      nominalsNA LA U nominalsNA RA U nominalsNN RN U 
      nominalsNN LP U nominalsNN RP U nominalsNSNP R)\<close>
  have 1:\<open>(
      case 
        ?sat
      of
        None \<Rightarrow> (common LA RA \<or> common LP RP \<or> reflect RN)
      | Some (n,m,p,R',R'') \<Rightarrow> 
          (if (sv' CLCT LA RA RN LP ((n,m) # RP) R' [] [] (T :: 'b) \<and> 
            sv' CLCT LA RA RN LP RP R' [] [(m,p)] (T :: 'b)) 
          then True 
          else  sv' ({(LA, RA, RN, LP, RP, R)} \<union> CLCT) LA RA RN LP RP R'' [] [] (T :: 'b)))\<close> 
    using 13 by simp
  have 2:\<open>\<forall> n m p R' R''.
    (if (sv' CLCT LA RA RN LP ((n,m) # RP) R' [] [] (T :: 'b) \<and> 
      sv' CLCT LA RA RN LP RP R' [] [(m,p)] (T :: 'b)) 
    then True 
    else  sv' ({(LA, RA, RN, LP, RP, R)} \<union> CLCT) LA RA RN LP RP R'' [] [] (T :: 'b)) =
    ((sv' CLCT LA RA RN LP ((n,m) # RP) R' [] [] (T :: 'b) \<and> 
      sv' CLCT LA RA RN LP RP R' [] [(m,p)] (T :: 'b)) \<or>
    sv' ({(LA, RA, RN, LP, RP, R)} \<union> CLCT) LA RA RN LP RP R'' [] [] (T :: 'b))\<close>
    by meson
  consider (none) \<open>?sat = None\<close> | (some) \<open>\<exists>n m p R' R''. ?sat = Some (n,m,p,R',R'')\<close> 
    by (metis not_None_eq old.prod.exhaust)
  then show ?case 
  proof cases
    case none
    then have \<open>(common LA RA \<or> common LP RP \<or> reflect RN)\<close> 
      using "1" by fastforce
    moreover have \<open>(common LA RA \<or> common LP RP \<or> reflect RN) \<Longrightarrow> sv LA RA RN LP RP R [] []\<close>
      using none by simp
    ultimately show ?thesis 
      by simp
  next
    case some
    then obtain n m p R' R'' where satsome: \<open>?sat = Some (n,m,p,R',R'')\<close>
      by blast
    then have \<open>
      ((sv' CLCT LA RA RN LP ((n,m) # RP) R' [] [] (T :: 'b) \<and> 
        sv' CLCT LA RA RN LP RP R' [] [(m,p)] (T :: 'b)) \<or>
      sv' ({(LA, RA, RN, LP, RP, R)} \<union> CLCT) LA RA RN LP RP R'' [] [] (T :: 'b))\<close>
      using 1 2 by simp
    then have \<open>
      ((sv LA RA RN LP ((n,m) # RP) R' [] [] \<and> 
        sv LA RA RN LP RP R' [] [(m,p)]) \<or>
      sv LA RA RN LP RP R'' [] [])\<close> 
      by (meson "13.hyps"(1) "13.hyps"(2) "13.hyps"(3) satsome)
    then show ?thesis 
      using satsome by simp
  qed
qed auto

lemma R_some: "
  consistent LA RA RN LP RP R [] [] (T :: 'a itself) \<Longrightarrow>
  \<forall> (A :: 'a set). finite A \<longrightarrow> (\<exists> (a :: 'a). a \<notin> A) \<Longrightarrow>
  saturate R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U 
      nominalsNSNP R) = Some (n,m,p,R',R'') \<Longrightarrow>
    (\<forall> RE (V :: 'a \<Rightarrow> 'b \<Rightarrow> bool) G. sc RE V G LA RA RN LP RP R [] []) \<longleftrightarrow>
        (\<forall> RE (V :: 'a \<Rightarrow> 'b \<Rightarrow> bool) G. sc RE V G LA RA RN LP ((n,m) # RP) R' [] []) \<and> 
          (\<forall> RE (V :: 'a \<Rightarrow> 'b \<Rightarrow> bool) G. sc RE V G LA RA RN LP RP R' [] [(m,p)]) \<or>
        (\<forall> RE (V :: 'a \<Rightarrow> 'b \<Rightarrow> bool) G. sc RE V G LA RA RN LP RP R'' [] [])" 
(is \<open>?cons \<Longrightarrow> ?P1 \<Longrightarrow> ?P2 \<Longrightarrow> ?L \<longleftrightarrow> ?R\<close>)
proof
  let ?noms = \<open>nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U 
      nominalsNSNP R\<close>
  assume axi: ?P1
  assume sat: ?P2
  assume l: ?L
  have \<open>
    \<not>((\<forall> RE (V :: 'a \<Rightarrow> 'b \<Rightarrow> bool) G. sc RE V G LA RA RN LP ((n,m) # RP) R' [] []) \<and> 
          (\<forall> RE (V :: 'a \<Rightarrow> 'b \<Rightarrow> bool) G. sc RE V G LA RA RN LP RP R' [] [(m,p)])) \<Longrightarrow>
    (\<forall> RE (V :: 'a \<Rightarrow> 'b \<Rightarrow> bool) G. sc RE V G LA RA RN LP RP R'' [] [])\<close> (is \<open>\<not>(?L1\<and>?L2) \<Longrightarrow> ?R1\<close>) 
  proof (intro allI)
    fix V :: \<open>'a \<Rightarrow> 'b \<Rightarrow> bool\<close>
    fix RE G
    assume \<open>\<not>(?L1 \<and> ?L2)\<close>
    then consider \<open>\<not>?L1\<close> | \<open>\<not>?L2\<close>
      by blast
    then show \<open>sc RE V G LA RA RN LP RP R'' [] []\<close>
    proof cases
      case 1
      then obtain RE' V' G' where 
        \<open>\<not>sc RE' (V' :: 'a \<Rightarrow> 'b \<Rightarrow> bool) G' LA RA RN LP ((n,m) # RP) R' [] []\<close>
        by blast
      then have \<open>
        (\<forall> (n1,n2) \<in> set LP. RE' (G' n1) (G' n2)) \<and>
        (\<forall> (n,a) \<in> set LA. V' (G' n) a) \<and>
        \<not>(\<exists> (n,ns,p) \<in> set R'. (\<exists> w. RE' (G' n) w \<and> semantics RE' V' G' w p)) \<and>
        \<not>(\<exists> (n1,n2) \<in> set ((n,m) # RP). RE' (G' n1) (G' n2)) \<and>
        \<not>(\<exists> (n1,n2) \<in> set RN. (G' n1) = (G' n2)) \<and>
        \<not>(\<exists> (n,a) \<in> set RA. V' (G' n) a)
        \<close>
        by (simp add: sc_def)
      then have \<open>\<forall> RE V G. \<close>
      then show ?thesis sorry
    next
      case 2
      then show ?thesis sorry
    qed
  qed
  then show ?R 
    by blast
next
  let ?noms = \<open>nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U 
      nominalsNSNP R\<close>
  assume axi: ?P1
  assume sat: ?P2
  then obtain ms where ms_def:\<open>(n,ms,p) \<in> set R \<and> \<not>member m ms\<close> 
    by (meson ms_exi)
  have mdef: \<open>member m ?noms\<close>
    by (meson sat saturate_nom_members)
  assume r: ?R
  have \<open>\<forall> RE (V :: 'a \<Rightarrow> 'b \<Rightarrow> bool) G. ( 
      (\<forall> (n1,n2) \<in> set LP. RE (G n1) (G n2)) \<and>
      (\<forall> (n,a) \<in> set LA. V (G n) a)
    ) \<longrightarrow> (
      (\<exists> (n,u,p) \<in> set R. (\<exists> w. RE (G n) w \<and> semantics RE V G w p)) \<or>
      (\<exists> (n1,n2) \<in> set RP. RE (G n1) (G n2)) \<or>
      (\<exists> (n1,n2) \<in> set RN. (G n1) = (G n2)) \<or>
      (\<exists> (n,a) \<in> set RA. V (G n) a)
    )\<close>
  proof (intro allI impI)
    fix V :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
    fix RE G
    assume a:\<open>
      (\<forall> (n1,n2) \<in> set LP. RE (G n1) (G n2)) \<and>
      (\<forall> (n,a) \<in> set LA. V (G n) a)\<close>
    consider 
      \<open>(\<forall> RE (V :: 'a \<Rightarrow> 'b \<Rightarrow> bool) G. sc RE V G LA RA RN LP ((n,m) # RP) R' [] []) \<and> 
          (\<forall> RE (V :: 'a \<Rightarrow> 'b \<Rightarrow> bool) G. sc RE V G LA RA RN LP RP R' [] [(m,p)])\<close> | 
      \<open>(\<forall> RE (V :: 'a \<Rightarrow> 'b \<Rightarrow> bool) G. sc RE V G LA RA RN LP RP R'' [] [])\<close> 
      using r by fastforce
    then show \<open>
      (\<exists> (n,u,p) \<in> set R. 
        (\<exists> w. RE (G n) w \<and> semantics RE V G w p)) \<or>
      (\<exists> (n1,n2) \<in> set RP. RE (G n1) (G n2)) \<or>
      (\<exists> (n1,n2) \<in> set RN. (G n1) = (G n2)) \<or>
      (\<exists> (n,a) \<in> set RA. V (G n) a)\<close> 
    proof cases
      case 1
      consider \<open>sc RE V G LA RA RN LP RP R' [] []\<close> | \<open>RE (G n) (G m) \<and> semantics RE V G (G m) p\<close>
          by (metis "1" sc_pop_P sc_pop_RP)
      then show ?thesis 
      proof cases
        case 1
        have \<open>
          \<exists> (n,u,p) \<in> set R'. 
            (\<exists> w. RE (G n) w \<and> semantics RE V G w p) \<Longrightarrow>
          \<exists> (n,u,p) \<in> set R. 
            (\<exists> w. RE (G n) w \<and> semantics RE V G w p)\<close> 
        proof-
          assume \<open>
            \<exists> (n,u,p) \<in> set R'. 
            (\<exists> w. RE (G n) w \<and> semantics RE V G w p)\<close>
          then obtain n' u' p' w' where nupw'_def:
            \<open>(n',u',p') \<in> set R' \<and> RE (G n') w' \<and> semantics RE V G w' p'\<close> 
            by blast
          then have "\<exists> ms'. (n',ms',p') \<in> set R"
            using sat ms_exi2 by (meson member_iff member_sub_set sat_sub_set)
          then show \<open>
            \<exists> (n,u,p) \<in> set R. 
            (\<exists> w. RE (G n) w \<and> semantics RE V G w p)\<close> 
            using nupw'_def by blast
        qed
        moreover have \<open>
          (\<exists> (n,u,p) \<in> set R'. 
            (\<exists> w. RE (G n) w \<and> semantics RE V G w p)) \<or>
          (\<exists> (n1,n2) \<in> set RP. RE (G n1) (G n2)) \<or>
          (\<exists> (n1,n2) \<in> set RN. (G n1) = (G n2)) \<or>
          (\<exists> (n,a) \<in> set RA. V (G n) a)\<close> 
          using 1 a by (simp add: sc_def) 
        ultimately show ?thesis 
          by linarith
      next
        case 2
        then show ?thesis 
          using ms_def by blast
      qed
    next
      case 2
      then have \<open>
        (\<exists> (n,u,p) \<in> set R''. 
          (\<exists> w. RE (G n) w \<and> semantics RE V G w p)) \<or>
        (\<exists> (n1,n2) \<in> set RP. RE (G n1) (G n2)) \<or>
        (\<exists> (n1,n2) \<in> set RN. (G n1) = (G n2)) \<or>
        (\<exists> (n,a) \<in> set RA. V (G n) a)\<close> 
        using a by (simp add: sc_def) 
      moreover have \<open>
        (\<exists> (n,u,p) \<in> set R''. 
          (\<exists> w. RE (G n) w \<and> semantics RE V G w p) ) \<Longrightarrow>
        (\<exists> (n,u,p) \<in> set R. 
          (\<exists> w. RE (G n) w \<and> semantics RE V G w p))\<close> (is \<open>?L1 \<Longrightarrow> ?R1\<close>)
      proof-
        assume ?L1
        then obtain n' u' p' w' where nupw'_def: \<open>(n',u',p') \<in> set R'' \<and> 
          RE (G n') w' \<and> semantics RE V G w' p'\<close>
          by blast
        then obtain u'' where nupw''_def:
          \<open>(n',u'',p') \<in> set R \<and> sub_set u'' u'\<close> 
          using sat sat_exi by (metis member_iff) 
        then have \<open>
          (\<exists> w. RE (G n') w \<and> semantics RE V G w p')\<close> 
          using nupw'_def by auto
        then show ?R1 
          using nupw''_def by auto
      qed
      ultimately show ?thesis 
        by blast
    qed
  qed
  then show ?L 
    by (simp add: sc_def)
qed


theorem correctness: \<open>
  (\<forall> (A :: 'a set). finite A \<longrightarrow> (\<exists> (a :: 'a). a \<notin> A)) \<Longrightarrow>
  (\<forall> RE (V :: 'a \<Rightarrow> 'b \<Rightarrow> bool) G. sc RE V G LA RA RN LP RP R Q P) \<Longrightarrow>
  sv LA RA RN LP RP R Q P\<close>
proof (induct LA RA RN LP RP R Q P rule: sv.induct)
  case (1 LA RA RN LP RP R Q n a P)
  then show ?case 
    by (simp add: P_Pro)
next
  case (2 LA RA RN LP RP R Q n1 n2 P)
  then show ?case 
    by (auto simp add: P_Nom 2)
next
  case (3 LA RA RN LP RP R Q n p P)
  then show ?case 
    by (auto simp add: P_Neg 3)
next
  case (4 LA RA RN LP RP R Q n p1 p2 P)
  then show ?case 
    by (auto simp add: P_Con 4)
next
  case (5 LA RA RN LP RP R Q n1 n2 p P)
  then show ?case 
    by (auto simp add: P_Sat 5)
next
  case (6 LA RA RN LP RP R Q n p P)
  then show ?case 
    by (auto simp add: P_Pos 6)
next
  case (7 LA RA RN LP RP R n a Q)
  then show ?case 
    by (auto simp add: Q_Pro 7)
next
  case (8 LA RA RN LP RP R n1 n2 Q)
  then show ?case 
    by (meson sv.simps(8) Q_Nom 8)
next
  case (9 LA RA RN LP RP R n p Q)
  then show ?case 
    by (auto simp add: Q_Neg 9)
next
  case (10 LA RA RN LP RP R n p1 p2 Q)
  then show ?case 
    by (auto simp add: Q_Con 10)
next
  case (11 LA RA RN LP RP R n1 n2 p Q)
  then show ?case 
    by (auto simp add: Q_Sat 11)
next
  case (12 LA RA RN LP RP R n p Q)
  then show ?case 
    by (meson sv.simps(12) Q_Pos 12)
next
  case (13 LA RA RN LP RP R)
  let ?sat = \<open>
    saturate R (nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U nominalsNN RP U 
      nominalsNSNP R)\<close>
  have axi: \<open>(\<forall> (A :: 'a set). finite A \<longrightarrow> (\<exists> (a :: 'a). a \<notin> A))\<close> 
    by (simp add: "13.prems")
  have cons:\<open>consistent LA RA RN LP RP R [] [] (T :: 'a itself)\<close> sorry

  consider (none)\<open>?sat = None\<close> | (some)\<open>\<exists> n m p R' R''. ?sat = Some (n,m,p,R',R'')\<close> 
    by (metis option.exhaust prod_cases5)
  then show ?case 
  proof cases
    case none
    then have \<open>(\<forall> RE (V :: 'a \<Rightarrow> 'b \<Rightarrow> bool) G. 
      sc RE V G LA RA RN LP RP R [] []) \<longleftrightarrow> common LA RA \<or> common LP RP \<or> reflect RN\<close> 
      using axi cons by (simp add: R_none)
    moreover have \<open>sv LA RA RN LP RP R [] [] \<longleftrightarrow> common LA RA \<or> common LP RP \<or> reflect RN\<close> 
      using none by simp
    ultimately show ?thesis using "13.prems"(2) by blast
  next
    case some
    then obtain n m p R' R'' where sat_def:\<open>?sat = Some (n,m,p,R',R'')\<close> by auto
    then have \<open>(\<forall>  RE (V :: 'a \<Rightarrow> 'b \<Rightarrow> bool) G. 
      sc RE V G LA RA RN LP RP R [] []) \<longleftrightarrow>
        (\<forall>  RE (V :: 'a \<Rightarrow> 'b \<Rightarrow> bool) G. sc RE V G LA RA RN LP ((n,m) # RP) R' [] []) \<and> 
          (\<forall>  RE (V :: 'a \<Rightarrow> 'b \<Rightarrow> bool) G. sc RE V G LA RA RN LP RP R' [] [(m,p)]) \<or>
        (\<forall>  RE (V :: 'a \<Rightarrow> 'b \<Rightarrow> bool) G. sc RE V G LA RA RN LP RP R'' [] [])\<close> 
      using axi R_some cons by metis
    moreover have \<open>
      sv LA RA RN LP RP R [] [] \<longleftrightarrow>
        (sv LA RA RN LP ((n,m) # RP) R' [] [] \<and> 
          sv LA RA RN LP RP R' [] [(m,p)]) \<or>
        sv LA RA RN LP RP R'' [] []\<close>
      using sat_def by simp
    ultimately show ?thesis 
      using "13.hyps" sat_def axi by (metis "13.prems"(2))
  qed
qed*)
(*/soundness*)

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
proposition \<open>prover 
  (NOT ((Sat 1 (Pos (NOM 4))) AND 
  (NOT (Sat 1 (Pos (NOT ((Sat 2 (Pos (NOM 3))) AND (Sat 3 (Pro A))) AND 
  NOT ((Sat 2 (Pos (NOM 4))) AND (Sat 4 (Pro A))))))) AND 
  (NOT (Sat 2 (Pos (Pro A))))))\<close>
  by eval

proposition \<open>prover 
  (NOT ((Sat 1 (Pos (NOM 4))) AND 
  (NOT (Sat 2 (Pos (Pro A)))) AND
  (NOT (Sat 1 (Pos (NOT ((Sat 2 (Pos (NOM 3))) AND (Sat 3 (Pro A))) AND 
  NOT ((Sat 2 (Pos (NOM 4))) AND (Sat 4 (Pro A)))))))))\<close>
  by eval

proposition \<open>prover (
  (AT 1 NOM 4) THEN (AT 2 \<diamond> PRO A) OR ((NOT ((AT 2 \<diamond> NOM 3) AND AT 3 PRO A) AND NOT ((AT 2 \<diamond> NOM 4) AND AT 4 PRO A))))\<close>
  by eval

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