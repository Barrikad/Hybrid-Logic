theory HybridSequentCalculus imports Main
begin

(*lists as sets functions*)

primrec member where
  \<open>member _ [] = False\<close> |
  \<open>member m (n # A) = (m = n \<or> member m A)\<close>

lemma member_iff [iff]: \<open>member m A \<longleftrightarrow> m \<in> set A\<close>
  by (induct A) simp_all

primrec common where
  \<open>common _ [] = False\<close> |
  \<open>common X (y # Y) = (member y X \<or> common X Y)\<close>

lemma common_iff [iff]: \<open>common A B \<longleftrightarrow> set A \<inter> set B \<noteq> {}\<close>
  by (induct B) simp_all

definition add where "
  add a X \<equiv> 
    if member a X
    then X
    else a # X" 

lemma add_simp [simp]: \<open>add a X = Y \<longrightarrow> (insert a (set X)) = set Y\<close>
  by (metis add_def insert_absorb list.simps(15) member_iff)

(*UNION*)
primrec union (infixr \<open>U\<close> 100) where
  \<open>union A [] = A\<close> |
  \<open>union A (b # B) = union (add b A) B\<close>

lemma union_simp [simp]: \<open>union A B = C \<longrightarrow> set A \<union> set B = set C\<close>
proof (induct B arbitrary: A C)
case Nil
  then show ?case by simp
next
  case (Cons a B)
  then show ?case
    by (metis Un_insert_left Un_insert_right add_simp list.simps(15) union.simps(2))
qed 
(*\UNION*)

(*REMOVE*)
primrec remove where
  \<open>remove [] B = []\<close> |
  \<open>remove (a # A) B = (
    if member a B
    then remove A B
    else a # remove A B)\<close>

lemma remove_simp [simp]: \<open>remove A B = C \<longrightarrow> set A - set B = set C\<close>
proof (induct A arbitrary: B C)
case Nil
  then show ?case by simp
next
  case (Cons a A)
  then show ?case 
    by (metis insert_Diff_if list.simps(15) member_iff remove.simps(2))
qed

lemma removent: \<open>\<not>common A B \<Longrightarrow> remove A B = A\<close> 
proof (induct A)
case Nil
  then show ?case by simp
next
  case (Cons a A)
  then have a: "\<not> common (a # A) B \<and> (\<not> common A B \<longrightarrow> remove A B = A)" by simp
  then have 1:"\<not> member a B"
    by (metis common_iff insert_disjoint(1) list.simps(15) member_iff)
  from a have "\<not> common A B" 
    by (metis "1" Int_insert_left_if0 common_iff list.simps(15) member_iff)
  then show ?case using 1
    using Cons.hyps by fastforce
qed 

lemma remove_size: \<open>common A B \<Longrightarrow> size (remove A B) < size A\<close>
proof (induct A)
  case Nil
  then show ?case by simp
next
  case (Cons a A)
  then have a: "(common A B \<longrightarrow> length (remove A B) < length A) \<and> common (a # A) B" by simp
  then show ?case 
  proof cases
    assume "member a B"
    then show ?thesis using a 
      by (metis dual_order.strict_trans impossible_Cons not_le_imp_less remove.simps(2) removent)
  next
    assume "\<not> member a B"
    then have "common A B"
      using Cons.prems set_ConsD by fastforce
    then show ?thesis using a by simp
  qed
qed
(*\REMOVE*)

(*SETEQUAL*)
definition set_equal where \<open>set_equal A B \<equiv> remove A B = [] \<and> remove B A = []\<close>

lemma set_equal_iff[iff]: "set_equal A B \<longleftrightarrow> set A = set B"
proof (induct A arbitrary: B)
  case Nil
  then show ?case by (smt (z3) Diff_empty remove_simp set_empty set_equal_def)
next
  case (Cons a A)
  then show ?case 
    by (smt (verit) Diff_cancel Un_Diff_cancel Un_left_commute 
        remove_simp set_empty2 set_equal_def sup_bot.right_neutral)
qed 

lemma unionadd: \<open>set_equal (add a (A U B)) ((add a A) U B)\<close>
  by (metis Un_insert_left add_simp set_equal_iff union_simp)

lemma unionaddnt: \<open>set_equal ([] U B) B\<close>
proof (induct B)
  case Nil
  then show ?case by simp
next
  case (Cons a B)
  then show ?case using set_equal_def
    by (smt (verit, del_insts) add_def add_simp 
        list.simps(15) set_equal_iff union.simps(2) unionadd)
qed 
(*\SETEQUAL*)

(*ISSET*)
primrec is_set where 
  \<open>is_set [] = True\<close> |
  \<open>is_set (a # A) = (\<not> member a A \<and> is_set A)\<close>

lemma is_set_size: \<open>is_set A \<longleftrightarrow> (\<forall> a. member a A \<longrightarrow> Suc (size (remove A [a])) = size A)\<close>
proof (induct A)
  case Nil
  then show ?case by simp
next
  case (Cons a A)
  assume a1: "is_set A = (\<forall>a. member a A \<longrightarrow> Suc (length (remove A [a])) = length A)"
  show "is_set (a # A) \<longleftrightarrow> (\<forall>aa. member aa (a # A) \<longrightarrow> Suc (length (remove (a # A) [aa])) = length (a # A))" 
  proof
    assume a2: "is_set (a # A)"
    then have 1:"(\<forall>a. member a A \<longrightarrow> Suc (length (remove A [a])) = length A)" using a1  by simp

    show "(\<forall>aa. member aa (a # A) \<longrightarrow> Suc (length (remove (a # A) [aa])) = length (a # A))" 
    proof
      fix aa
      show "member aa (a # A) \<longrightarrow> Suc (length (remove (a # A) [aa])) = length (a # A)" 
      proof
        assume a3: "member aa (a # A)"
        show "Suc (length (remove (a # A) [aa])) = length (a # A)" 
        proof cases
          assume "member aa A"
          then show ?thesis
            using 1 a2 by auto
        next
          assume a4: "\<not> member aa A"
          then have 1: \<open>remove (a # A) [aa] = remove A [aa]\<close> 
            by (metis member.simps(2) a3 remove.simps(2)) 
          then have "remove A [aa] = A" using a4 removent 
            by force
          then show ?thesis
            using 1 by auto
        qed
      qed
    qed
  next
    assume a2:"\<forall>aa. member aa (a # A) \<longrightarrow> Suc (length (remove (a # A) [aa])) = length (a # A)"
    have "\<forall>a. member a A \<longrightarrow> Suc (length (remove A [a])) = length A" 
    proof
      fix a'
      show "member a' A \<longrightarrow> Suc (length (remove A [a'])) = length A" 
      proof
        assume a3:"member a' A"
        then have 1: "Suc (length (remove (a # A) [a'])) = length (a # A)" using a2 
          by (meson HybridSequentCalculus.member.simps(2))
        have "a \<noteq> a'" 
        proof (rule ccontr)
          assume "\<not>a \<noteq> a'"
          then have 2:"remove (a # A) [a'] = remove A [a']" by simp
          have "length (remove A [a']) < length A" using a3 
            by (metis common.simps(2) remove_size)
          then show "False" 
            using 1 2 by fastforce
        qed
        then show "Suc (length (remove A [a'])) = length A" 
          using 1 by auto
      qed
    qed
    then show "is_set (a # A)"
      using HybridSequentCalculus.member.simps(2) a1 a2 by fastforce
  qed
qed

lemma union_is_set: \<open>is_set A \<Longrightarrow> is_set (A U B)\<close>
proof (induct B arbitrary: A)
  case Nil
  then show ?case by simp
next
  case (Cons a B)
  then show ?case 
    by (metis add_def is_set.simps(2) union.simps(2))
qed

(*\ISSET*)

datatype 'a option
  = None
  | Some 'a

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
  \<open>nominalsNSNP ((n,ns,p) # NSNP) = add n (union (union (nominalsForm p) (nominalsNSNP NSNP)) ns)\<close>

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
  apply (induct NSNP)
   apply simp
  by (metis form_is_set list.distinct(1) nominalsNSNP.cases nominalsNSNP.simps(2) 
      union.simps(1) union.simps(2) union_is_set)
  
(*merge functions replaces all occurences of a nominal with another.
Used when two nominals are found to be equal*)
fun mergeNS where 
  \<open>mergeNS [] na nb = []\<close> |
  \<open>mergeNS (n # NS) na nb = (if n = na then nb else n) # (mergeNS NS na nb)\<close>

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
      by (meson HybridSequentCalculus.member.simps(2))
    from this 1 have "(\<forall>n ms p. member (n, ms, p) R \<longrightarrow> remove ns ms = []) \<longrightarrow>
                       saturate' (R' @ [(n, ms, p)]) R ns = None" by simp
    from this 2 have 3:"saturate' (R' @ [(n, ms, p)]) R ns = None" 
      by (meson HybridSequentCalculus.member.simps(2))
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
        by (metis (no_types, lifting) "1" a2 addnt2 append_Cons self_append_conv2)
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

fun missing' where
  \<open>missing' ms [] = 0\<close> |
  \<open>missing' ms (n # ns) = (if \<not>member n ms then Suc (missing' ms ns) else missing' ms ns)\<close>

lemma miss1: \<open>missing' (m # ms) ns \<le> missing' ms ns\<close>
proof (induct ns arbitrary: ms)
  case Nil
  then show ?case by simp
next
  case (Cons a ns)
  then show ?case 
    by (metis HybridSequentCalculus.member.simps(2) Suc_leD Suc_le_mono missing'.simps(2))
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
          by (metis HybridSequentCalculus.member.simps(2) 
              a1 a2 a3 missing'.simps(2) remove.simps(2))
      qed
    next
      assume "\<not> member a (m' # ms)"
      then show "missing' (m' # ms) (a # ns) < missing' ms (a # ns)" 
        by (metis HybridSequentCalculus.member.simps(2) a2 list.inject remove.simps(2))
    qed
  qed
qed

fun missing where
  \<open>missing [] ns = 0\<close> |
  \<open>missing ((_,ms,_) # R) ns = missing' ms ns + missing R ns\<close>

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

(*Check if any of the pairs in a list contains two of the same element*)
fun reflect where
  \<open>reflect [] = False\<close> |
  \<open>reflect ((n1,n2) # B) = (n1 = n2 \<or> reflect B)\<close>



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

function atomize where
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
primrec size_atom_form :: \<open>nat \<Rightarrow> nat \<Rightarrow> 'a hybr_form \<Rightarrow> nat\<close> where
  \<open>size_atom_form r ns (Pro a) = Suc 0\<close> |
  \<open>size_atom_form r ns (Nom n) = Suc 0\<close> |
  \<open>size_atom_form r ns (Neg p) = Suc (size_atom_form r ns p)\<close> |
  \<open>size_atom_form r ns (Con p1 p2) = Suc (size_atom_form r ns p1 + size_atom_form r ns p2)\<close> |
  \<open>size_atom_form r ns (Sat n p) = Suc (size_atom_form r ns p)\<close> |
  \<open>size_atom_form r ns (Pos p) = Suc (Suc (r + ns + size_atom_form r ns p))\<close>

termination 
  apply (relation \<open>measure (\<lambda>(LA,RA,RN,LP,RP,R,Q,P). 
    let ns = nominalsNA LA U nominalsNA RA U nominalsNN RN U 
      nominalsNN LP U nominalsNN RP U nominalsNSNP R U nominalsNP Q U nominalsNP P in
    (\<Sum>(_,p) \<leftarrow> Q @ P. size_atom_form (size R) (size ns) p) + 
    (\<Sum>(_,_,p) \<leftarrow> R. Suc (size_atom_form (size R) (size ns) p)) + 
    missing R ns)\<close>) 
  apply simp_all



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