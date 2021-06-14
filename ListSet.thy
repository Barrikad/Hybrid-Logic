theory ListSet imports Main
begin

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
  apply (induct B arbitrary: A C)
   apply simp
  by (metis Un_insert_left Un_insert_right add_simp list.simps(15) union.simps(2))

lemma union_member: \<open>member a (A U B) \<longleftrightarrow> member a A \<or> member a B\<close> 
  by (metis Un_iff member_iff union_simp)
(*\UNION*)

(*REMOVE*)
primrec remove where
  \<open>remove [] B = []\<close> |
  \<open>remove (a # A) B = (
    if member a B
    then remove A B
    else a # remove A B)\<close>

lemma remove_simp [simp]: \<open>remove A B = C \<longrightarrow> set A - set B = set C\<close>
  apply (induct A arbitrary: B C)
   apply simp
  by (metis insert_Diff_if list.simps(15) member_iff remove.simps(2))

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

lemma removent2: \<open>\<not> member b B \<Longrightarrow> member b A \<Longrightarrow> member b (remove A B)\<close>
  by (metis DiffI member_iff remove_simp)

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

lemma member_remove: \<open>member a B \<Longrightarrow> \<not> member a (remove A B)\<close> 
  by (metis DiffD2 member_iff remove_simp)
(*\REMOVE*)

(*SETEQUAL*)
definition set_equal where \<open>set_equal A B \<equiv> remove A B = [] \<and> remove B A = []\<close>

lemma set_equal_iff[iff]: "set_equal A B \<longleftrightarrow> set A = set B"
  apply (induct A arbitrary: B)
   apply (smt (z3) Diff_empty remove_simp set_empty set_equal_def)
  by (smt (verit) Diff_cancel Un_Diff_cancel Un_left_commute 
      remove_simp set_empty2 set_equal_def sup_bot.right_neutral)

lemma set_equal_reflexive: \<open>set_equal A A\<close> 
  by simp

lemma set_equal_commutative: \<open>set_equal A B \<longleftrightarrow> set_equal B A\<close>
  by auto

lemma set_equal_associative: \<open>set_equal A B \<Longrightarrow> set_equal B C \<Longrightarrow> set_equal A C\<close>
  by simp

lemma union_commutative: \<open>set_equal (A U B) (B U A)\<close> 
  apply simp 
  by (metis Un_commute union_simp)

lemma union_associative: \<open>set_equal (A U (B U C)) ((A U B) U C)\<close>
  by (metis boolean_algebra_cancel.sup1 set_equal_iff union_simp)

lemma union_reflexive:\<open>set_equal A (A U A)\<close>
  by (metis set_equal_iff sup.idem union_simp)

lemma equal_add: \<open>set_equal A B \<Longrightarrow> set_equal (add a A) (add a B)\<close> 
  by (metis add_simp set_equal_iff)

lemma unionadd1: \<open>set_equal (add a (A U B)) ((add a A) U B)\<close>
  by (metis Un_insert_left add_simp set_equal_iff union_simp)

lemma unionadd11: \<open>set_equal (add a (add b (A U B))) ((add a (add b A)) U B)\<close> 
  by (metis add_simp set_equal_iff unionadd1)

lemma unionadd2: \<open>set_equal (add a (A U B)) (A U (add a B))\<close> 
  by (metis add_simp set_equal_iff union_commutative unionadd1)

lemma unionaddnt: \<open>set_equal ([] U B) B\<close>
proof (induct B)
  case Nil
  then show ?case by simp
next
  case (Cons a B)
  then show ?case using set_equal_def
    by (smt (verit, del_insts) add_def add_simp 
        list.simps(15) set_equal_iff union.simps(2) unionadd1)
qed 

lemma union_with_equal: \<open>set_equal A B \<Longrightarrow> set_equal (C U A) (C U B)\<close>
  apply (induct C)
   apply (metis set_equal_iff unionaddnt)
  apply simp
  by (metis union_simp)

lemma union_with_equal2: \<open>set_equal A B \<Longrightarrow> set_equal (A U C) (B U C)\<close>
  by (metis set_equal_iff union_simp)

lemma set_equal_append_add: \<open>set_equal (a # A) (add a A)\<close> 
  by simp

lemma remove_equal: \<open>set_equal A B \<Longrightarrow> set_equal (remove A C) (remove B C)\<close>
  by (metis remove_simp set_equal_iff)

lemma remove_commute: \<open>set_equal (remove (remove A B) C) (remove A (C @ B))\<close> 
proof (induct A)
  case Nil
  then show ?case by simp
next
  case (Cons a A)
  consider \<open>member a B \<or> member a C\<close> | \<open>\<not>member a B \<and> \<not>member a C\<close>
    by auto
  then show ?case 
  proof cases
    case 1
    have \<open>member a (C @ B)\<close> 
      by (metis 1 UnI1 UnI2 member_iff set_append)
    then have \<open>set_equal (remove (a # A) (C @ B)) (remove A (C @ B))\<close> 
      by simp
    moreover have \<open>set_equal (remove (remove (a # A) B) C) (remove (remove A B) C)\<close> 
      using "1" by auto 
    ultimately show ?thesis 
      using Cons.hyps by force
  next
    case 2
    then have \<open>\<not>member a (C @ B)\<close> 
      by (metis Un_iff member_iff set_append)
    then have \<open>set_equal (remove (a # A) (C @ B)) (a # (remove A (C @ B)))\<close> 
      by simp
    moreover have \<open>set_equal (remove (remove (a # A) B) C) (a # (remove (remove A B) C))\<close>
      using "2" by auto
    ultimately show ?thesis
      using Cons.hyps by force
  qed
qed

lemma set_equal_remove_commont: \<open>
  \<not> common A B \<Longrightarrow> set_equal (remove (B @ A) B) A\<close>  
proof (induct B)
  case Nil
  then show ?case 
    by (simp add: removent)
next
  case (Cons a B)
  have 0:\<open>\<not>member a A\<close>
    by (meson Cons.prems common.simps(2))
  have 1:\<open>set_equal A (remove (B @ A) B)\<close>
    by (meson Cons.hyps Cons.prems common.simps(2) set_equal_commutative)
  then have 2:\<open>\<not> member a (remove (B @ A) B)\<close> 
    by (metis Cons.prems ListSet.member.simps(1) common.simps(2) removent2 set_equal_def)
  have \<open>set_equal A (remove (B @ A) B)\<close> 
    using "1" by auto
  moreover have \<open>set_equal ... (remove (remove (B @ A) B) [a])\<close> 
    by (metis "2" append_Nil2 common.simps(1) common.simps(2) remove_commute removent) 
  moreover have \<open>set_equal ... (remove (B @ A) (a # B))\<close> 
    by (metis append_Cons append_Nil remove_commute)
  moreover have \<open>set_equal ... (remove (a # B @ A) (a # B))\<close> 
    by (metis ListSet.member.simps(2) remove.simps(2) union_with_equal union.simps(1) unionaddnt)
  ultimately show ?case
    by simp
qed 

lemma set_equal_commont_remove: \<open>
  \<not> common A C \<Longrightarrow> set_equal (C @ A) B \<Longrightarrow> set_equal A (remove B C)\<close> 
proof -
  assume a1:\<open>\<not> common A C\<close>
  assume a2:\<open>set_equal (C @ A) B\<close>
  then have \<open>set_equal (remove (C @ A) C) (remove B C)\<close> 
    by (meson remove_equal)
  moreover have \<open>set_equal (remove (C @ A) C) A\<close> using a1 
    by (meson set_equal_remove_commont)
  ultimately show ?thesis
    by simp
qed

lemma double_union_equal: \<open>
  set_equal A C \<Longrightarrow> set_equal B D \<Longrightarrow> set_equal (A U B) (C U D)\<close> (is \<open>?A1 \<Longrightarrow> ?A2 \<Longrightarrow> ?C\<close>)
proof -
  assume a1:"?A1"
  assume a2:\<open>?A2\<close>
  have \<open>set_equal (A U B) (A U D)\<close> 
    by (meson a2 union_with_equal)
  then show ?C 
    by (metis a1 set_equal_iff union_simp)
qed

lemma set_equal_add_con: \<open>set_equal (add a (b # A)) (b # (add a A))\<close> 
proof-
  have \<open>set_equal (add a (b # A)) (add a (add b A))\<close> 
    by (meson equal_add set_equal_append_add)
  moreover have \<open>set_equal ... (add b (add a A))\<close> 
    by (metis calculation set_equal_associative set_equal_commutative union.simps(1) 
        union.simps(2) union_commutative unionadd2)
  ultimately show ?thesis 
    by simp
qed
(*\SETEQUAL*)

(*SUBSET*)
definition sub_set where "sub_set A B \<equiv> remove A B = []"

lemma sub_set_iff[iff]: "sub_set A B \<longleftrightarrow> set A \<subseteq> set B"
  apply (induct A)
   apply (simp add: sub_set_def)
  by (metis Diff_eq_empty_iff remove_simp set_empty sub_set_def)

lemma sub_set_union1: \<open>sub_set A (A U B)\<close>
  by (metis sub_set_iff sup.cobounded1 union_simp)

lemma sub_set_union2: \<open>sub_set A (B U A)\<close>
  by (metis UnI2 sub_set_iff subsetI union_simp)

lemma sub_set_remove: \<open>\<not> member a' A \<Longrightarrow> sub_set A B \<Longrightarrow> sub_set A (remove B [a'])\<close>
proof (induct A arbitrary: a' B)
  case Nil
  then show ?case by simp
next
  case (Cons a A)
  have 1:"a' \<noteq> a" 
    by (metis Cons.prems(1) member.simps(2))
  have 2:"sub_set A (remove B [a'])"
    by (metis Cons.hyps Cons.prems(1) Cons.prems(2) member.simps(2) 
        list.distinct(1) remove.simps(2) sub_set_def)
  show ?case 
  proof cases
    assume "member a B"
    then have "member a (remove B [a'])" 
      by (metis "1" member.simps(1) 
          member.simps(2) removent2)
    then show ?thesis 
      by (metis 2 remove.simps(2) sub_set_def) 
  next
    assume "\<not>member a B"
    then show ?thesis
      by (metis Cons.prems(2) list.distinct(1) remove.simps(2) sub_set_def)
  qed
qed

lemma sub_set_remove2: \<open>\<not> member a' A \<Longrightarrow> sub_set A (a' # B) \<Longrightarrow> sub_set A B\<close> 
  using set_ConsD by fastforce

lemma add_sub_set: \<open>sub_set A B \<Longrightarrow> sub_set A (add b B)\<close>
  by (metis add_simp sub_set_iff subset_insertI2)

lemma sub_set_union: \<open>sub_set A C \<Longrightarrow> sub_set B C \<Longrightarrow> sub_set (A U B) C\<close> 
  by (metis Un_subset_iff sub_set_iff union_simp)

lemma member_sub_set: \<open>(\<forall> a. member a A \<longrightarrow> member a B) \<longleftrightarrow> sub_set A B\<close> 
  by auto

lemma sub_remove_set: \<open>sub_set A B \<Longrightarrow> sub_set (remove A C) B\<close> 
  apply (induct A) 
   apply simp 
  by (metis list.distinct(1) remove.simps(2) sub_set_def)

lemma sub_remove_middle: \<open>A = A1 @ A2 @ A3 \<Longrightarrow> A' = A1 @ A3 \<Longrightarrow> sub_set A' A\<close>
  apply (induct A1 arbitrary: A A') 
   apply simp
   apply (meson sub_set_iff sub_set_union2)
  by (metis (full_types) Cons_eq_appendI ListSet.member.simps(2) member_sub_set)
(*\SUBSET*)

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
          by (meson member.simps(2))
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
      using member.simps(2) a1 a2 by fastforce
  qed
qed

lemma union_is_set: \<open>is_set A \<Longrightarrow> is_set (A U B)\<close>
  apply (induct B arbitrary: A)
  apply simp
 by (metis add_def is_set.simps(2) union.simps(2))

lemma add_is_set: \<open>is_set A \<Longrightarrow> is_set (add a A)\<close>
  by (simp add: add_def)

lemma remove_is_set: \<open>is_set A \<Longrightarrow> is_set (remove A B)\<close>
proof (induct A)
  case Nil
  then show ?case by simp
next
  case (Cons a A)
  then show ?case
  proof cases 
    assume "member a B"
    then show ?thesis 
      using Cons.hyps Cons.prems by auto
  next
    assume "\<not>member a B"
    have "\<not> member a A"
      using Cons.prems by auto
    then have "\<not> member a (remove A B)" 
      by (metis DiffE member_iff remove_simp)
    then show ?thesis 
      using Cons.hyps Cons.prems by auto
  qed
qed
  
lemma set_size_equal: \<open>is_set A \<Longrightarrow> is_set B \<Longrightarrow> set_equal A B \<Longrightarrow> length A = length B\<close>
  apply (induct A arbitrary: B)
   apply simp 
  by (smt (verit, ccfv_threshold) member.simps(2) is_set.simps(2) is_set_size 
      length_Cons less_irrefl_nat list.distinct(1) nat.inject remove.simps(2) remove_equal 
      remove_is_set remove_size removent set_equal_def)

lemma sub_set_size: \<open>is_set A \<Longrightarrow> is_set B \<Longrightarrow> sub_set A B \<Longrightarrow> length A \<le> length B\<close>
proof (induct A arbitrary: B)
  case Nil
  then show ?case by simp
next
  case (Cons a A)
  then show ?case 
  proof cases
    assume "member a A"
    then show ?thesis
      by (meson Cons.prems(1) is_set.simps(2))
  next
    assume a:"\<not> member a A"
    then have "member a B" 
      by (metis Cons.prems(3) in_mono list.set_intros(1) member_iff sub_set_iff)
    moreover have "is_set A" 
      using Cons.prems(1) by auto
    moreover have "is_set (remove B [a])" 
      by (simp add: Cons.prems(2) remove_is_set)
    then have "length A \<le> length (remove B [a])" 
      by (metis Cons.hyps Cons.prems(3) a calculation(1) 
          calculation(2) remove.simps(2) sub_set_def sub_set_remove)
    then show ?thesis 
      using Cons.prems(2) calculation(1) is_set_size by fastforce
  qed
qed

lemma add_size: \<open>length (add a A) \<le> length A + 1\<close> 
proof cases
  assume "member a A"
  then show ?thesis 
    by (simp add: add_def)
next
  assume "\<not> member a A"
  then show ?thesis 
    by (metis One_nat_def add_def eq_imp_le list.size(4))
qed
(*\ISSET*)
end