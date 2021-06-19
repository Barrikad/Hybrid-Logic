theory HybridSC2 imports Main ListSet
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
  case (Cons a N)
  then have \<open>a = n \<or> member n N\<close>
      by (metis member.simps(2))
  then show ?case 
    using Cons lmax_def by auto
qed simp
  
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

fun nominalsNNSP where
  \<open>nominalsNNSP [] = []\<close> |
  \<open>nominalsNNSP ((n,ns,p) # NNSP) = nominalsNNSP NNSP U add n (ns U nominalsForm p)\<close>

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

lemma NNSP_is_set: \<open>is_set (nominalsNNSP NNSP)\<close>
proof (induct NNSP)
  case Nil
  then show ?case by simp
next
  case (Cons a NNSP)
  then show ?case 
    by (metis list.discI list.inject nominalsNNSP.elims union_is_set)
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

fun mergeNNSP where
  \<open>mergeNNSP [] na nb = []\<close> |
  \<open>mergeNNSP ((n,ns,p) # R) na nb = 
    (if n = na then nb else n, mergeNS ns na nb, mergeP p na nb) # (mergeNNSP R na nb)\<close>

fun clear where
  \<open>clear [] = []\<close> |
  \<open>clear ((n,ns,p) # R) = (n,[],p) # clear R\<close>

fun saturate' where
  \<open>saturate' R' [] ns = None\<close> |
  \<open>saturate' R' ((n,ms,p) # R) ns = (
    case remove ns ms of
      []      \<Rightarrow> saturate' (R' @ [(n,ms,p)]) R ns
    | (m # _) \<Rightarrow> Some (n,m,p,clear (R' @ R),R' @ [(n,m # ms,p)] @ R))\<close>

abbreviation saturate where \<open>saturate R ns \<equiv> saturate' [] R ns\<close>

lemma sat_empty: \<open>saturate [] ns = None\<close>
  by (simp)
              
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
  nominalsNN LP U nominalsNN RP U nominalsNNSP R U nominalsNP Q U nominalsNP P\<close>
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

private fun pos_countNNSP where
  \<open>pos_countNNSP [] = 0\<close> |                                          
  \<open>pos_countNNSP ((_,_,p) # NNSP) = pos_count p + pos_countNNSP NNSP\<close>


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

  \<open>sv LA RA RN LP RP R Q ((n,Pos p) # P) = 
    sv LA RA RN LP RP ((n,[],p) # R) Q P\<close>|

  (*match LHS*)
  \<open>sv LA RA RN LP RP R ((n,Pro a) # Q) [] = 
    sv ((n,a) # LA) RA RN LP RP R Q []\<close> |

  \<open>sv LA RA RN LP RP R ((n1,Nom n2) # Q) [] = 
    sv (mergeNA LA n1 n2) (mergeNA RA n1 n2) (mergeNN RN n1 n2) 
      (mergeNN LP n1 n2) (mergeNN RP n1 n2) (mergeNNSP R n1 n2) (mergeNP Q n1 n2) []\<close> |

  \<open>sv LA RA RN LP RP R ((n,Neg p) # Q) [] = 
    sv LA RA RN LP RP R Q [(n,p)]\<close> |

  \<open>sv LA RA RN LP RP R ((n,Con p1 p2) # Q) []= 
    sv LA RA RN LP RP R ((n,p1) # (n,p2) # Q) []\<close> |

  \<open>sv LA RA RN LP RP R ((n1,Sat n2 p) # Q) [] = 
    sv LA RA RN LP RP R ((n2,p) # Q) []\<close> |

  \<open>sv LA RA RN LP RP R ((n,Pos p) # Q) [] = (
    let nw = fresh (
      nominalsNA LA U nominalsNA RA U nominalsNN RN U nominalsNN LP U 
      nominalsNN RP U nominalsNNSP R U nominalsNP ((n,Pos p) # Q)) 
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
          nominalsNN LP U nominalsNN RP U nominalsNNSP R)
      of
        None \<Rightarrow> (common LA RA \<or> common LP RP \<or> reflect RN)
      | Some (n,m,p,R',R'') \<Rightarrow> 
          (sv LA RA RN LP ((n,m) # RP) R' [] [] \<and> sv LA RA RN LP RP R' [] [(m,p)]) 
          \<or> sv LA RA RN LP RP R'' [] [])\<close> 
  by pat_completeness simp_all
(*size definition for proving termination of sv*)
termination sorry

definition prover where 
  \<open>prover p \<equiv> sv [] [] [] [] [] [] [] [(fresh (nominalsForm p),p)]\<close>

end

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
    (\<exists> (n,ns,p) \<in> set R. 
      (\<exists> w. RE (G n) w \<and> semantics RE V G w p)) \<or>
    (\<exists> (n1,n2) \<in> set RP. RE (G n1) (G n2)) \<or>
    (\<exists> (n1,n2) \<in> set RN. (G n1) = (G n2)) \<or>
    (\<exists> (n,a) \<in> set RA. V (G n) a)
  )\<close>


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
  (AT 1 NOM 4) THEN (AT 2 \<diamond> PRO A) OR ((NOT ((AT 2 \<diamond> NOM 3) AND AT 3 PRO A) AND NOT 
  ((AT 2 \<diamond> NOM 4) AND AT 4 PRO A))))\<close>
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

proposition \<open>\<not>(sv [] [] [] [] [] [] [(1,\<diamond> NOM 2)] [(1,\<diamond> AT 1 (NOT (\<diamond> PRO A)))])\<close>
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

proposition \<open>\<not>prover (AT 1 (\<diamond> ((PRO A OR NOT PRO A) OR NOT (AT 1 \<diamond> NOM 2))))\<close>
  by eval

(*export
definition \<open>main \<equiv> prover (Sat 1 (Neg (Con (Pro A) (Neg (Pro A)))))\<close>
proposition main by eval
export_code main in Haskell*)

end