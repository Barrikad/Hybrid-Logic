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

primrec union (infixr \<open>U\<close> 100) where
  \<open>union A [] = A\<close> |
  \<open>union A (b # B) = (
    if member b A
    then union A B
    else union (b # A) B)\<close>

lemma union_simp [simp]: \<open>union A B = C \<longrightarrow> set A \<union> set B = set C\<close>
proof (induct B arbitrary: A C)
case Nil
  then show ?case by simp
next
  case (Cons a B)
  then show ?case 
    by (metis Un_insert_left Un_insert_right insert_absorb list.simps(15) member_iff union.simps(2))
qed 

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

(*size definition for proving termination of atomize*)
primrec size' :: \<open>'a hybr_form \<Rightarrow> nat\<close> where
  \<open>size' (Pro a) = Suc 0\<close> |
  \<open>size' (Nom n) = Suc 0\<close> |
  \<open>size' (Neg p) = Suc (size' p)\<close> |
  \<open>size' (Con p1 p2) = Suc (size' p1 + size' p2)\<close> |
  \<open>size' (Sat n p) = Suc (Suc (size' p))\<close> |
  \<open>size' (Pos p) = Suc (Suc (size' p))\<close>

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
(*since nominals has linear order now we could just look at last element instead*)
fun nomMax where
  \<open>nomMax [] i = Suc i\<close> |
  \<open>nomMax (n # N) i = nomMax N (max i n)\<close>

(*return nominal not in a set of nominals*)
abbreviation fresh where \<open>fresh N \<equiv> nomMax N 0\<close>

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
  \<open>nominalsNSNP ((n,ns,p) # NSNP) = add n (union ns (union (nominalsForm p) (nominalsNSNP NSNP)))\<close>

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
  

lemma sat_consistent: 
  \<open>saturate R ns = None \<or> (saturate R ns = Some (n,m,p,R1,R2) \<and> (\<exists> ms. member (n,m # ms,p) R2))\<close>
proof (induct R arbitrary: n m p R1 R2)
  case Nil
  then show ?case by simp
next
  case (Cons a R)
  assume "(\<And>n m p R1 R2.
           saturate R ns = HybridSequentCalculus.option.None \<or>
           saturate R ns = HybridSequentCalculus.option.Some (n, m, p, R1, R2) \<and>
           (\<exists>ms. member (n, m # ms, p) R2))"
  then show ?case
  proof 
    assume 1:"saturate R ns = None"
    have "\<exists> x ys q. a = (x,ys,q)" by (meson prod_cases3)
    then obtain x ys q where 2:\<open>a = (x,ys,q)\<close> by auto
      then have \<open>remove ns ys = [] \<longrightarrow> saturate ((x,ys,q) # R) ns = None\<close> using 1 sorry
    then show ?case sorry
    next
      assume "saturate R ns = Some (n, m, p, R1, R2) \<and> (\<exists>ms. member (n, m # ms, p) R2)"
      then show ?case sorry
    qed
qed

fun missing' where
  \<open>missing' ms [] = 0\<close> |
  \<open>missing' ms (n # ns) = (if \<not>member n ms then Suc (missing' ms ns) else missing' ms ns)\<close>

fun missing where
  \<open>missing [] ns = 0\<close> |
  \<open>missing ((_,ms,_) # R) ns = missing' ms ns + missing R ns\<close>

lemma saturate_size1: \<open>
  saturate R ns = Some (n,m,p,R',R'') \<Longrightarrow>
  Suc (size R') = size R\<close>
proof (induct R arbitrary: R' R'' ns n m p)
  case Nil
  then show ?case 
    by (metis HybridSequentCalculus.option.distinct(1) sat_empty)
next
  case (Cons a R)
  assume a1: "(\<And>R' R'' ns n m p.
           saturate R ns = Some (n, m, p, R', R'') \<Longrightarrow>
           Suc (length R') = length R)"
  assume a2: "saturate (a # R) ns = Some (n, m, p, R', R'')"
  then have \<open>\<exists> ms. member (n,m # ms,p) (a # R)\<close> sorry
  from a1 a2 have "Suc (length R') = length (a # R)"  sorry
  then show ?case by simp
qed

lemma saturate_size2: \<open>
  saturate R ns = Some (n,m,p,R',R'') \<Longrightarrow>
  missing R'' ns < missing R ns\<close>
proof (induct R arbitrary: R' R'' ns n m p)
  case Nil
  then show ?case
    by (metis HybridSequentCalculus.option.distinct(1) sat_empty)
next
  case (Cons a R)
  then show ?case sorry
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
termination 
  (*apply (relation \<open>measure (\<lambda>(_,_,_,_,_,_,Q,P). \<Sum>(_,p) \<leftarrow> Q @ P. size' p)\<close>) *)
  sorry

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