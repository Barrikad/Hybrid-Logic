theory HybridSC3 imports Main
begin

datatype 'a hybr_form 
  =  Pro 'a (\<open>PRO _\<close> [999] 999)
  | Nom nat (\<open>NOM _\<close> [998] 998)
  | Neg \<open>'a hybr_form\<close> (\<open>NOT _\<close> [900] 900)
  | Con \<open>'a hybr_form\<close> \<open>'a hybr_form\<close> (infixl "AND" 300)
  | Sat nat \<open>'a hybr_form\<close> (\<open>AT _ _\<close> [899]  899)
  | Pos \<open>'a hybr_form\<close> (\<open>\<diamond> _\<close> [800] 800)

primrec maxnomP where
  \<open>maxnomP mn (Pro a) = mn\<close> |
  \<open>maxnomP mn (Nom n) = max mn n\<close> |
  \<open>maxnomP mn (Neg p) = maxnomP mn p\<close> |
  \<open>maxnomP mn (Con p1 p2) = max (maxnomP mn p1) (maxnomP mn p2)\<close> |
  \<open>maxnomP mn (Sat n p) = max n (maxnomP mn p)\<close> |
  \<open>maxnomP mn (Pos p) = maxnomP mn p\<close> 
  
primrec mergeP where
  \<open>mergeP (Pro a) na nb = Pro a\<close> |
  \<open>mergeP (Nom n) na nb = Nom (if n = na then nb else n)\<close> |
  \<open>mergeP (Neg p) na nb = Neg (mergeP p na nb)\<close> |
  \<open>mergeP (Con p1 p2) na nb = Con (mergeP p1 na nb) (mergeP p2 na nb)\<close> |
  \<open>mergeP (Sat n p) na nb = Sat (if n = na then nb else n) (mergeP p na nb)\<close> |
  \<open>mergeP (Pos p) na nb = Pos (mergeP p na nb)\<close>

fun mergeNP where
  \<open>mergeNP [] na nb = []\<close> |
  \<open>mergeNP ((n,p) # NP) na nb = (if n = na then nb else n, mergeP p na nb) # (mergeNP NP na nb)\<close>

(*validity checks*)
(*Check if any of the pairs in a list contains two of the same element*)
fun reflect where
  \<open>reflect [] = False\<close> |
  \<open>reflect ((n1,Nom n2) # B) = (n1 = n2 \<or> reflect B)\<close> |
  \<open>reflect (_ # B) = reflect B\<close>

lemma reflect_iff[iff]: \<open>reflect nn \<longleftrightarrow> (\<exists> n. (n,Nom n) \<in> set nn)\<close> 
  apply (induct nn)
   apply simp 
  by (smt (z3) insert_iff list.distinct(1) list.inject list.set(2) 
      reflect.elims(1) reflect.simps(2))

primrec member where
  \<open>member x [] = False\<close> |
  \<open>member x (y # xs) = (x = y \<or> member x xs)\<close>

lemma member_iff[iff]: \<open>member x xs \<longleftrightarrow> x \<in> set xs\<close>
  by (induct xs) simp_all

primrec common where
  \<open>common [] ys = False\<close> |
  \<open>common (x # xs) ys = (member x ys \<or> common xs ys)\<close>

lemma common_iff[iff]: \<open>common xs ys \<longleftrightarrow> set xs \<inter> set ys \<noteq> {}\<close>
  by (induct xs) simp_all

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

function sv where
  (*match RHS*)
  \<open>sv mn cn LA RA Y X Q ((n,Pro a) # P) = 
    sv mn cn LA ((n,Pro a) # RA) Y X Q P\<close> |

  \<open>sv mn cn LA RA Y X Q ((n1,Nom n2) # P) = 
    sv mn cn LA ((n1,Nom n2) # RA) Y X Q P\<close> |

  \<open>sv mn cn LA RA Y X Q ((n,Neg p) # P) = 
    sv mn cn LA RA Y X ((n,p) # Q) P\<close> |

  \<open>sv mn cn LA RA Y X Q ((n,Con p1 p2) # P) =
    ((sv mn cn LA RA Y X Q ((n,p1) # P)) \<and> (sv mn cn LA RA Y X Q ((n,p2) # P)))\<close> |

  \<open>sv mn cn LA RA Y X Q ((n1,Sat n2 p) # P) = 
    sv mn cn LA RA Y X Q ((n2,p) # P)\<close> |

  \<open>sv mn cn LA RA Y X Q ((n,Pos p) # P) = 
    sv mn cn LA RA Y ((n,p) # X) Q P\<close>|

  (*match LHS*)
  \<open>sv mn cn LA RA Y X ((n,Pro a) # Q) [] = 
    sv mn cn ((n,Pro a) # LA) RA Y X Q []\<close> |

  \<open>sv mn cn LA RA Y X ((n1,Nom n2) # Q) [] = 
    sv mn cn (mergeNP LA n1 n2) (mergeNP RA n1 n2) (mergeNP Y n1 n2) (mergeNP X n1 n2) (mergeNP Q n1 n2) []\<close> |

  \<open>sv mn cn LA RA Y X ((n,Neg p) # Q) [] = 
    sv mn cn LA RA Y X Q [(n,p)]\<close> |

  \<open>sv mn cn LA RA Y X ((n,Con p1 p2) # Q) []= 
    sv mn cn LA RA Y X ((n,p1) # (n,p2) # Q) []\<close> |

  \<open>sv mn cn LA RA Y X ((n1,Sat n2 p) # Q) [] = 
    sv mn cn LA RA Y X ((n2,p) # Q) []\<close> |

  \<open>sv mn cn LA RA Y X ((n,Pos p) # Q) [] =
    sv (mn + 1) cn ((n,Pos (Nom mn)) # LA) RA Y X ((mn,p) # Q) []\<close> |
(*-------Try all relevant assignments of nominals to possibility on RHS-----------
If no assignment can be made, check if current sequent is a tautology.
Else we can process a statement @n\<diamond>P.
  Find a nominal m to witness the statement
  Check if the sequent with @n\<diamond>P removed fulfills both @n\<diamond>m and @mP
  Lastly, try another assignment. Remember that we already tried m.*)
  \<open>sv mn cn LA RA Y ((n,p) # X) [] [] = (
    if cn < mn 
    then (
      sv mn 0 LA ((n,Pos (Nom cn)) # RA) [] (Y @ X) [] [] \<and>
      sv mn 0 LA RA [] (Y @ X) [] [(cn,p)]) \<or> 
      sv mn (cn + 1) LA RA Y ((n,p) # X) [] []
    else sv mn 0 LA RA ((n,p) # Y) X [] [])\<close> |
  \<open>sv mn cn LA RA Y [] [] [] = (reflect RA \<or> common LA RA)\<close>
  by pat_completeness simp_all
(*size definition for proving termination of sv*)
termination sorry

definition prover where 
  \<open>prover p \<equiv> (let mn = maxnomP 0 p in sv (mn + 2) 0 [] [] [] [] [] [(mn + 1,p)])\<close>

primrec semantics :: \<open>('c \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
                  (nat \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> 'a hybr_form \<Rightarrow> bool\<close> where
  \<open>semantics RE V G w (Pro a) = V w a\<close> |
  \<open>semantics RE V G w (Nom n) = ((G n) = w)\<close> |
  \<open>semantics RE V G w (Neg p) = (\<not> semantics RE V G w p)\<close> |
  \<open>semantics RE V G w (Con p1 p2) = (semantics RE V G w p1 \<and> semantics RE V G w p2)\<close> |
  \<open>semantics RE V G w (Sat n p) = semantics RE V G (G n) p\<close> |
  \<open>semantics RE V G w (Pos p) = (\<exists> v. (RE w v) \<and> (semantics RE V G v p))\<close>

definition \<open>sc RE V G LA RA Y X Q P \<equiv> 
  (
    (\<forall> (n,p) \<in> set Q \<union> set LA. semantics RE V G (G n) p)
  ) \<longrightarrow> (
    (\<exists> (n,p) \<in> set P \<union> set RA. semantics RE V G (G n) p) \<or>
    (\<exists> (n,p) \<in> set Y \<union> set X. semantics RE V G (G n) (Pos p))
  )\<close>

definition \<open>
  consistent_soundness mn cn LA RA Y X Q P \<equiv>
  (cn \<noteq> 0 \<longleftrightarrow> Q = [] \<and> P = []) \<and>
  (\<forall> (n,p) \<in> set LA \<union> set RA \<union> set Y \<union> set X \<union> set Q \<union> set P. mn > n \<and> mn > maxnomP 0 p)\<close>

theorem soundness: \<open>
  consistent_soundness mn cn LA RA Y X Q P \<Longrightarrow> 
  sv mn cn LA RA Y X Q P \<Longrightarrow>
  (\<forall> RE V G. sc RE V G LA RA Y X Q P)\<close>
proof (induct Y X Q P rule: sv.induct)
  case (1 mn cn LA RA Y X Q n a P)
  then show ?case sorry
next
  case (2 mn cn LA RA Y X Q n1 n2 P)
  then show ?case sorry
next
  case (3 mn cn LA RA Y X Q n p P)
  then show ?case sorry
next
  case (4 mn cn LA RA Y X Q n p1 p2 P)
  then show ?case sorry
next
  case (5 mn cn LA RA Y X Q n1 n2 p P)
  then show ?case sorry
next
  case (6 mn cn LA RA Y X Q n p P)
  then show ?case sorry
next
  case (7 mn cn LA RA Y X n a Q)
  then show ?case sorry
next
  case (8 mn cn LA RA Y X n1 n2 Q)
  then show ?case sorry
next
  case (9 mn cn LA RA Y X n p Q)
  then show ?case sorry
next
  case (10 mn cn LA RA Y X n p1 p2 Q)
  then show ?case sorry
next
  case (11 mn cn LA RA Y X n1 n2 p Q)
  then show ?case sorry
next
  case (12 mn cn LA RA Y X n p Q)
  then show ?case sorry
next
  case (13 mn cn LA RA Y n p X)
  then show ?case sorry
next
  case (14 mn cn LA RA Y)
  then show ?case sorry
qed

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

proposition \<open>\<not>(sv 3 0 [] [] [] [] [(1,\<diamond> NOM 2)] [(1,\<diamond> AT 1 (NOT (\<diamond> PRO A)))])\<close>
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

value \<open>maxnomP 0 ((Pro A) THEN (Sat (1) (Pro A)))\<close>

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