theory HybridSequentCalculus imports Main
begin

primrec member where
  \<open>member _ [] = False\<close> |
  \<open>member m (n # A) = (m = n \<or> member m A)\<close>

lemma member_iff [iff]: \<open>member m A \<longleftrightarrow> m \<in> set A\<close>
  by (induct A) simp_all

datatype nom
  = Uni
  | Nml nat

(*give nominals linear order. used to convert from set to list*)
instantiation nom :: linorder
begin
fun less_eq_nom where
  \<open>less_eq_nom Uni n = True\<close> |
  \<open>less_eq_nom (Nml i) Uni = False\<close> |
  \<open>less_eq_nom (Nml i1) (Nml i2) = (i1 \<le> i2)\<close>

fun less_nom where
  \<open>less_nom Uni (Nml i) = True\<close> |
  \<open>less_nom Uni Uni = False\<close> |
  \<open>less_nom (Nml i) Uni = False\<close> |
  \<open>less_nom (Nml i1) (Nml i2) = (i1 < i2)\<close>

instance   
  proof
    fix x y z :: nom
    have 1:"(x < y) \<Longrightarrow> (x \<le> y \<and> \<not> y \<le> x)" by (induct x; induct y) simp_all
    have 2:"(x \<le> y \<and> \<not> y \<le> x) \<Longrightarrow> (x < y)" by (induct x; induct y) simp_all
    from 1 2 show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" by fast
    show "x \<le> x" by (induct x) simp_all
    show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" by (induct x; induct y; induct z) simp_all
    show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" by (induct x; induct y) simp_all
    show "x \<le> y \<or> y \<le> x" by (induct x; induct y) auto
  qed
end

datatype 'a hybr_form 
  =  Pro 'a 
  | Nom nom
  | Neg \<open>'a hybr_form\<close> 
  | Con \<open>'a hybr_form\<close> \<open>'a hybr_form\<close>
  | Sat nom \<open>'a hybr_form\<close>
  | Pos \<open>'a hybr_form\<close>

fun semantics :: \<open>('c \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
                  (nom \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> 'a hybr_form \<Rightarrow> bool\<close> where
  \<open>semantics R V G w (Pro a) = V w a\<close> |
  \<open>semantics R V G w (Nom n) = ((G n) = w)\<close> |
  \<open>semantics R V G w (Neg p) = (\<not> semantics R V G w p)\<close> |
  \<open>semantics R V G w (Con p1 p2) = (semantics R V G w p1 \<and> semantics R V G w p2)\<close> |
  \<open>semantics R V G w (Sat n p) = semantics R V G (G n) p\<close> |
  \<open>semantics R V G w (Pos p) = (\<exists>v. (R w v) \<and> (semantics R V G v p))\<close>

abbreviation \<open>sc X Y R V G w \<equiv> (\<forall> x \<in> X. semantics R V G w x) \<longrightarrow> (\<exists> y \<in> Y. semantics R V G w y)\<close>

(*find the maximal nominal in a list of nominals, and return one bigger than that*)
(*since nominals has linear order now we could just look at last element instead*)
fun nomMax where
  \<open>nomMax [] i = Nml (Suc i)\<close> |
  \<open>nomMax (Uni # N) i = nomMax N i\<close> |
  \<open>nomMax (Nml n # N) i = nomMax N (max i n)\<close>

(*return nominal not in a set of nominals*)
abbreviation fresh where \<open>fresh N \<equiv> nomMax (sorted_list_of_set N) 0\<close>

(*get a set of all used nominal, for different formula representations*)
fun nominalsForm where
  \<open>nominalsForm (Pro a) = {}\<close> |
  \<open>nominalsForm (Nom n) = {n}\<close> |
  \<open>nominalsForm (Neg p) = nominalsForm p\<close> |
  \<open>nominalsForm (Con p1 p2) = nominalsForm p1 \<union> (nominalsForm p2)\<close> |
  \<open>nominalsForm (Sat n p) = {n} \<union> (nominalsForm p)\<close> |
  \<open>nominalsForm (Pos p) = nominalsForm p\<close>

fun nominalsForms where
  \<open>nominalsForms [] = {}\<close> |
  \<open>nominalsForms (x # xs) = nominalsForm x \<union> (nominalsForms xs)\<close>

fun nominalsNN :: \<open>(nom \<times> nom) list \<Rightarrow> nom set\<close> where
  \<open>nominalsNN [] = {}\<close> |
  \<open>nominalsNN ((n1,n2) # NN) = {n1,n2} \<union> (nominalsNN NN)\<close>

fun nominalsNA :: \<open>(nom \<times> 'a) list \<Rightarrow> nom set\<close> where
  \<open>nominalsNA [] = {}\<close> |
  \<open>nominalsNA ((n,a) # NP) = {n} \<union> nominalsNA NP\<close>

fun nominalsNP :: \<open>(nom \<times> ('a hybr_form)) list \<Rightarrow> nom set\<close> where
  \<open>nominalsNP [] = {}\<close> |
  \<open>nominalsNP ((n,p) # NP) = {n} \<union> (nominalsForm p) \<union> (nominalsNP NP)\<close>

(*get all used nominals on one side of a sequent*)
abbreviation used where 
  \<open>used X Y Z Q \<equiv> nominalsNA X \<union> (nominalsNN Y) \<union> (nominalsNN Z) \<union> (nominalsForms Q)\<close>

(*merge functions replaces all occurences of a nominal with another
use when two nominals are found to denote the same world*)
fun mergeNN :: \<open>(nom \<times> nom) list \<Rightarrow> nom \<Rightarrow> nom \<Rightarrow> (nom \<times> nom) list\<close> where
  \<open>mergeNN [] na nb = []\<close> |
  \<open>mergeNN ((n1,n2) # NN) na nb = (let n3 = (if n1 = na then nb else n1) in 
                                  let n4 = (if n2 = na then nb else n2) in 
                                  (n3,n4) # (mergeNN NN na nb))\<close>

fun mergeNA :: \<open>(nom \<times> 'a) list \<Rightarrow> nom \<Rightarrow> nom \<Rightarrow> (nom \<times> 'a) list\<close> where
  \<open>mergeNA [] na nb = []\<close> |
  \<open>mergeNA ((n1,a) # NA) na nb = (if n1 = na then nb else n1, a) # (mergeNA NA na nb)\<close>

fun mergeP :: \<open>'a hybr_form \<Rightarrow> nom \<Rightarrow> nom \<Rightarrow> 'a hybr_form\<close> where
  \<open>mergeP (Pro a) na nb = Pro a\<close> |
  \<open>mergeP (Nom n1) na nb = Nom (if n1 = na then nb else n1)\<close> |
  \<open>mergeP (Neg p) na nb = mergeP p na nb\<close> |
  \<open>mergeP (Con p1 p2) na nb = Con (mergeP p1 na nb) (mergeP p2 na nb)\<close> |
  \<open>mergeP (Sat n p) na nb = Sat (if n = na then nb else n) (mergeP p na nb)\<close> |
  \<open>mergeP (Pos p) na nb = Pos (mergeP p na nb)\<close>

fun mergeNP :: \<open>(nom \<times>('a hybr_form)) list \<Rightarrow> nom \<Rightarrow> nom \<Rightarrow> 
                 (nom \<times> ('a hybr_form)) list\<close> where
  \<open>mergeNP [] na nb = []\<close> |
  \<open>mergeNP ((n1,p) # NP) na nb = (if n1 = na then nb else n1, mergeP p na nb) # (mergeNP NP na nb)\<close>

(*removes all statements about world refrenced by nw
if other worlds depend on being reached from nw, remove them too
use when it is shown that a world we assumed existed doesn't exist*)
function purge' :: 
\<open>(nom \<times> 'a) list \<Rightarrow> (nom \<times> 'a) list \<Rightarrow> (nom \<times> nom) list \<Rightarrow> (nom \<times> nom) list \<Rightarrow>
(nom \<times> nom) list \<Rightarrow>
(nom \<times> 'a) list \<Rightarrow> (nom \<times> 'a) list \<Rightarrow> (nom \<times> nom) list \<Rightarrow> (nom \<times> nom) list \<Rightarrow>
(nom \<times> nom) list \<Rightarrow> 
nom \<Rightarrow> 
((nom \<times> 'a) list \<times> (nom \<times> 'a) list \<times> (nom \<times> nom) list \<times> (nom \<times> nom) list \<times> (nom \<times> nom) list)\<close>
where
  \<open>purge' X A B Z ((n1,n2) # C) X' A' B' Z' C' nw = 
    (let ((X'',A'',B'',Z'',C''),C''') =
      (if n1 = nw then 
      (purge' X A B Z C [] [] [] [] [] n2,C') 
       else ((X,A,B,Z,C),(n1,n2) # C')) in
    purge' X'' A'' B'' Z'' C'' X' A' B' Z' C''' nw)\<close> |
  \<open>purge' X A B ((n1,n2) # Z) [] X' A' B' Z' C' nw = 
    (if n1 = nw then 
    purge' X A B Z [] X' A' B' Z' C' nw else
    purge' X A B Z [] X' A' B' ((n1,n2) # Z') C' nw)\<close>|
  \<open>purge' X A ((n1,n2) # B) [] [] X' A' B' Z' C' nw = 
    (if n1 = nw then 
    purge' X A B [] [] X' A' B' Z' C' nw else
    purge' X A B [] [] X' A' ((n1,n2) # B') Z' C' nw)\<close>|
  \<open>purge' X ((n1,a) # A) [] [] [] X' A' B' Z' C' nw = 
    (if n1 = nw then 
    purge' X A [] [] [] X' A' B' Z' C' nw else
    purge' X A [] [] [] X' ((n1,a) # A') B' Z' C' nw)\<close>|
  \<open>purge' ((n1,a) # X) [] [] [] [] X' A' B' Z' C' nw = 
    (if n1 = nw then 
    purge' X [] [] [] [] X' A' B' Z' C' nw else
    purge' X [] [] [] [] ((n1,a) # X') A' B' Z' C' nw)\<close>|
  \<open>purge' [] [] [] [] [] X' A' B' Z' C' nw = (X',A',B',Z',C')\<close> 
by pat_completeness auto
termination 
  apply (relation \<open>measure (\<lambda>(X,A,B,Z,C,_,_,_,_,_,_). 
                   \<Sum>p \<leftarrow> B @ Z @ C. \<Sum>q \<leftarrow> X @ A. (size p) + (size q))\<close>)
  apply auto
  sorry
(*termination should be straight forward. Need to find out what fails*)

abbreviation purge where \<open>purge X A B Z C \<equiv> purge' X A B Z C [] [] [] [] []\<close>

function pvr :: 
\<open>(nom \<times> 'a) list \<Rightarrow> (nom \<times> 'a) list \<Rightarrow> 
(nom \<times> nom) list \<Rightarrow> (nom \<times> nom) list \<Rightarrow>
(nom \<times> nom) list \<Rightarrow> (nom \<times> nom) list \<Rightarrow>
'a hybr_form list \<Rightarrow> 'a hybr_form list 
\<Rightarrow> bool\<close>
and witness where
  (*match formulas on RHS*)
  \<open>pvr X A Y B Z C Q (Sat n (Pro a) # P)     = pvr X ((n,a) # A) Y B Z C Q P\<close> |
  \<open>pvr X A Y B Z C Q (Sat n1 (Nom n2) # P)   = pvr X A Y ((n1,n2) # B) Z C Q P\<close> |
  \<open>pvr X A Y B Z C Q (Sat n (Neg p) # P)     = pvr X A Y B Z C (Sat n p # Q) P\<close> |
  \<open>pvr X A Y B Z C Q (Sat n (Con p1 p2) # P) =(pvr X A Y B Z C Q (Sat n p1 # P) 
                                             \<and> pvr X A Y B Z C Q (Sat n p2 # P))\<close> |
  \<open>pvr X A Y B Z C Q (Sat n1 (Sat n2 p) # P) = pvr X A Y B Z C Q (Sat n2 p # P)\<close> |
  \<open>pvr X A Y B Z C Q (Sat n (Pos p) # P)     =(let nw = fresh (used X Y Z P \<union> 
                                                              (used A B C Q)) in
                                              (pvr X A Y B Z ((n,nw) # C) Q (Sat nw p # P)))\<close> |
  \<open>pvr X A Y B Z C Q (p # P)                 = pvr X A Y B Z C Q (Sat Uni p # P)\<close> |
  (*match formulas on LHS*)
  \<open>pvr X A Y B Z C (Sat n (Pro a) # Q) []    = pvr ((n,a) # X) A Y B Z C Q []\<close> |
  \<open>pvr X A Y B Z C (Sat n1 (Nom n2) # Q) []  = pvr X A ((n1,n2) # Y) B Z C Q []\<close> |
  \<open>pvr X A Y B Z C (Sat n (Neg p) # Q) []    = pvr X A Y B Z C Q [Sat n p]\<close> |
  \<open>pvr X A Y B Z C (Sat n (Con p1 p2) # Q) []= pvr X A Y B Z C (Sat n p1 # (Sat n p2 # Q)) []\<close> |
  \<open>pvr X A Y B Z C (Sat n1 (Sat n2 p) # Q) []= pvr X A Y B Z C (Sat n2 p # Q) []\<close> |
  \<open>pvr X A Y B Z C (Sat n (Pos p) # Q) []    =(let nw = fresh (used X Y Z Q \<union> 
                                                              (used A B C Q)) in
                                              (pvr X A Y B ((n,nw) # Z) C (Sat nw p # Q) []))\<close> |
  \<open>pvr X A Y B Z C Q (p # P)                 = pvr X A Y B Z C (Sat Uni p # Q) []\<close> |
  (*merge equal nominals*)
  \<open>pvr X A ((n1,n2) # Y) B Z C [] [] = pvr (mergeNA X n1 n2) (mergeNA A n1 n2) 
                                           (mergeNN Y n1 n2) (mergeNN B n1 n2) 
                                           (mergeNN Z n1 n2) (mergeNN C n1 n2) [] []\<close> |

  (*find witnesses for possibility on RHS. 
   If no witness can be found, purge the node and try with next*)
  \<open>pvr X A [] B Z ((n,nw) # C) [] [] = (witness X A B Z C (n,nw) \<or>
                                       (let (X',A',B',Z',C') = purge X A B Z C nw in 
                                        pvr X' A' [] B' Z' C' [] []))\<close> |
  (*can't find witness if nothing is reachable*)
  \<open>witness X A B [] C (n,nw) = False\<close> |
  (*if n2 is reachable from n, then check if p holds at n2*)
  \<open>witness X A B ((n1,n2) # Z) C (n,nw) = (((n1 = n \<or> n1 = Uni) \<and> pvr X A [(nw,n2)] B Z C [] []) \<or>
                                            witness X A B Z C (n,nw))\<close> |

  (*@a b on RSH holds if a=b*)
  \<open>pvr X A [] ((n1,n2) # B) Z [] [] [] = (n1 = n2 \<or> pvr X A [] B Z [] [] [])\<close> |
  (*A proposition on a world holds if it's on both LHS and RHS*)
  \<open>pvr X ((n,a) # A) [] [] Z [] [] [] =(member (Uni,a) X \<or> member (n,a) X 
                                      \<or> pvr X A [] [] Z [] [] [])\<close> |
  (*If we reach this point, we couldn't show that the sequent is valid*)
  \<open>pvr X [] [] [] Z [] [] [] = False\<close>
  by sorry

(*General notes:
magic uni nominal. Represents forall. To prove something for at the uni world, you must use 
something from the uni world. Anything can be proven with statements from the uni world

We gather up statements about which nominals are equal in Y, then reduce everything to 1 nominal
per world by emptying the list

possibility on lhs should create a new accessible world. possibility on rhs can be witnessed by 
existing accessible world. nominals created by possibility will only show up in satisfaction
*)

end