theory HybridSequentCalculus imports Main
begin

fun f :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>f 0 = (2)\<close> |
  \<open>f (Suc 0) = (4)\<close> |
  \<open>f _ = 2\<close>


primrec member where
  \<open>member _ [] = False\<close> |
  \<open>member m (n # A) = (m = n \<or> member m A)\<close>

lemma member_iff [iff]: \<open>member m A \<longleftrightarrow> m \<in> set A\<close>
  by (induct A) simp_all

datatype nom
  = Uni
  | Nml nat (\<open>NL _\<close> 999)

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
  =  Pro 'a (\<open>PRO _\<close> [999] 999)
  | Nom nom (\<open>NOM _\<close> [998] 998)
  | Neg \<open>'a hybr_form\<close> (\<open>NOT _\<close> [900] 900)
  | Con \<open>'a hybr_form\<close> \<open>'a hybr_form\<close> (infixl "AND" 300)
  | Sat nom \<open>'a hybr_form\<close> (\<open>AT _ _\<close> 110)
  | Pos \<open>'a hybr_form\<close> (\<open>\<diamond> _\<close> 800)

primrec semantics :: \<open>'c set \<Rightarrow> ('c \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
                  (nom \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> 'a hybr_form \<Rightarrow> bool\<close> where
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
  \<open>nomMax [] i = Nml (Suc i)\<close> |
  \<open>nomMax (Uni # N) i = nomMax N i\<close> |
  \<open>nomMax (Nml n # N) i = nomMax N (max i n)\<close>

(*return nominal not in a set of nominals*)
abbreviation fresh where \<open>fresh N \<equiv> nomMax (sorted_list_of_set N) 0\<close>

(*get a set of all used nominal, for different formula representations*)
primrec nominalsForm where
  \<open>nominalsForm (Pro a) = {}\<close> |
  \<open>nominalsForm (Nom n) = {n}\<close> |
  \<open>nominalsForm (Neg p) = nominalsForm p\<close> |
  \<open>nominalsForm (Con p1 p2) = nominalsForm p1 \<union> (nominalsForm p2)\<close> |
  \<open>nominalsForm (Sat n p) = {n} \<union> (nominalsForm p)\<close> |
  \<open>nominalsForm (Pos p) = nominalsForm p\<close>

primrec nominalsForms where
  \<open>nominalsForms [] = {}\<close> |
  \<open>nominalsForms (x # xs) = nominalsForm x \<union> (nominalsForms xs)\<close>

fun nominalsNN :: \<open>(nom \<times> nom) list \<Rightarrow> nom set\<close> where
  \<open>nominalsNN [] = {}\<close> |
  \<open>nominalsNN ((n1,n2) # NN) = {n1,n2} \<union> (nominalsNN NN)\<close>

fun nominalsNA :: \<open>(nom \<times> 'a) list \<Rightarrow> nom set\<close> where
  \<open>nominalsNA [] = {}\<close> |
  \<open>nominalsNA ((n,a) # NA) = {n} \<union> nominalsNA NA\<close>

fun nominalsNP :: \<open>(nom \<times> ('a hybr_form)) list \<Rightarrow> nom set\<close> where
  \<open>nominalsNP [] = {}\<close> |
  \<open>nominalsNP ((n,p) # NP) = {n} \<union> (nominalsForm p) \<union> (nominalsNP NP)\<close>

(*get all used nominals on one side of a sequent*)
abbreviation used where 
  \<open>used X Y Z Q \<equiv> nominalsNA X \<union> (nominalsNN Y) \<union> (nominalsNN Z) \<union> (nominalsNP Q)\<close>

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
  apply simp_all
  sorry
(*termination should be straight forward. Need to find out what fails*)

abbreviation purge where \<open>purge X A B Z C \<equiv> purge' X A B Z C [] [] [] [] []\<close>
  
fun pvr  where
  (*@a b on RSH holds if a=b*)
  \<open>pvr X A ((n1,n2) # B) = (n1 = n2 \<or> pvr X A B)\<close> |
  (*A proposition on a world holds if it's on both LHS and RHS*)
  \<open>pvr X ((n,a) # A) [] =(member (Uni,a) X \<or> member (n,a) X \<or> pvr X A [])\<close> |
  (*If we reach this point, we couldn't show that the sequent is valid*)
  \<open>pvr _ [] [] = False\<close>

function reach and witness where
  (*merge equal nominals*)
  \<open>reach X A B Z C ((n1,n2) # Y) = reach (mergeNA X n1 n2) (mergeNA A n1 n2) 
                                         (mergeNN B n1 n2) (mergeNN Z n1 n2) 
                                         (mergeNN C n1 n2) (mergeNN Y n1 n2)\<close> |

  (*find witnesses for possibility on RHS. 
   If no witness can be found, purge the node and try with next*)
  \<open>reach X A B Z ((n,nw) # C) [] = (witness X A B C Z (n,nw) Z 
                                    @(let (X',A',B',Z',C') = purge X A B Z C nw in 
                                      reach X' A' B' Z' C' []))\<close> |
  \<open>reach X A B _ [] [] = [(X,A,B)]\<close> |
  (*can't find witness if nothing is reachable*)
  \<open>witness X A B C Z2 (n,nw) [] = []\<close> |
  (*if n2 is reachable from n, then check if p holds at n2*)
  \<open>witness X A B C Z2 (n,nw) ((n1,n2) # Z) = ((if (n1 = n \<or> n1 = Uni) 
                                              then reach X A B Z2 C [(nw,n2)]
                                              else [])
                                              @ witness X A B C Z2 (n,nw) Z)\<close> 
  by pat_completeness auto
termination sorry

function atomize where
  (*match RHS*)
  \<open>atomize X A Y B Z C Q ((n,Pro a) # P)     = atomize X ((n,a) # A) Y B Z C Q P\<close> |
  \<open>atomize X A Y B Z C Q ((n1,Nom n2) # P)   = atomize X A Y ((n1,n2) # B) Z C Q P\<close> |
  \<open>atomize X A Y B Z C Q ((n,Neg p) # P)     = atomize X A Y B Z C ((n,p) # Q) P\<close> |
  \<open>atomize X A Y B Z C Q ((n,Con p1 p2) # P) =((atomize X A Y B Z C Q ((n,p1) # P)) 
                                              @ (atomize X A Y B Z C Q ((n,p2) # P)))\<close> |
  \<open>atomize X A Y B Z C Q ((n1,Sat n2 p) # P) = atomize X A Y B Z C Q ((n2,p) # P)\<close> |
  \<open>atomize X A Y B Z C Q ((n,Pos p) # P)     =
          (let nw = fresh (used X Y Z P \<union> (used A B C Q)) in
          (atomize X A Y B Z ((n,nw) # C) Q ((nw,p) # P)))\<close> |
  (*match LHS*)
  \<open>atomize X A Y B Z C ((n,Pro a) # Q) []    = atomize ((n,a) # X) A Y B Z C Q []\<close> |
  \<open>atomize X A Y B Z C ((n1,Nom n2) # Q) []  = atomize X A ((n1,n2) # Y) B Z C Q []\<close> |
  \<open>atomize X A Y B Z C ((n,Neg p) # Q) []    = atomize X A Y B Z C Q [(n,p)]\<close> |
  \<open>atomize X A Y B Z C ((n,Con p1 p2) # Q) []
        = atomize X A Y B Z C ((n,p1) # (n,p2) # Q) []\<close> |
  \<open>atomize X A Y B Z C ((n1,Sat n2 p) # Q) []= atomize X A Y B Z C ((n2,p) # Q) []\<close> |
  \<open>atomize X A Y B Z C ((n,Pos p) # Q) []    =
          (let nw = fresh (used X Y Z Q \<union> (used A B C Q)) in
          (atomize X A Y B ((n,nw) # Z) C ((nw,p) # Q) []))\<close> |
  \<open>atomize X A Y B Z C [] []                  = [(X,A,Y,B,Z,(rev C))]\<close>
  by pat_completeness auto
termination sorry
  (*by (relation \<open>measure (\<lambda>(_,_,_,_,_,_,Q,P). \<Sum>p \<leftarrow> Q @ P. (size p))\<close>) 
               (auto simp add: Let_def)*)

fun eval2 where
  \<open>eval2 [] = False\<close> |
  \<open>eval2 ((X,A,B) # XS) = (pvr X A B \<or> eval2 XS)\<close>

fun eval1 where
  \<open>eval1 [] = True\<close> |
  \<open>eval1 ((X,A,Y,B,Z,C) # XS) = (eval2 (reach X A B Z C Y) \<and> eval1 XS)\<close>

(*tautology definition*)
definition prover where \<open>prover p \<equiv> eval1 (atomize [] [] [] [] [] [] [] [(Uni,p)])\<close>

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
proposition \<open>prover (((Sat (Nml 1)  (Pos (Nom (Nml 2)))) AND (Sat (Nml 2) (Pro A))) 
                     THEN (Sat (Nml 1) (Pos (Pro A))))\<close>
  by eval

proposition \<open>prover (NOT (NOT Pro A AND Pro A))\<close>
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

proposition \<open>prover (NOT ((AT (Nml 1) (\<diamond> (NOM Nml 2))) 
             AND (AT (Nml 2) (Pro A)) AND (AT (Nml 1) (\<box> NOT Pro A))))\<close>
  by eval

proposition \<open>prover 
 ((AT (Nml 1) (NOM Nml 3)) THEN 
  ((AT (Nml 2) (Pro A)) OR (AT (Nml 1) (\<diamond> (AT (Nml 2) (NOT Pro A))))))\<close>
  by eval

proposition \<open>prover ((AT (Nml 1) (\<diamond> NOM Nml 2)) AND
                     (AT (Nml 2) (\<diamond> NOM Nml 3)) AND 
                     (AT (Nml 3) (Pro A)) THEN 
                     (AT (Nml 1) (\<diamond>(\<diamond> (Pro A)))))\<close>
  by eval

proposition \<open>prover ((AT (Nml 1) (\<diamond>\<diamond>\<diamond>\<diamond> Pro A)) THEN (AT (Nml 1) (\<diamond>\<diamond>\<diamond>\<diamond> Pro A)))\<close>
  by eval

proposition \<open>prover ((AT (Nml 1) ((NOM Nml 1) AND 
                     (AT (Nml 2) ((NOM Nml 2) AND 
                     ((\<box>((Pro A) THEN ((NOT ((Pro A) THEN ((Pro B) THEN (Pro A)))) OR (Pro B)))) 
                      THEN ((\<box>(Pro A)) THEN \<box> (Pro B))))))))\<close>
  by eval


(*invalid tests*)
proposition \<open>\<not>(prover (Pro A))\<close>
  by eval

proposition \<open>\<not>(prover (Con (Pro A) (Pro A)))\<close>
  by eval

proposition \<open>\<not>(prover (Con (Neg (Pro A)) (Pro A)))\<close>
  by eval

proposition \<open>\<not>(prover (Sat (Nml 1) (Con (Neg (Pro A)) (Pro A))))\<close>
  by eval

proposition \<open>\<not>(prover ( 
  NOT (Pro A AND Pro A) 
  AND (Pro C THEN Pro B) AND NOT (NOT Pro E THEN (Pro C OR NOT NOT Pro D))))\<close>
  by eval

proposition \<open>\<not>(prover ( 
NOT (Pro A AND Pro A) AND (Pro C THEN Pro B) AND
 (AT (Nml 1) (NOT (NOT Pro E THEN (Pro C OR NOT NOT Pro D)))) AND
 (AT (Nml 2) (AT (Nml 3) (Pro C)))
))\<close> by eval

proposition \<open>\<not>(prover (
(\<diamond>(Pro A)) AND (\<diamond>((Pro A) AND (\<diamond>(Pro A)))) AND (\<box>((Pro A) AND (\<diamond>(Pro A)) AND
 (\<diamond>((\<diamond>(NOT (Pro A))) AND (\<box>(Pro B)))))) AND
(\<box>(NOT Pro B)) AND ((Pro A) IFF (Pro C)) AND (\<box>((Pro A) IFF (Pro C))) AND
((Pro K) OR (Pro L) OR (Pro M) OR (Pro N) OR (Pro F)) AND
((NOT Pro K) OR (NOT Pro L) OR (NOT Pro M)) AND
(\<box>\<box>\<box>((Pro K) IFF (Pro L)))
))\<close> by eval

(*export*)
definition \<open>main \<equiv> prover (Sat Uni (Neg (Con (Pro A) (Neg (Pro A)))))\<close>
proposition main by eval
export_code main in Haskell

(*General notes:
magic uni nominal. Represents forall. To prove something for at the uni world, you must use 
something from the uni world. Anything can be proven with statements from the uni world

We gather up statements about which nominals are equal in Y, then reduce everything to 1 nominal
per world by emptying the list

possibility on lhs should create a new accessible world. possibility on rhs can be witnessed by 
existing accessible world. nominals created by possibility will only show up in satisfaction
*)

end