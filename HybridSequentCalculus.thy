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


datatype 'a hybr_form 
  =  Pro 'a (\<open>PRO _\<close> [999] 999)
  | Nom nat (\<open>NOM _\<close> [998] 998)
  | Neg \<open>'a hybr_form\<close> (\<open>NOT _\<close> [900] 900)
  | Con \<open>'a hybr_form\<close> \<open>'a hybr_form\<close> (infixl "AND" 300)
  | Sat nat \<open>'a hybr_form\<close> (\<open>AT _ _\<close> [899] 899)
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
(*since nominals has linear order now we could just look at last element instead*)
fun nomMax where
  \<open>nomMax [] i = Suc i\<close> |
  \<open>nomMax (n # N) i = nomMax N (max i n)\<close>

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

fun nominalsNN :: \<open>(nat list \<times> nat) list \<Rightarrow> nat set\<close> where
  \<open>nominalsNN [] = {}\<close> |
  \<open>nominalsNN ((XS,n) # NN) = {n} \<union> (set XS) \<union> (nominalsNN NN)\<close>

fun nominalsNA :: \<open>(nat list \<times> 'a) list \<Rightarrow> nat set\<close> where
  \<open>nominalsNA [] = {}\<close> |
  \<open>nominalsNA ((XS,a) # NA) = (set XS) \<union> nominalsNA NA\<close>

fun nominalsNP :: \<open>(nat list \<times> ('a hybr_form)) list \<Rightarrow> nat set\<close> where
  \<open>nominalsNP [] = {}\<close> |
  \<open>nominalsNP ((XS,p) # NP) = (set XS) \<union> (nominalsForm p) \<union> (nominalsNP NP)\<close>

(*get all used nominals on one side of a sequent*)
abbreviation used where 
  \<open>used X Y Z Q \<equiv> nominalsNA X \<union> (nominalsNN Y) \<union> (nominalsNN Z) \<union> (nominalsNP Q)\<close>

(*merge functions replaces all occurences of a nominal with another
use when two nominals are found to denote the same world*)

primrec mergeN where
  \<open>mergeN [] na nb = []\<close> |
  \<open>mergeN (n # XS) na nb = (if na = n then nb else n) # mergeN XS na nb\<close>

fun mergeNN where
  \<open>mergeNN [] na nb = []\<close> |
  \<open>mergeNN ((XS,n) # NN) na nb = (mergeN XS na nb, if n = na then nb else n) # mergeNN NN na nb\<close>

fun mergeNA where
  \<open>mergeNA [] na nb = []\<close> |
  \<open>mergeNA ((XS,a) # NA) na nb = (mergeN XS na nb, a) # (mergeNA NA na nb)\<close>

fun nameCur where
  \<open>nameCur [] n = []\<close> |
  \<open>nameCur (([],a) # X) n = ([n],a) # nameCur X n\<close> |
  \<open>nameCur ((x # XS,a) # X) n = (x # XS,a) # nameCur X n\<close>

(*removes all statements about world refrenced by nw
if other worlds depend on being reached from nw, remove them too
use when it is shown that a world we assumed existed doesn't exist*)
function purge'
where
  \<open>purge' X A B Z ((XS,n) # C) X' A' B' Z' C' nw = 
    (let ((X'',A'',B'',Z'',C''),C''') =
      (if member nw XS then 
      (purge' X A B Z C [] [] [] [] [] n,C') 
       else ((X,A,B,Z,C),(XS,n) # C')) in
    purge' X'' A'' B'' Z'' C'' X' A' B' Z' C''' nw)\<close> |
  \<open>purge' X A B ((XS,n) # Z) [] X' A' B' Z' C' nw = 
    (if member nw XS then 
    purge' X A B Z [] X' A' B' Z' C' nw else
    purge' X A B Z [] X' A' B' ((XS,n) # Z') C' nw)\<close>|
  \<open>purge' X A ((XS,n) # B) [] [] X' A' B' Z' C' nw = 
    (if member nw XS then 
    purge' X A B [] [] X' A' B' Z' C' nw else
    purge' X A B [] [] X' A' ((XS,n) # B') Z' C' nw)\<close>|
  \<open>purge' X ((XS,a) # A) [] [] [] X' A' B' Z' C' nw = 
    (if member nw XS then 
    purge' X A [] [] [] X' A' B' Z' C' nw else
    purge' X A [] [] [] X' ((XS,a) # A') B' Z' C' nw)\<close>|
  \<open>purge' ((XS,a) # X) [] [] [] [] X' A' B' Z' C' nw = 
    (if member nw XS then 
    purge' X [] [] [] [] X' A' B' Z' C' nw else
    purge' X [] [] [] [] ((XS,a) # X') A' B' Z' C' nw)\<close>|
  \<open>purge' [] [] [] [] [] X' A' B' Z' C' nw = (X',A',B',Z',C')\<close> 
by pat_completeness auto
termination 
  apply (relation \<open>measure (\<lambda>(X,A,B,Z,C,_,_,_,_,_,_). size X + size A + size B + size Z + size C)\<close>)
  sorry
(*termination should be straight forward. Need to find out what fails*)

abbreviation purge where \<open>purge X A B Z C \<equiv> purge' X A B Z C [] [] [] [] []\<close>

fun match where
  \<open>match [] [] = True\<close> |
  \<open>match [] _ = False\<close> |
  \<open>match _ [] = False\<close> |
  \<open>match (n1 # XS) (n2 # YS) = (n1 = n2)\<close>

fun findAtom where
  \<open>findAtom [] n a = False\<close> |
  \<open>findAtom (([], b) # X) n a = findAtom X n a\<close> |
  \<open>findAtom ((n1 # XS, b) # X) n2 a = ((b = a \<and> n1 = n2) \<or> findAtom X n2 a)\<close>
  
fun pvr :: "(nat list \<times> 'a) list \<Rightarrow> (nat list \<times> 'a) list \<Rightarrow> (nat list \<times> nat) list \<Rightarrow> bool" where
  (*@a b on RSH holds if a=b*)
  \<open>pvr X A (([],n) # B) = pvr X A B\<close> |
  \<open>pvr X A ((n1 # XS,n2) # B) = (n1 = n2 \<or> pvr X A B)\<close> |
  (*A proposition on a world holds if it's on both LHS and RHS*)
  \<open>pvr X (([],a) # A) [] = (member ([],a) X \<or> pvr X A [])\<close> |
  \<open>pvr X ((n # XS,a) # A) [] =(findAtom X n a \<or> pvr X A [])\<close> |
  (*If we reach this point, we couldn't show that the sequent is valid*)
  \<open>pvr _ [] [] = False\<close>

function reach and witness where
  (*merge equal nominals*)
  \<open>reach X A B Z C (([],n) # Y) = reach (nameCur X n) (nameCur A n) (nameCur B n) 
                                        (nameCur Z n) (nameCur C n) (nameCur Y n)\<close> |
  \<open>reach X A B Z C ((n1 # XS,n2) # Y) = reach (mergeNA X n1 n2) (mergeNA A n1 n2) 
                                              (mergeNN B n1 n2) (mergeNN Z n1 n2) 
                                              (mergeNN C n1 n2) (mergeNN Y n1 n2)\<close> |

  (*find witnesses for possibility on RHS. 
   If no witness can be found, purge the node and try with next*)
  \<open>reach X A B Z ((XS,nw) # C) [] = (witness X A B C Z (XS,nw) Z 
                                    @(let (X',A',B',Z',C') = purge X A B Z C nw in 
                                      reach X' A' B' Z' C' []))\<close> |
  \<open>reach X A B _ [] [] = [(X,A,B)]\<close> |
  (*can't find witness if nothing is reachable*)
  \<open>witness X A B C Z2 (XS,nw) [] = []\<close> |
  (*if n2 is reachable from n, then check if p holds at n2*)
  \<open>witness X A B C Z2 (XS,nw) ((YS,n2) # Z) = ((if match XS YS 
                                                then reach X A B Z2 C [([nw],n2)]
                                                else [])
                                                @ witness X A B C Z2 (XS,nw) Z)\<close> 
  by pat_completeness auto
termination sorry

function atomize where
  (*match RHS*)
  \<open>atomize X A Y B Z C Q ((XS,Pro a) # P)     = atomize X ((XS,a) # A) Y B Z C Q P\<close> |
  \<open>atomize X A Y B Z C Q ((XS,Nom n) # P)   = atomize X A Y ((XS,n) # B) Z C Q P\<close> |
  \<open>atomize X A Y B Z C Q ((XS,Neg p) # P)     = atomize X A Y B Z C ((XS,p) # Q) P\<close> |
  \<open>atomize X A Y B Z C Q ((XS,Con p1 p2) # P) =((atomize X A Y B Z C Q ((XS,p1) # P)) 
                                                  @ (atomize X A Y B Z C Q ((XS,p2) # P)))\<close> |
  \<open>atomize X A Y B Z C Q ((XS,Sat n p) # P) = atomize X A Y B Z C Q ((n # XS,p) # P)\<close> |
  \<open>atomize X A Y B Z C Q ((XS,Pos p) # P)     =
          (let nw = fresh (used X Y Z ((XS,Pos p) # P) \<union> (used A B C Q)) in
          (atomize X A Y B Z ((XS,nw) # C) Q ((nw # XS,p) # P)))\<close> |
  (*match LHS*)
  \<open>atomize X A Y B Z C ((XS,Pro a) # Q) []    = atomize ((XS,a) # X) A Y B Z C Q []\<close> |
  \<open>atomize X A Y B Z C ((XS,Nom n) # Q) []  = atomize X A ((XS,n) # Y) B Z C Q []\<close> |
  \<open>atomize X A Y B Z C ((XS,Neg p) # Q) []    = atomize X A Y B Z C Q [(XS,p)]\<close> |
  \<open>atomize X A Y B Z C ((XS,Con p1 p2) # Q) []
        = atomize X A Y B Z C ((XS,p1) # (XS,p2) # Q) []\<close> |
  \<open>atomize X A Y B Z C ((XS,Sat n p) # Q) []= atomize X A Y B Z C ((n # XS,p) # Q) []\<close> |
  \<open>atomize X A Y B Z C ((XS,Pos p) # Q) []    =
          (let nw = fresh (used X Y Z Q \<union> (used A B C Q)) in
          (atomize X A Y B ((XS,nw) # Z) C ((nw # XS,p) # Q) []))\<close> |
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
definition prover where \<open>prover p \<equiv> eval1 (atomize [] [] [] [] [] [] [] [([],p)])\<close>

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

proposition \<open>prover ((AT (1) ((NOM 1) AND 
                     (AT (2) ((NOM 2) AND 
                     ((\<box>((Pro A) THEN ((NOT ((Pro A) THEN ((Pro B) THEN (Pro A)))) OR (Pro B)))) 
                      THEN ((\<box>(Pro A)) THEN \<box> (Pro B))))))))\<close>
  by eval

proposition \<open>prover ((AT (1) (NOT (\<diamond> NOM (1)))) THEN 
                    ((AT (1) (NOM (2) AND (Pro A))) THEN 
                     (AT (1) (NOT (\<diamond> NOM (2))))))\<close>
  by eval

proposition \<open>prover ((\<diamond>PRO A) THEN (\<diamond>PRO A))\<close>
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
))\<close> by eval

proposition \<open>\<not>(prover (
(\<diamond>(Pro A)) AND (\<diamond>((Pro A) AND (\<diamond>(Pro A)))) AND (\<box>((Pro A) AND (\<diamond>(Pro A)) AND
 (\<diamond>((\<diamond>(NOT (Pro A))) AND (\<box>(Pro B)))))) AND
(\<box>(NOT Pro B)) AND ((Pro A) IFF (Pro C)) AND (\<box>((Pro A) IFF (Pro C))) AND
((Pro K) OR (Pro L) OR (Pro M) OR (Pro N) OR (Pro F)) AND
((NOT Pro K) OR (NOT Pro L) OR (NOT Pro M)) AND
(\<box>\<box>\<box>((Pro K) IFF (Pro L)))
))\<close> by eval


proposition \<open>\<not>prover ((AT (2) (Pro A)) THEN (AT (1) (\<diamond> (AT (2) (Pro A)))))\<close>
  by eval

proposition \<open>\<not>prover ((Pro A) THEN (Sat (1) (Pro A)))\<close>
  by eval


(*export*)
definition \<open>main \<equiv> prover (Sat 1 (Neg (Con (Pro A) (Neg (Pro A)))))\<close>
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