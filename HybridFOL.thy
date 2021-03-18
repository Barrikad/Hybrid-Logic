theory HybridFOL imports Main
begin

datatype 'b nom
  = Uni
  | Nml 'b

datatype ('a, 'b) hybr_form 
  =  Pro 'a 
  | Nom \<open>'b nom\<close>
  | Neg \<open>('a,'b) hybr_form\<close> 
  | Con \<open>('a,'b) hybr_form\<close> \<open>('a,'b) hybr_form\<close>
  | Sat \<open>'b nom\<close> \<open>('a,'b) hybr_form\<close> 
  | Pos \<open>('a,'b) hybr_form\<close>

fun semantics :: \<open>('c \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
                  ('b nom \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> ('a, 'b) hybr_form \<Rightarrow> bool\<close> where
  \<open>semantics R V G w (Pro a) = V w a\<close> |
  \<open>semantics R V G w (Nom n) = ((G n) = w)\<close> |
  \<open>semantics R V G w (Neg p) = (\<not> semantics R V G w p)\<close> |
  \<open>semantics R V G w (Con p1 p2) = (semantics R V G w p1 \<and> semantics R V G w p2)\<close> |
  \<open>semantics R V G w (Sat n p) = semantics R V G (G n) p\<close> |
  \<open>semantics R V G w (Pos p) = (\<exists>v. (R w v) \<and> (semantics R V G v p))\<close>
 
fun fresh where
  \<open>fresh X A Y B Z C Q P = Uni\<close>

abbreviation \<open>sc X Y R V G w \<equiv> (\<forall> x \<in> X. semantics R V G w x) \<longrightarrow> (\<exists> y \<in> Y. semantics R V G w y)\<close>

primrec member where
  \<open>member _ [] = False\<close> |
  \<open>member m (n # A) = (m = n \<or> member m A)\<close>

lemma member_iff [iff]: \<open>member m A \<longleftrightarrow> m \<in> set A\<close>
  by (induct A) simp_all

function pvr where
  \<open>pvr X A Y B Z C Q (Sat n (Pro a) # P)     = pvr X ((n,a) # A) Y B Z C Q P\<close> |
  \<open>pvr X A Y B Z C Q (Sat n1 (Nom n2) # P)   = pvr X A Y ((n1,n2) # B) Z C Q P\<close> |
  \<open>pvr X A Y B Z C Q (Sat n (Neg p) # P)     = pvr X A Y B Z C (Sat n p # Q) P\<close> |
  \<open>pvr X A Y B Z C Q (Sat n (Con p1 p2) # P) =(pvr X A Y B Z C Q (Sat n p1 # P) 
                                             \<and> pvr X A Y B Z C Q (Sat n p2 # P))\<close> |
  \<open>pvr X A Y B Z C Q (Sat n1 (Sat n2 p) # P) = pvr X A Y B Z C Q (Sat n2 p # P)\<close> |
  \<open>pvr X A Y B Z C Q (Sat n (Pos p) # P)     = pvr X A Y B Z ((n,Uni) # X) Q (Sat Uni p # P)\<close> |
  (*need fresh noms*)
  \<open>pvr X A Y B Z C Q (p # P)                 = pvr X A Y B Z C Q (Sat Uni p # P)\<close> |

  \<open>pvr X A Y B Z C (Sat n (Pos p) # Q) []    = pvr X A Y B ((n,Uni) # Z) C (Sat Uni p # Q) []\<close> |
  (*need a way to generate fresh noms*)
  (*need to match rest of cases*)

  
  \<open>pvr X A ((n1,n2) # Y) B Z C [] [] = True\<close> |
  (*replace every occurence of n1 with n2*)

  \<open>pvr X A [] B Z ((n1,n2) # C) [] [] = True\<close> |
 (*for every other nominal n3 such that (n1,n3) in Z,
   replace n2 by n3 and check if returns true, 
   if not try next*)

  \<open>pvr X A [] ((n1,n2) # B) Z [] [] [] = (n1 = n2 \<or> pvr X A [] B Z [] [] [])\<close> |
  \<open>pvr X ((n,a) # A) [] [] Z [] [] [] =(member (Uni,a) X \<or> member (n,a) X 
                                      \<or> pvr X A [] [] Z [] [] [])\<close> |
  \<open>pvr X [] [] [] Z [] [] [] = False\<close>
  sorry

datatype ('a,'b) fol_form 
  = At 'b 'a
  | R 'b 'b
  | Eq 'b 'b
  | Negf \<open>('a,'b) fol_form\<close>
  | Conf \<open>('a,'b) fol_form\<close> \<open>('a,'b) fol_form\<close>
  | Fral 'b \<open>('a,'b) fol_form\<close>


fun f2h where
  \<open>f2h n (Pro a) = At n a\<close> |
  \<open>f2h n1 (Nom n2) = Eq n1 n2\<close> |
  \<open>f2h n (Neg p) = Negf (f2h n p)\<close> |
  \<open>f2h n (Con p1 p2) = Conf (f2h n p1) (f2h n p2)\<close> |
  \<open>f2h n1 (Sat n2 p) = f2h n2 p\<close> |
  \<open>f2h n (Pos p) = Negf (Fral Uni (Negf (Negf (Conf (R n Uni) (Negf (f2h Uni p))))))\<close>
  (*need fresh*)

end