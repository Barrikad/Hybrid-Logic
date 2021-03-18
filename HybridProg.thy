theory HybridProg imports Main
begin

(*arithmetic expression*)
datatype 'a artm = Var 'a | Num int | Plus \<open>'a artm\<close> \<open>'a artm\<close> | Minus \<open>'a artm\<close> \<open>'a artm\<close>

(*atomic proposition*)
datatype 'a atom = Assignment \<open>'a\<close> \<open>'a artm\<close> | Less \<open>'a artm\<close> \<open>'a artm\<close> | Equal \<open>'a artm\<close> \<open>'a artm\<close>

(*formulas*)
datatype ('a,'b) formula = Nom 'b | Atom \<open>'a atom\<close> | Satisfaction 'b \<open>('a,'b) formula\<close>
  | Possibility \<open>('a,'b) formula\<close> | Neg \<open>('a,'b) formula\<close> | Imp \<open>('a,'b) formula\<close> \<open>('a,'b) formula\<close>
  | And \<open>('a,'b) formula\<close> \<open>('a,'b) formula\<close>

(*semantics of arithmetic expressions*) 
fun optionPlus :: \<open>int option \<Rightarrow> int option \<Rightarrow> int option\<close> where
  \<open>optionPlus None _ = None\<close> |
  \<open>optionPlus _ None = None\<close> |
  \<open>optionPlus (Some i1) (Some i2) = Some (i1 + i2)\<close>

fun optionMinus :: \<open>int option \<Rightarrow> int option \<Rightarrow> int option\<close> where
  \<open>optionMinus None _ = None\<close> |
  \<open>optionMinus _ None = None\<close> |
  \<open>optionMinus (Some i1) (Some i2) = Some (i1 - i2)\<close>

fun artmSemantics :: \<open>('a,int) map \<Rightarrow> 'a artm \<Rightarrow> int option\<close> where
  \<open>artmSemantics mem (Var v) = mem v\<close> |
  \<open>artmSemantics mem (Num i) = Some i\<close> |
  \<open>artmSemantics mem (Plus a1 a2) = optionPlus (artmSemantics mem a1) (artmSemantics mem a2)\<close> |
  \<open>artmSemantics mem (Minus a1 a2) = optionMinus (artmSemantics mem a1) (artmSemantics mem a2)\<close>

(*semantics of atoms*)
fun optionLess :: \<open>int option \<Rightarrow> int option \<Rightarrow> bool\<close> where
  \<open>optionLess None _ = False\<close> |
  \<open>optionLess _ None = False\<close> |
  \<open>optionLess (Some i1) (Some i2) = (i1 < i2)\<close> 

fun optionEqual :: \<open>int option \<Rightarrow> int option \<Rightarrow> bool\<close> where
  \<open>optionEqual None _ = False\<close> |
  \<open>optionEqual _ None = False\<close> |
  \<open>optionEqual (Some i1) (Some i2) = (i1 = i2)\<close> 

fun atomSemantics :: \<open>('a,int) map \<Rightarrow> ('a,int) map \<Rightarrow> 'a atom \<Rightarrow> bool\<close> where
  \<open>atomSemantics memOld memNew (Less a1 a2) = 
    optionLess (artmSemantics memOld a1) (artmSemantics memOld a2)\<close> |
  \<open>atomSemantics memOld memNew (Equal a1 a2) = 
    optionEqual (artmSemantics memOld a1) (artmSemantics memOld a2)\<close> |
  \<open>atomSemantics memOld memNew (Assignment v a) = 
    ((memNew v \<noteq> None) \<and>
    (memNew v = artmSemantics memOld a))\<close>

(*semantics of formulas*)
function formulaSemantics :: \<open>('b,('a,'b) formula) map \<Rightarrow> ('b,'b set) map \<Rightarrow>
                         ('a,int) map \<Rightarrow> ('a,int) map \<Rightarrow> 'b \<Rightarrow> ('a,'b) formula \<Rightarrow> bool\<close> where
  \<open>formulaSemantics M R memOld memNew w (Nom w1) = (w = w1)\<close> |
  \<open>formulaSemantics M R memOld memNew w (Atom a) = atomSemantics memOld memNew a\<close> |
  \<open>formulaSemantics M R memOld memNew w (Neg f) = (\<not> formulaSemantics M R memOld memNew w f)\<close> |
  \<open>formulaSemantics M R memOld memNew w (Imp f1 f2) = 
    (formulaSemantics M R memOld memNew w f1 \<longrightarrow> formulaSemantics M R memOld memNew w f2)\<close> |
  \<open>formulaSemantics M R memOld memNew w (And f1 f2) = 
    (formulaSemantics M R memOld memNew w f1 \<and> formulaSemantics M R memOld memNew w f2)\<close> |
  \<open>formulaSemantics M R memOld memNew w (Satisfaction w1 f) = \<close>


end