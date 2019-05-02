theory SEAR_old
imports FOL_Base

begin

text \<open>
Shulman's Sets, Elements, And Relations, formulated as a theory of many-sorted first-order logic.
\<close>

declare[[eta_contract=false]]


section \<open>Logical foundations\<close>

subsection \<open>The sorts\<close>

typedecl t \<comment>\<open>terms of the language\<close>
instance t :: expr ..

typedecl sort
instance sort :: expr ..

axiomatization
  has_type :: "[t, sort] \<Rightarrow> o" (infix ":" 40)

axiomatization
  Set  :: sort and
  Elem :: "t \<Rightarrow> sort" and
  Rel  :: "[t, t] \<Rightarrow> sort"


subsection \<open>Sorted FOL and set theory\<close>

no_notation
  All (binder "\<forall>" 10) and
  Ex  (binder "\<exists>" 10) and
  Ex1 (binder "\<exists>!" 10)
notation
  All (binder "ALL " 10) and
  Ex  (binder "EX " 10) and
  Ex1 (binder "EX! " 10)

text \<open>Quantifiers:\<close>

definition forall_set :: "(t \<Rightarrow> o) \<Rightarrow> o" (binder "\<forall>" [10] 11)
  where "\<forall>X. P X \<equiv> ALL X. (X: Set \<longrightarrow> P X)"

definition exists_set :: "(t \<Rightarrow> o) \<Rightarrow> o" (binder "\<exists>" [10] 11)
  where "\<exists>X. P X \<equiv> EX X. (X: Set \<and> P X)"

definition exists1_set :: "(t \<Rightarrow> o) \<Rightarrow> o" (binder "\<exists>!" [10] 11)
  where "\<exists>!X. P X \<equiv> EX! X. (X: Set \<and> P X)"

definition forall_elem :: "[t, t \<Rightarrow> o] \<Rightarrow> o"
  where "forall_elem X P \<equiv> ALL x. (x: Elem X \<longrightarrow> P x)"

definition exists_elem :: "[t, t \<Rightarrow> o] \<Rightarrow> o"
  where "exists_elem X P \<equiv> EX x. (x: Elem X \<and> P x)"

definition exists1_elem :: "[t, t \<Rightarrow> o] \<Rightarrow> o"
  where "exists1_elem X P \<equiv> EX! x. (x: Elem X \<and> P x)"

definition forall_rel :: "[t, t, t \<Rightarrow> o] \<Rightarrow> o"
  where "forall_rel A B P \<equiv> ALL \<phi>. (\<phi>: Rel A B \<longrightarrow> P \<phi>)"

definition exists_rel :: "[t, t, t \<Rightarrow> o] \<Rightarrow> o"
  where "exists_rel A B P \<equiv> EX \<phi>. (\<phi>: Rel A B \<and> P \<phi>)"

definition exists1_rel :: "[t, t, t \<Rightarrow> o] \<Rightarrow> o"
  where "exists1_rel A B P \<equiv> EX! \<phi>. (\<phi>: Rel A B \<and> P \<phi>)"

syntax
  "_forall_elem" :: "[idt, t, t \<Rightarrow> o] \<Rightarrow> o" ("(\<forall>_: _./ _)" [0, 0, 10] 11)
  "_exists_elem" :: "[idt, t, t \<Rightarrow> o] \<Rightarrow> o" ("(\<exists>_: _./ _)" [0, 0, 10] 11)
  "_exists1_elem" :: "[idt, t, t \<Rightarrow> o] \<Rightarrow> o" ("(\<exists>!_: _./ _)" [0, 0, 10] 11)
  "_forall_rel"  :: "[idt, t, t, t \<Rightarrow> o] \<Rightarrow> o" ("(\<forall>_: _ \<succ> _./ _)" [0, 0, 0, 10] 11)
  "_exists_rel"  :: "[idt, t, t, t \<Rightarrow> o] \<Rightarrow> o" ("(\<exists>_: _ \<succ> _./ _)" [0, 0, 0, 10] 11)
  "_exists1_rel"  :: "[idt, t, t, t \<Rightarrow> o] \<Rightarrow> o" ("(\<exists>!_: _ \<succ> _./ _)" [0, 0, 0, 10] 11)
translations
  "\<forall>x: X. P" \<rightleftharpoons> "CONST forall_elem X (\<lambda>x. P)"
  "\<exists>x: X. P" \<rightleftharpoons> "CONST exists_elem X (\<lambda>x. P)"
  "\<exists>!x: X. P" \<rightleftharpoons> "CONST exists1_elem X (\<lambda>x. P)"
  "\<forall>\<phi>: A \<succ> B. P" \<rightleftharpoons> "CONST forall_rel A B (\<lambda>\<phi>. P)"
  "\<exists>\<phi>: A \<succ> B. P" \<rightleftharpoons> "CONST exists_rel A B (\<lambda>\<phi>. P)"
  "\<exists>!\<phi>: A \<succ> B. P" \<rightleftharpoons> "CONST exists1_rel A B (\<lambda>\<phi>. P)"

text \<open>Basic formula constructors:\<close>

axiomatization
  elem_of :: "[t, t] \<Rightarrow> o" (infix "\<in>" 50) and
  holds   :: "[t, t, t] \<Rightarrow> o" ("(_'(_, _'))" [100, 0, 0])

section \<open>Axioms\<close>

axiomatization where
  existence: "\<exists>X. \<exists>x: X. x \<in> X" and
  comprehension: "A: Set \<Longrightarrow> B: Set \<Longrightarrow> \<exists>!\<phi>: A \<succ> B. \<phi>(x, y) \<longleftrightarrow> P x y"

thm exists1_rel_def

theorem
  assumes "A: Set" "B: Set"
  shows "\<exists>! \<phi> : A \<succ> B. \<phi>(x, y) \<longleftrightarrow> P x y"
proof (auto simp: exists1_rel_def ex1_def)
  obtain \<phi> where "\<phi>: Rel A B" using comprehension[OF assms] ex1_def by 

end
