theory SEAR
imports
  Pure
  Soft_Types

begin

text \<open>
Shulman's Sets, Elements, And Relations, formulated as a theory of multiply-sorted first-order logic.

The sorts are dependent; to handle this we use Alex Krauss's soft types library.
\<close>

declare[[eta_contract=false]]


section \<open>Logical foundations\<close>

subsection \<open>The sorts\<close>

typedecl tx \<comment>\<open>term expressions of the language\<close>

type_synonym sort = "tx type"

notation has_type (infix ":" 40)

axiomatization
  Set  :: sort and
  Elem :: "tx \<Rightarrow> sort" and
  Rel  :: "[tx, tx] \<Rightarrow> sort"


subsection \<open>Sorted FOL and set theory\<close>

typedecl bool

judgment Trueprop :: "bool \<Rightarrow> prop" ("(_)" 5)

axiomatization
  \<comment>\<open>Basic connectives\<close>
  conj :: "[bool, bool] \<Rightarrow> bool" (infix "\<and>" 30) and
  disj :: "[bool, bool] \<Rightarrow> bool" (infix "\<or>" 29) and
  not  :: "bool \<Rightarrow> bool" ("\<not> _" 59) and

  \<comment>\<open>Extra-logical connectives\<close>
  elem_of :: "[tx, tx] \<Rightarrow> bool" (infix "\<in>" 60) and
  eq      :: "[tx, tx] \<Rightarrow> bool" (infix "=" 60) and

  \<comment>\<open>Quantifiers\<close>
  forall_set  :: "(tx \<Rightarrow> bool) \<Rightarrow> bool" (binder "\<forall>" [10] 11) and
  exists_set  :: "(tx \<Rightarrow> bool) \<Rightarrow> bool" (binder "\<exists>" [10] 11) and
  forall_elem :: "[tx, tx \<Rightarrow> bool] \<Rightarrow> bool" and
  exists_elem :: "[tx, tx \<Rightarrow> bool] \<Rightarrow> bool" and
  forall_rel  :: "[tx, tx, tx \<Rightarrow> bool] \<Rightarrow> bool" and
  exists_rel  :: "[tx, tx, tx \<Rightarrow> bool] \<Rightarrow> bool"

syntax
  "_forall_elem" :: "[idt, tx, tx \<Rightarrow> bool] \<Rightarrow> bool" ("(\<forall>_: _./ _)" [0, 0, 10] 11)
  "_exists_elem" :: "[idt, tx, tx \<Rightarrow> bool] \<Rightarrow> bool" ("(\<exists>_: _./ _)" [0, 0, 10] 11)
  "_forall_rel"  :: "[idt, tx, tx, tx \<Rightarrow> bool] \<Rightarrow> bool" ("(\<forall>_: _ \<succ> _./ _)" [0, 0, 0, 10] 11)
  "_exists_rel"  :: "[idt, tx, tx, tx \<Rightarrow> bool] \<Rightarrow> bool" ("(\<exists>_: _ \<succ> _./ _)" [0, 0, 0, 10] 11)
translations
  "\<forall>x: X. P" \<rightleftharpoons> "CONST forall_elem X (\<lambda>x. P)"
  "\<exists>x: X. P" \<rightleftharpoons> "CONST exists_elem X (\<lambda>x. P)"
  "\<forall>\<phi>: A \<succ> B. P" \<rightleftharpoons> "CONST forall_rel A B (\<lambda>\<phi>. P)"
  "\<exists>\<phi>: A \<succ> B. P" \<rightleftharpoons> "CONST exists_rel A B (\<lambda>\<phi>. P)"


prop "\<exists>A. \<forall>R: A \<succ> A. \<not> R = S"
ML_val {* @{prop "\<exists>A. \<forall>R: A \<succ> A. \<not> R = S"} *}



end
