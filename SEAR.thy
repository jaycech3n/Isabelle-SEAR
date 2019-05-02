theory SEAR
imports FOL_Base

begin

text \<open>
Shulman's Sets, Elements, And Relations, formulated as a theory of many-sorted first-order logic.
\<close>

declare[[eta_contract=false]]


section \<open>Logical foundations\<close>

subsection \<open>Meta\<close>

text \<open>For meta-level nondependent typing: terms are divided into three meta-types.\<close>

class Sort

typedecl set
instance set :: Sort ..

typedecl elem
instance elem :: Sort ..

typedecl rel
instance rel :: Sort ..

text \<open>
For object-level dependent typing: the dependent sorts are the sort of elements for each set X, and the relations for each pair of sets A, B.
Instead of formalizing the sorts directly, we encode sort information in the form of a sort typing judgment @{text ":"}, defined separately for elements and relations.
\<close>

axiomatization
  elem_sorted :: "[elem, set] \<Rightarrow> o" (infix ":" 40) and
  rel_sorted :: "[rel, set, set] \<Rightarrow> o" ("(_ : _ \<succ> _)" [41, 0, 41] 40)


subsection \<open>Sorted FOL and set theory\<close>

subsubsection \<open>Quantifiers\<close>

abbreviation all_elem :: "[set, elem \<Rightarrow> o] \<Rightarrow> o"
  where "all_elem X P \<equiv> \<forall>x. x: X \<longrightarrow> P x"

abbreviation ex_elem :: "[set, elem \<Rightarrow> o] \<Rightarrow> o"
  where "ex_elem X P \<equiv> \<exists>x. x: X \<and> P x"

abbreviation ex1_elem :: "[set, elem \<Rightarrow> o] \<Rightarrow> o"
  where "ex1_elem X P \<equiv> \<exists>!x. x: X \<and> P x"

abbreviation all_rel :: "[set, set, rel \<Rightarrow> o] \<Rightarrow> o"
  where "all_rel A B P \<equiv> \<forall>\<phi>. \<phi>: A \<succ> B \<longrightarrow> P \<phi>"

abbreviation ex_rel :: "[set, set, rel \<Rightarrow> o] \<Rightarrow> o"
  where "ex_rel A B P \<equiv> \<exists>\<phi>. \<phi>: A \<succ> B \<and> P \<phi>"

abbreviation ex1_rel :: "[set, set, rel \<Rightarrow> o] \<Rightarrow> o"
  where "ex1_rel A B P \<equiv> \<exists>!\<phi>. \<phi>: A \<succ> B \<and> P \<phi>"

syntax
  "_all_elem" :: "[idt, set, o] \<Rightarrow> o" ("(\<forall>_: _./ _)" [0, 0, 10] 11)
  "_ex_elem"  :: "[idt, set, o] \<Rightarrow> o" ("(\<exists>_: _./ _)" [0, 0, 10] 11)
  "_ex1_elem" :: "[idt, set, o] \<Rightarrow> o" ("(\<exists>!_: _./ _)" [0, 0, 10] 11)
  "_all_rel"  :: "[idt, set, set, o] \<Rightarrow> o" ("(\<forall>_: _ \<succ> _./ _)" [0, 0, 0, 10] 11)
  "_ex_rel"   :: "[idt, set, set, o] \<Rightarrow> o" ("(\<exists>_: _ \<succ> _./ _)" [0, 0, 0, 10] 11)
  "_ex1_rel"  :: "[idt, set, set, o] \<Rightarrow> o" ("(\<exists>!_: _ \<succ> _./ _)" [0, 0, 0, 10] 11)
translations
  "\<forall>x: X. P"  \<rightleftharpoons> "CONST all_elem X (\<lambda>x. P)"
  "\<exists>x: X. P"  \<rightleftharpoons> "CONST ex_elem X (\<lambda>x. P)"
  "\<exists>!x: X. P" \<rightleftharpoons> "CONST ex1_elem X (\<lambda>x. P)"
  "\<forall>\<phi>: A \<succ> B. P"  \<rightleftharpoons> "CONST all_rel A B (\<lambda>\<phi>. P)"
  "\<exists>\<phi>: A \<succ> B. P"  \<rightleftharpoons> "CONST ex_rel A B (\<lambda>\<phi>. P)"
  "\<exists>!\<phi>: A \<succ> B. P" \<rightleftharpoons> "CONST ex1_rel A B (\<lambda>\<phi>. P)"

subsubsection \<open>Basic judgments\<close>

axiomatization
  elem_of :: "[elem, set] \<Rightarrow> o" (infix "\<in>" 50) and
  holds   :: "[rel, elem, elem] \<Rightarrow> o" ("(_'(_, _'))" [100, 0, 0])
where
  elem_of_sort: "x \<in> X \<Longrightarrow> x: X" and
  holds_dom_sort: "\<phi>: A \<succ> B \<Longrightarrow> \<phi>(x, y) \<Longrightarrow> x: A" and
  holds_codom_sort: "\<phi>: A \<succ> B \<Longrightarrow> \<phi>(x, y) \<Longrightarrow> y: B"

abbreviation "not_elem_of" :: "[elem, set] \<Rightarrow> o" (infix "\<notin>" 50)
  where "x \<notin> X \<equiv> \<not> x \<in> X"

subsubsection \<open>Definite description\<close>

axiomatization desc :: "('a \<Rightarrow> o) \<Rightarrow> 'a" where
  desc_def [intro?]: "\<exists>!x. P x \<Longrightarrow> P (desc P)"

syntax "_the" :: "[idt, o] \<Rightarrow> 'a" ("(the _ | _)")
translations "the x | P" \<rightleftharpoons> "CONST desc (\<lambda>x. P)"


section \<open>Axioms\<close>

axiomatization where

  existence: "\<exists>X. \<exists>x: X. x \<in> X" and

  comprehension: "\<exists>!\<phi>: A \<succ> B. \<forall>x: A. \<forall>y: B. \<phi>(x, y) \<longleftrightarrow> P x y"

text \<open>To state the third axiom we first define functions.\<close>

abbreviation is_func :: "[rel, set, set] \<Rightarrow> o" ("(_ : _ \<rightarrow> _)" [41, 0, 41] 40)
  where "\<phi>: A \<rightarrow> B \<equiv> \<phi>: A \<succ> B \<and> (\<forall>x. x \<in> A \<longrightarrow> (\<exists>!y. \<phi>(x, y)))"

abbreviation func_app :: "[rel, elem] \<Rightarrow> elem" ("(_'(_'))" [100, 0])
  where "\<phi>(x) \<equiv> the y | \<phi>(x, y)"

lemma "\<lbrakk>\<phi>: A \<rightarrow> B; x \<in> A\<rbrakk> \<Longrightarrow> \<phi>(x, \<phi>(x))"
  by rule auto

axiomatization
  tab :: "rel \<Rightarrow> set" ("|_|") and
  fst :: "rel \<Rightarrow> rel" and
  snd :: "rel \<Rightarrow> rel"
where
  tabulation:
    "\<forall>\<phi>: A \<succ> B.
      fst \<phi>: |\<phi>| \<rightarrow> A \<and>
      snd \<phi>: |\<phi>| \<rightarrow> B \<and>
      (\<forall>x: A. \<forall>y: B. \<phi>(x, y) \<longleftrightarrow> (\<exists>r: |\<phi>|. (fst \<phi>)(r) = x \<and> (snd \<phi>)(r) = y)) \<and>
      (\<forall>r: |\<phi>|. \<forall>s: |\<phi>|. (fst \<phi>)(r) = (fst \<phi>)(s) \<and> (snd \<phi>)(r) = (snd \<phi>)(s) \<longrightarrow> r = s)"


subsection \<open>Basic consequences of the axioms\<close>

theorem emptyset: "\<exists>X. \<forall>x: X. x \<notin> X"
proof -
  from existence
    obtain a A where "a \<in> A" by auto
  from comprehension[of A A "\<lambda>_ _. False"]
    obtain \<phi> where
    "\<phi>: A \<succ> A" and
    "\<forall>x: A. \<forall>y: A. \<not>\<phi>(x, y)"
    by auto
  with tabulation[of A A]
    have 


end
