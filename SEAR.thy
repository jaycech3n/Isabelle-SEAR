chapter \<open>Shulman's ``Sets, Elements, And Relations''\<close>

theory SEAR

imports
  HOL.HOL
  "HOL-Eisbach.Eisbach"
  "HOL-Eisbach.Eisbach_Tools"

keywords
  "relation" :: thy_decl

begin


section \<open>Basic settings\<close>

setup Pure_Thy.old_appl_syntax_setup
declare[[eta_contract=false]]


section \<open>Logic and definitions\<close>

subsection \<open>Sorts\<close>

text \<open>
We formulate the theory on top of HOL, but define a separate sort of objects, and modify the default
quantifiers to only quantify over this sort.
\<close>

\<comment>\<open>
Should at some point take a hard look at the actual logical strength/consistency of this theory.
Note for instance that most of the logical connectives and constants are defined using higher-order
statements.
\<close>

class sort

text \<open>
Three distinct sorts of object.
The original formulation is dependently-sorted, but Isabelle's type class system can't do that.
Instead, we ensure that every occurence of an element or relation in a formula appears together with
its domain.
\<close>

typedecl set
typedecl elem
typedecl rel

instance set  :: sort ..
instance elem :: sort ..
instance rel  :: sort ..


subsection \<open>Judgments\<close>

axiomatization
  elem_of :: "[elem, set] \<Rightarrow> bool" (infix "\<in>" 50) and
  rel_of  :: "[rel, set, set] \<Rightarrow> bool" ("(_ : _ \<succ> _)"[51, 0, 51] 50) and
  holds   :: "[rel, elem, elem] \<Rightarrow> bool"

syntax "_holds" :: "[elem, rel, elem] \<Rightarrow> bool" ("(_ _ _)")
translations "x \<phi> y" \<rightleftharpoons> "CONST holds(\<phi>, x, y)"

text \<open>We need to axiomatize what it means for a relation to have a particular domain and codomain.\<close>

axiomatization where
  rel_dom: "\<lbrakk>\<phi>: A \<succ> B; x \<phi> y\<rbrakk> \<Longrightarrow> x \<in> A" and
  rel_cod: "\<lbrakk>\<phi>: A \<succ> B; x \<phi> y\<rbrakk> \<Longrightarrow> y \<in> B"

abbreviation "not_elem_of" :: "[elem, set] \<Rightarrow> bool" (infix "\<notin>" 50)
  where "x \<notin> X \<equiv> \<not> x \<in> X"


subsection \<open>Quantifiers\<close>

\<comment>\<open>Free up notation to be used by our quantifiers.\<close>

no_notation
  All (binder "\<forall>" 10) and
  Ex  (binder "\<exists>" 10)
notation
  All (binder "ALL " 10) and
  Ex  (binder "EX " 10)

no_syntax
  "_Ex1" :: "pttrn \<Rightarrow> bool \<Rightarrow> bool" ("(3\<exists>!_./ _)" [0, 10] 10)
  "_Not_Ex" :: "idts \<Rightarrow> bool \<Rightarrow> bool" ("(3\<nexists>_./ _)" [0, 10] 10)
  "_Not_Ex1" :: "pttrn \<Rightarrow> bool \<Rightarrow> bool" ("(3\<nexists>!_./ _)" [0, 10] 10)

definition all_set :: "(set \<Rightarrow> bool) \<Rightarrow> bool" (binder "\<forall>" 10)
  where "\<forall>x. P(x) \<equiv> ALL x::set. P(x)"

definition ex_set :: "(set \<Rightarrow> bool) \<Rightarrow> bool" (binder "\<exists>" 10)
  where "\<exists>x. P(x) \<equiv> EX x::set. P(x)"

definition ex1_set :: "(set \<Rightarrow> bool) \<Rightarrow> bool" (binder "\<exists>!" 10)
  where "\<exists>!x. P(x) \<equiv> EX! x::set. P(x)"

definition all_elem :: "[set, elem \<Rightarrow> bool] \<Rightarrow> bool"
  where "all_elem(X, P) \<equiv> ALL x. x \<in> X \<longrightarrow> P(x)"

definition ex_elem :: "[set, elem \<Rightarrow> bool] \<Rightarrow> bool"
  where "ex_elem(X, P) \<equiv> EX x. x \<in> X \<and> P(x)"

definition ex1_elem :: "[set, elem \<Rightarrow> bool] \<Rightarrow> bool"
  where "ex1_elem(X, P) \<equiv> EX! x. x \<in> X \<and> P(x)"

definition all_rel :: "[set, set, rel \<Rightarrow> bool] \<Rightarrow> bool"
  where "all_rel(A, B, P) \<equiv> ALL \<phi>. \<phi>: A \<succ> B \<longrightarrow> P(\<phi>)"

definition ex_rel :: "[set, set, rel \<Rightarrow> bool] \<Rightarrow> bool"
  where "ex_rel(A, B, P) \<equiv> EX \<phi>. \<phi>: A \<succ> B \<and> P(\<phi>)"

definition ex1_rel :: "[set, set, rel \<Rightarrow> bool] \<Rightarrow> bool"
  where "ex1_rel(A, B, P) \<equiv> EX! \<phi>. \<phi>: A \<succ> B \<and> P(\<phi>)"

syntax
  "_all_elem" :: "[idt, set, bool] \<Rightarrow> bool" ("(\<forall>_ \<in> _./ _)"[0, 0, 10] 11)
  "_ex_elem"  :: "[idt, set, bool] \<Rightarrow> bool" ("(\<exists>_ \<in> _./ _)"[0, 0, 10] 11)
  "_ex1_elem" :: "[idt, set, bool] \<Rightarrow> bool" ("(\<exists>!_ \<in> _./ _)"[0, 0, 10] 11)
  "_all_rel"  :: "[idt, set, set, bool] \<Rightarrow> bool" ("(\<forall>_: _ \<succ> _./ _)"[0, 0, 0, 10] 11)
  "_ex_rel"   :: "[idt, set, set, bool] \<Rightarrow> bool" ("(\<exists>_: _ \<succ> _./ _)"[0, 0, 0, 10] 11)
  "_ex1_rel"  :: "[idt, set, set, bool] \<Rightarrow> bool" ("(\<exists>!_: _ \<succ> _./ _)"[0, 0, 0, 10] 11)
translations
  "\<forall>x \<in> X. P"  \<rightleftharpoons> "CONST all_elem(X, \<lambda>x. P)"
  "\<exists>x \<in> X. P"  \<rightleftharpoons> "CONST ex_elem(X, \<lambda>x. P)"
  "\<exists>!x \<in> X. P" \<rightleftharpoons> "CONST ex1_elem(X, \<lambda>x. P)"
  "\<forall>\<phi>: A \<succ> B. P"  \<rightleftharpoons> "CONST all_rel(A, B, \<lambda>\<phi>. P)"
  "\<exists>\<phi>: A \<succ> B. P"  \<rightleftharpoons> "CONST ex_rel(A, B, \<lambda>\<phi>. P)"
  "\<exists>!\<phi>: A \<succ> B. P" \<rightleftharpoons> "CONST ex1_rel(A, B, \<lambda>\<phi>. P)"


subsubsection \<open>Rules for quantifiers\<close>

\<comment>\<open>Following the quantifier rules implemented in HOL/HOL.thy.\<close>

text \<open>Universal\<close>

lemma
  all_set_spec: "\<forall>X. P(X) \<Longrightarrow> P(X)" and

  all_setI: "(\<And>X. P(X)) \<Longrightarrow> \<forall>X. P(X)" and

  all_setE: "\<lbrakk>\<forall>X. P(X); P(X) \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"

  unfolding all_set_def by auto

lemma
  all_elem_spec: "\<lbrakk>\<forall>x \<in> X. P(x); x \<in> X\<rbrakk> \<Longrightarrow> P(x)" and

  all_elemI: "(\<And>x. x \<in> X \<Longrightarrow> P(x)) \<Longrightarrow> \<forall>x \<in> X. P(x)" and

  all_elemE: "\<lbrakk>\<forall>x \<in> X. P(x); (\<And>x. x \<in> X \<Longrightarrow> P(x)) \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"

  unfolding all_elem_def by auto

lemma
  all_rel_spec: "\<lbrakk>\<forall>\<phi>: A \<succ> B. P(\<phi>); \<phi>: A \<succ> B\<rbrakk> \<Longrightarrow> P(\<phi>)" and

  all_relI: "(\<And>\<phi>. \<phi>: A \<succ> B \<Longrightarrow> P(\<phi>)) \<Longrightarrow> \<forall>\<phi>: A \<succ> B. P(\<phi>)" and

  all_relE: "\<lbrakk>\<forall>\<phi>: A \<succ> B. P(\<phi>); (\<And>\<phi>. \<phi>: A \<succ> B \<Longrightarrow> P(\<phi>)) \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"

  unfolding all_rel_def by auto


text \<open>Existential\<close>

lemma
  ex_setI: "\<And>P. P(X) \<Longrightarrow> \<exists>X. P(X)" and

  ex_setE: "\<And>P. \<lbrakk>\<exists>X. P(X); \<And>X. P(X) \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
and
  ex_elemI: "\<And>P. \<lbrakk>x \<in> X; P(x)\<rbrakk> \<Longrightarrow> \<exists>x \<in> X. P(x)" and

  ex_elemE: "\<And>P. \<lbrakk>\<exists>x \<in> X. P(x); \<And>x. \<lbrakk>x \<in> X; P(x)\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
and
  ex_relI: "\<And>P. \<lbrakk>\<phi>: A \<succ> B; P(\<phi>)\<rbrakk> \<Longrightarrow> \<exists>\<phi>: A \<succ> B. P(\<phi>)" and

  ex_relE: "\<And>P. \<lbrakk>\<exists>\<phi>: A \<succ> B. P(\<phi>); \<And>\<phi>. \<lbrakk>\<phi>: A \<succ> B; P(\<phi>)\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"

  unfolding ex_set_def ex_elem_def ex_rel_def by auto


text \<open>Unique existence\<close>

lemma
  ex1_setI: "\<lbrakk>P(X); \<And>Y. P(Y) \<Longrightarrow> Y = X\<rbrakk> \<Longrightarrow> \<exists>!X. P(X)" and

  ex_ex1_setI: "\<lbrakk>\<exists>X. P(X); \<And>X Y. \<lbrakk>P(X); P(Y)\<rbrakk> \<Longrightarrow> X = Y\<rbrakk> \<Longrightarrow> \<exists>!X. P(X)" and

  ex1_setE: "\<lbrakk>\<exists>!X. P(X); \<And>X. \<lbrakk>P(X); \<And>Y. P(Y) \<Longrightarrow> Y = X\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R" and

  alt_ex1_setE: "\<lbrakk>\<exists>!X. P(X); \<And>X. \<lbrakk>P(X); \<And>Y Y'. \<lbrakk>P(Y); P(Y')\<rbrakk> \<Longrightarrow> Y = Y'\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R" and

  ex1_implies_ex_set: "\<exists>!X. P(X) \<Longrightarrow> \<exists>X. P(X)"

  unfolding ex_set_def ex1_set_def by auto

lemma
  ex1_elemI: "\<lbrakk>x \<in> X; P(x); \<And>y. \<lbrakk>y \<in> X; P(y)\<rbrakk> \<Longrightarrow> y = x\<rbrakk> \<Longrightarrow> \<exists>!x \<in> X. P(x)" and

  ex_ex1_elemI: "\<lbrakk>\<exists>x \<in> X. P(x); \<And>x y. \<lbrakk>x \<in> X; y \<in> X; P(x); P(y)\<rbrakk> \<Longrightarrow> x = y\<rbrakk> \<Longrightarrow> \<exists>!x \<in> X. P(x)" and

  ex1_elemE: "\<lbrakk>\<exists>!x \<in> X. P(x); \<And>x. \<lbrakk>x \<in> X; P(x); \<And>y. \<lbrakk>y \<in> X; P(y)\<rbrakk> \<Longrightarrow> y = x\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R" and

  alt_ex1_elemE: "\<lbrakk>\<exists>!x \<in> X. P(x);
    \<And>x. \<lbrakk>x \<in> X; P(x); \<And>y y'. \<lbrakk>y \<in> X; y' \<in> X; P(y); P(y')\<rbrakk> \<Longrightarrow> y = y'\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R" and

  ex1_implies_ex_elem: "\<exists>!x \<in> X. P(x) \<Longrightarrow> \<exists>x \<in> X. P(x)"

  unfolding ex_elem_def ex1_elem_def by auto

lemma
  ex1_relI: "\<lbrakk>\<phi>: A \<succ> B; P(\<phi>); \<And>\<psi>. \<lbrakk>\<psi>: A \<succ> B; P(\<psi>)\<rbrakk> \<Longrightarrow> \<psi> = \<phi>\<rbrakk> \<Longrightarrow> \<exists>!\<phi>: A \<succ> B. P(\<phi>)" and

  ex_ex1_relI: "\<lbrakk>\<exists>\<phi>: A \<succ> B. P(\<phi>);
    \<And>\<phi> \<psi>. \<lbrakk>\<phi>: A \<succ> B; \<psi>: A \<succ> B; P(\<phi>); P(\<psi>)\<rbrakk> \<Longrightarrow> \<phi> = \<psi>\<rbrakk> \<Longrightarrow> \<exists>!\<phi>: A \<succ> B. P(\<phi>)" and

  ex1_relE: "\<lbrakk>\<exists>!\<phi>: A \<succ> B. P(\<phi>);
    \<And>\<phi>. \<lbrakk>\<phi>: A \<succ> B; P(\<phi>); \<And>\<psi>. \<lbrakk>\<psi>: A \<succ> B; P(\<psi>)\<rbrakk> \<Longrightarrow> \<psi> = \<phi>\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R" and

  alt_ex1_relE: "\<lbrakk>\<exists>!\<phi>: A \<succ> B. P(\<phi>);
    \<And>\<phi>. \<lbrakk>\<phi>: A \<succ> B; P(\<phi>); \<And>\<psi> \<psi>'. \<lbrakk>\<psi>: A \<succ> B; \<psi>': A \<succ> B; P(\<psi>); P(\<psi>')\<rbrakk> \<Longrightarrow> \<psi> = \<psi>'\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R" and

  ex1_implies_ex_rel: "\<exists>!\<phi>: A \<succ> B. P(\<phi>) \<Longrightarrow> \<exists>\<phi>: A \<succ> B. P(\<phi>)"

  unfolding ex_rel_def ex1_rel_def by auto

text \<open>Classical introduction\<close>

lemma ex_setCI: "(\<forall>x. \<not>P(x) \<Longrightarrow> P(x)) \<Longrightarrow> \<exists>x. P(x)"
  unfolding all_set_def ex_set_def by auto

lemma ex_elemCI: "(\<forall>x \<in> X. \<not>P(x) \<Longrightarrow> x \<in> X \<and> P(x)) \<Longrightarrow> \<exists>x \<in> X. P(x)"
  unfolding all_elem_def ex_elem_def by auto

lemma ex_relCI: "(\<forall>\<phi>: A \<succ> B. \<not>P(\<phi>) \<Longrightarrow> \<phi>: A \<succ> B \<and> P(\<phi>)) \<Longrightarrow> \<exists>\<phi>: A \<succ> B. P(\<phi>)"
  unfolding all_rel_def ex_rel_def by auto

(* HOL has `allE'`, would we want this? *)


declare
  ex_ex1_setI [intro!]
  ex_ex1_elemI [intro!]
  ex_ex1_relI [intro!]
and
  all_setI [intro!]
  all_elemI [intro!]
  all_relI [intro!]
and
  ex_setI [intro]
  ex_elemI [intro]
  ex_relI [intro]
and
  ex_setE [elim!]
  ex_elemE [elim!]
  ex_relE [elim!]
and
  all_setE [elim]
  all_elemE [elim]
  all_relE [elim]
and
  ex1_setI [intro]
  ex1_elemI [intro]
  ex1_relI [intro]
and
  ex1_implies_ex_set [elim?]
  ex1_implies_ex_elem [elim?]
  ex1_implies_ex_rel [elim?]
and
  alt_ex1_setE [elim!]
  alt_ex1_elemE [elim!]
  alt_ex1_relE [elim!]

text \<open>Rulify & atomize—conversion with meta quantification\<close>

lemma
  rulify_all_set: "\<And>P. Trueprop(\<forall>X. P(X)) \<equiv> (\<And>X. P(X))" and
  rulify_all_elem: "\<And>P. Trueprop(\<forall>x \<in> X. P(x)) \<equiv> (\<And>x. x \<in> X \<Longrightarrow> P(x))" and
  rulify_all_rel: "\<And>P. Trueprop(\<forall>\<phi>: A \<succ> B. P(\<phi>)) \<equiv> (\<And>\<phi>. \<phi>: A \<succ> B \<Longrightarrow> P(\<phi>))"
and
  rulify_ex_setL': "\<And>P Q. Trueprop((\<exists>X. P(X)) \<longrightarrow> Q) \<equiv> (\<And>X. P(X) \<Longrightarrow> Q)" and
  rulify_ex_elemL': "\<And>P Q. Trueprop((\<exists>x \<in> X. P(x)) \<longrightarrow> Q) \<equiv> (\<And>x. \<lbrakk>x \<in> X; P(x)\<rbrakk> \<Longrightarrow> Q)" and
  rulify_ex_relL': "\<And>P Q. Trueprop((\<exists>\<phi>: A \<succ> B. P(\<phi>))\<longrightarrow> Q) \<equiv> (\<And>\<phi>. \<lbrakk>\<phi>: A \<succ> B; P(\<phi>)\<rbrakk> \<Longrightarrow> Q)"
and
  rulify_ex_setL: "\<And>P Q. ((\<exists>X. P(X)) \<Longrightarrow> Q) \<equiv> (\<And>X. P(X) \<Longrightarrow> Q)" and
  rulify_ex_elemL: "\<And>P Q. ((\<exists>x \<in> X. P(x)) \<Longrightarrow> Q) \<equiv> (\<And>x. \<lbrakk>x \<in> X; P(x)\<rbrakk> \<Longrightarrow> Q)" and
  rulify_ex_relL: "\<And>P Q. ((\<exists>\<phi>: A \<succ> B. P(\<phi>)) \<Longrightarrow> Q) \<equiv> (\<And>\<phi>. \<lbrakk>\<phi>: A \<succ> B; P(\<phi>)\<rbrakk> \<Longrightarrow> Q)"

  by (rule, auto)+

lemmas rulify_quants [rulify, simp] =  \<comment>\<open>Not quite sure `simp` is a good idea here.\<close>
  rulify_all_set
  rulify_all_elem
  rulify_all_rel
  rulify_ex_setL'
  rulify_ex_elemL'
  rulify_ex_relL'
  rulify_ex_setL
  rulify_ex_elemL
  rulify_ex_relL

lemmas [symmetric, atomize] =
  rulify_all_set
  rulify_all_elem
  rulify_all_rel
  rulify_ex_setL'
  rulify_ex_elemL'
  rulify_ex_relL'

lemmas [symmetric, atomize_elim] =
  rulify_ex_setL
  rulify_ex_elemL
  rulify_ex_relL


text \<open>Simplification rules\<close>

lemma all_set_simps [simp]:
  "(\<forall>X. P) = P"
  "(\<forall>X. X \<noteq> A) = False"
  "(\<forall>X. A \<noteq> X) = False"
  "\<And>P. (\<forall>X. X = A \<longrightarrow> P(X)) = P(A)"
  "\<And>P. (\<forall>X. A = X \<longrightarrow> P(X)) = P(A)"
  "\<And>P Q. (\<forall>x. P(x) \<and> Q) = ((\<forall>x. P(x)) \<and> Q)"
  "\<And>P Q. (\<forall>x. P \<and> Q(x)) = (P \<and> (\<forall>x. Q(x)))"
  "\<And>P Q. (\<forall>x. P(x) \<or> Q) = ((\<forall>x. P(x)) \<or> Q)"
  "\<And>P Q. (\<forall>x. P \<or> Q(x)) = (P \<or> (\<forall>x. Q(x)))"
  "\<And>P Q. (\<forall>x. P(x) \<longrightarrow> Q) = ((\<exists>x. P(x)) \<longrightarrow> Q)"
  "\<And>P Q. (\<forall>x. P \<longrightarrow> Q(x)) = (P \<longrightarrow> (\<forall>x. Q(x)))"

and ex_set_simps [simp]:
  "(\<exists>X. P) = P"
  "\<exists>X. X = A"
  "\<exists>X. A = X"
  "\<And>P. (\<exists>X. X = A \<and> P(X)) = P(A)"
  "\<And>P. (\<exists>X. A = X \<and> P(X)) = P(A)"
  "\<And>P Q. (\<exists>x. P(x) \<and> Q) = ((\<exists>x. P(x)) \<and> Q)"
  "\<And>P Q. (\<exists>x. P \<and> Q(x)) = (P \<and> (\<exists>x. Q(x)))"
  "\<And>P Q. (\<exists>x. P(x) \<or> Q) = ((\<exists>x. P(x)) \<or> Q)"
  "\<And>P Q. (\<exists>x. P \<or> Q(x)) = (P \<or> (\<exists>x. Q(x)))"
  "\<And>P Q. (\<exists>x. P(x) \<longrightarrow> Q) = ((\<forall>x. P(x)) \<longrightarrow> Q)"
  "\<And>P Q. (\<exists>x. P \<longrightarrow> Q(x)) = (P \<longrightarrow> (\<exists>x. Q(x)))"

  by auto+


subsection \<open>Definite description\<close>

definition "the_set(P) \<equiv> THE X::set. P(X)"
definition "the_elem(X, P) \<equiv> THE x. x \<in> X \<and> P(x)"
definition "the_rel(A, B, P) \<equiv> THE \<phi>. \<phi>: A \<succ> B \<and> P(\<phi>)"

syntax
  "_the_set"  :: "[set, bool] \<Rightarrow> set" ("(the _. _)" 49)
  "_the_elem" :: "[elem, set, bool] \<Rightarrow> elem" ("(the '(_ \<in> _'). _)" 49)
  "_the_rel"  :: "[rel, set, set, bool] \<Rightarrow> rel" ("(the '(_: _ \<succ> _'). _)" 49)
translations
  "the X. P" \<rightleftharpoons> "CONST the_set(\<lambda>X. P)"
  "the (x \<in> X). Q" \<rightleftharpoons> "CONST the_elem(X, \<lambda>x. Q)"
  "the (\<phi>: A \<succ> B). R" \<rightleftharpoons> "CONST the_rel(A, B, \<lambda>\<phi>. R)"

lemma the_set_equality: "\<lbrakk>P(X); \<And>Y. P(Y) \<Longrightarrow> Y = X\<rbrakk> \<Longrightarrow> (the X. P(X)) = X"
  unfolding the_set_def by blast

lemma the_setI: "\<lbrakk>P(X); \<And>Y. P(Y) \<Longrightarrow> Y = X\<rbrakk> \<Longrightarrow> P(the X. P(X))"
  by (subst the_set_equality)

lemma the_setI': "\<exists>!X. P(X) \<Longrightarrow> P(the X. P(X))"
  by (auto intro: the_setI)

lemma the_setI2: "\<lbrakk>P(X); \<And>Y. P(Y) \<Longrightarrow> Y = X; \<And>X. P(X) \<Longrightarrow> Q(X)\<rbrakk> \<Longrightarrow> Q(the X. P(X))"
  by (auto intro: the_setI)

lemma the_setI2': "\<lbrakk>\<exists>!X. P(X); \<And>X. P(X) \<Longrightarrow> Q(X)\<rbrakk> \<Longrightarrow> Q(the X. P(X))"
  by (auto intro: the_setI2[where ?P=P and ?Q=Q])

lemma the_set_equality': "\<lbrakk>\<exists>!X. P(X); P(X)\<rbrakk> \<Longrightarrow> (the X. P(X)) = X"
  by (auto intro: the_set_equality)

lemma the_set_sym_eq_trivial: "(the Y. X = Y) = X"
  by (auto intro: the_set_equality)

lemma the_elem_equality: "\<lbrakk>x \<in> X; P(x); \<And>y. \<lbrakk>y \<in> X; P(y)\<rbrakk> \<Longrightarrow> y = x\<rbrakk> \<Longrightarrow> (the (x \<in> X). P(x)) = x"
  unfolding the_elem_def by blast

lemma the_elemI: "\<lbrakk>x \<in> X; P(x); \<And>y. \<lbrakk>y \<in> X; P(y)\<rbrakk> \<Longrightarrow> y = x\<rbrakk> \<Longrightarrow> P(the (x \<in> X). P(x))"
  by (subst the_elem_equality)

lemma the_elemI': "\<exists>!x \<in> X. P(x) \<Longrightarrow> P(the (x \<in> X). P(x))"
  by (auto intro: the_elemI)

lemma the_elem_sort': "\<exists>!x \<in> X. P(x) \<Longrightarrow> (the (x \<in> X). P(x)) \<in> X"
  unfolding ex1_elem_def the_elem_def by (blast dest!: theI')

lemma the_elem_sort: "\<lbrakk>x \<in> X; P(x); \<And>y. \<lbrakk>y \<in> X; P(y)\<rbrakk> \<Longrightarrow> y = x\<rbrakk> \<Longrightarrow> (the (x \<in> X). P(x)) \<in> X"
  by (blast intro: the_elem_sort')

lemma the_elemI2:
  "\<lbrakk>x \<in> X; P(x); \<And>y. \<lbrakk>y \<in> X; P(y)\<rbrakk> \<Longrightarrow> y = x;
    \<And>x. \<lbrakk>x \<in> X; P(x)\<rbrakk> \<Longrightarrow> Q(x)\<rbrakk> \<Longrightarrow> Q(the (x \<in> X). P(x))"
  by (auto intro: the_elem_sort the_elemI)

lemma the_elemI2': "\<lbrakk>\<exists>!x \<in> X. P(x); \<And>x. \<lbrakk>x \<in> X; P(x)\<rbrakk> \<Longrightarrow> Q(x)\<rbrakk> \<Longrightarrow> Q(the (x \<in> X). P(x))"
  by (auto intro: the_elemI2[where ?P=P and ?Q=Q])

lemma the_elem_equality': "\<lbrakk>\<exists>!x \<in> X. P(x); x \<in> X; P(x)\<rbrakk> \<Longrightarrow> (the (x \<in> X). P(x)) = x"
  by (auto intro: the_elem_equality)

lemma the_elem_sym_eq_trivial: "x \<in> X \<Longrightarrow> (the (y \<in> X). x = y) = x"
  by (auto intro: the_elem_equality)

lemma the_rel_equality: "\<lbrakk>\<phi>: A \<succ> B; P(\<phi>); \<And>\<psi>. \<lbrakk>\<psi>: A \<succ> B; P(\<psi>)\<rbrakk> \<Longrightarrow> \<psi> = \<phi>\<rbrakk> \<Longrightarrow> (the (\<phi>: A \<succ> B). P(\<phi>)) = \<phi>"
  unfolding the_rel_def by blast

lemma the_relI: "\<lbrakk>\<phi>: A \<succ> B; P(\<phi>); \<And>\<psi>. \<lbrakk>\<psi>: A \<succ> B; P(\<psi>)\<rbrakk> \<Longrightarrow> \<psi> = \<phi>\<rbrakk> \<Longrightarrow> P(the (\<phi>: A \<succ> B). P(\<phi>))"
  by (subst the_rel_equality)

lemma the_relI': "\<exists>!\<phi>: A \<succ> B. P(\<phi>) \<Longrightarrow> P(the (\<phi>: A \<succ> B). P(\<phi>))"
  by (auto intro: the_relI)

lemma the_rel_sort': "\<exists>!\<phi>: A \<succ> B. P(\<phi>) \<Longrightarrow> (the (\<phi>: A \<succ> B). P(\<phi>)): A \<succ> B"
  unfolding ex1_rel_def the_rel_def by (blast dest!: theI')

lemma the_rel_sort: "\<lbrakk>\<phi>: A \<succ> B; P(\<phi>);
  \<And>\<psi>. \<lbrakk>\<psi>: A \<succ> B; P(\<psi>)\<rbrakk> \<Longrightarrow> \<psi> = \<phi>\<rbrakk> \<Longrightarrow> (the (\<phi>: A \<succ> B). P(\<phi>)): A \<succ> B"
  by (blast intro: the_rel_sort')

lemma the_relI2:
  "\<lbrakk>\<phi>: A \<succ> B; P(\<phi>); \<And>\<psi>. \<lbrakk>\<psi>: A \<succ> B; P(\<psi>)\<rbrakk> \<Longrightarrow> \<psi> = \<phi>;
    \<And>\<phi>. \<lbrakk>\<phi>: A \<succ> B; P(\<phi>)\<rbrakk> \<Longrightarrow> Q(\<phi>)\<rbrakk> \<Longrightarrow> Q(the (\<phi>: A \<succ> B). P(\<phi>))"
  by (auto intro: the_rel_sort the_relI)

lemma the_relI2': "\<lbrakk>\<exists>!\<phi>: A \<succ> B. P(\<phi>); \<And>\<phi>. \<lbrakk>\<phi>: A \<succ> B; P(\<phi>)\<rbrakk> \<Longrightarrow> Q(\<phi>)\<rbrakk> \<Longrightarrow> Q(the (\<phi>: A \<succ> B). P(\<phi>))"
  by (auto intro: the_relI2[where ?P=P and ?Q=Q])

lemma the_rel_equality': "\<lbrakk>\<exists>!\<phi>: A \<succ> B. P(\<phi>); \<phi>: A \<succ> B; P(\<phi>)\<rbrakk> \<Longrightarrow> (the (\<phi>: A \<succ> B). P(\<phi>)) = \<phi>"
  by (auto intro: the_rel_equality)

lemma the_rel_sym_eq_trivial: "\<phi>: A \<succ> B \<Longrightarrow> (the (\<psi>: A \<succ> B). \<phi> = \<psi>) = \<phi>"
  by (auto intro: the_rel_equality)


lemmas [intro] =
  the_set_equality
  the_elem_equality
  the_rel_equality

lemmas [elim?] =
  the_set_equality'
  the_elem_equality'
  the_rel_equality'
  the_setI'
  the_elemI'
  the_relI'
  the_elem_sort'
  the_rel_sort'


(* subsection \<open>Indefinite description for sets\<close>

axiomatization some_set :: "(set \<Rightarrow> bool) \<Rightarrow> set"
  where some_setI: "\<exists>X. P(X) \<Longrightarrow> P(some_set(\<lambda>X. P(X)))"

syntax "_some_set" :: "[set, bool] \<Rightarrow> set" ("(some _. _)" 49)
translations "some X. P" \<rightleftharpoons> "CONST some_set (\<lambda>X. P)" *)


subsection \<open>Injectivity and surjectivity of relations\<close>

definition rel_inj :: "[rel, set, set] \<Rightarrow> bool" ("(_ : _ \<succ> _ injective)")
  where "\<phi>: A \<succ> B injective \<equiv> \<forall>a \<in> A. \<forall>a' \<in> A. (\<exists>b \<in> B. (a \<phi> b) \<and> (a' \<phi> b)) \<longrightarrow> a = a'"

definition rel_surj :: "[rel, set, set] \<Rightarrow> bool" ("(_ : _ \<succ> _ surjective)")
  where "\<phi>: A \<succ> B surjective \<equiv> \<forall>b \<in> B. \<exists>a \<in> A. (a \<phi> b)"


subsection \<open>Functions\<close>

definition fun :: "[rel, set, set] \<Rightarrow> bool" ("(_ : _ \<rightarrow> _)"[51, 0, 51] 50)
  where "f: A \<rightarrow> B \<equiv> f: A \<succ> B \<and> (\<forall>x \<in> A. \<exists>!y \<in> B. (x f y))"


subsubsection \<open>Application\<close>

axiomatization app :: "[rel, elem] \<Rightarrow> elem" (infixl "`" 100)
  where app_def: "f: A \<rightarrow> B \<Longrightarrow> f`x \<equiv> the (y \<in> B). (x f y)"


subsubsection \<open>Injectivity and surjectivity\<close>

definition fun_inj :: "[rel, set, set] \<Rightarrow> bool" ("(_ : _ \<hookrightarrow> _)")
  where "f: A \<hookrightarrow> B \<equiv> f: A \<rightarrow> B \<and> (\<forall>a \<in> A. \<forall>a' \<in> A. f`a = f`a' \<longrightarrow> a = a')"

definition fun_surj :: "[rel, set, set] \<Rightarrow> bool" ("(_ : _ \<Rrightarrow> _)")
  where "f: A \<Rrightarrow> B \<equiv> f: A \<rightarrow> B \<and> (\<forall>b \<in> B. \<exists>a \<in> A. f`a = b)"


subsubsection \<open>Rules\<close>

lemma fun_rel: "f: A \<rightarrow> B \<Longrightarrow> f: A \<succ> B"
  unfolding fun_def by auto

lemma fun_uniq_val: "\<lbrakk>f: A \<rightarrow> B; x \<in> A; y \<in> B; y' \<in> B; x f y; x f y'\<rbrakk> \<Longrightarrow> y = y'"
  unfolding fun_def by blast

lemma fun_uniq_val': "\<lbrakk>f: A \<rightarrow> B; x \<in> A\<rbrakk> \<Longrightarrow> \<exists>!y \<in> B. (x f y)"
  unfolding fun_def by blast

lemma fun_holds: "\<lbrakk>f: A \<rightarrow> B; x \<in> A\<rbrakk> \<Longrightarrow> x f (f`x)"
  using fun_uniq_val' app_def the_elemI'[where ?P="\<lambda>y. (x f y)"] by auto

lemma appI: "\<lbrakk>f: A \<rightarrow> B; x \<in> A\<rbrakk> \<Longrightarrow> f`x \<in> B"
  using fun_rel fun_holds by (intro rel_cod)

lemma holds_app_iff [iff]: "\<lbrakk>f: A \<rightarrow> B; x \<in> A; y \<in> B\<rbrakk> \<Longrightarrow>(x f y) \<longleftrightarrow> y = f`x"
  using fun_holds appI fun_uniq_val by auto

lemma rel_inj_fun_inj_iff: "f: A \<rightarrow> B \<and> (f: A \<succ> B injective) \<longleftrightarrow> (f: A \<hookrightarrow> B)"
  by (auto simp: fun_inj_def rel_inj_def fun_holds appI)+


subsection \<open>Tabulations\<close>

text \<open>
A tabulation is a reflection of relations into sets.
It is used in the statement of the third axiom.
\<close>

definition tabulates :: "[set, rel, rel, rel, set, set] \<Rightarrow> bool" ("(_, _, _ tabulates _ : _ \<succ> _)")
  where "T, f1, f2 tabulates \<phi>: A \<succ> B \<equiv>
    f1: T \<rightarrow> A \<and>
    f2: T \<rightarrow> B \<and>
    (\<forall>x \<in> A. \<forall>y \<in> B. (x \<phi> y) \<longleftrightarrow> (\<exists>t \<in> T. f1`t = x \<and> f2`t = y)) \<and>
    (\<forall>s \<in> T. \<forall>t \<in> T. f1`s = f1`t \<and> f2`s = f2`t \<longrightarrow> s = t)"

lemma tabulatesD1:
  "\<lbrakk>T, f1, f2 tabulates \<phi>: A \<succ> B; x \<in> A; y \<in> B\<rbrakk> \<Longrightarrow> (x \<phi> y) \<longleftrightarrow> (\<exists>t \<in> T. f1`t = x \<and> f2`t = y)"
  unfolding tabulates_def by blast

lemma tabulatesD2:
  "\<lbrakk>T, f1, f2 tabulates \<phi>: A \<succ> B; s \<in> T; t \<in> T\<rbrakk> \<Longrightarrow> f1`s = f1`t \<and> f2`s = f2`t \<longrightarrow> s = t"
  unfolding tabulates_def by auto

lemma tabulates_appI: "\<lbrakk>T, f1, f2 tabulates \<phi>: A \<succ> B; r \<in> T\<rbrakk> \<Longrightarrow> f1`r \<in> A \<and> f2`r \<in> B"
  unfolding tabulates_def using appI by auto

lemma tabulates_holds: "\<lbrakk>T, f1, f2 tabulates \<phi>: A \<succ> B; r \<in> T\<rbrakk> \<Longrightarrow> (f1`r) \<phi> (f2`r)"
  by (subst tabulatesD1) (insert tabulates_appI, blast+)


section \<open>Axioms part I\<close>

axiomatization
  elem :: elem and
  set  :: set and
  tab  :: "rel \<Rightarrow> set" ("|_|") and
  fst  :: "rel \<Rightarrow> rel" ("|_|\<^sub>1") and
  snd  :: "rel \<Rightarrow> rel" ("|_|\<^sub>2")
where
  nontrivial: "elem \<in> set" and
  rel_comprehension: "\<exists>!\<phi>: A \<succ> B. \<forall>x \<in> A. \<forall>y \<in> B. (x \<phi> y) \<longleftrightarrow> P(x, y)" and
  tabulation: "\<phi>: A \<succ> B \<Longrightarrow> |\<phi>|, |\<phi>|\<^sub>1, |\<phi>|\<^sub>2 tabulates \<phi>: A \<succ> B"


lemma fst_fun: "\<phi>: A \<succ> B \<Longrightarrow> |\<phi>|\<^sub>1: |\<phi>| \<rightarrow> A"
  using tabulation unfolding tabulates_def by auto

lemma snd_fun: "\<phi>: A \<succ> B \<Longrightarrow> |\<phi>|\<^sub>2: |\<phi>| \<rightarrow> B"
  using tabulation unfolding tabulates_def by auto

lemma tab_holds: "\<lbrakk>\<phi>: A \<succ> B; r \<in> |\<phi>|\<rbrakk> \<Longrightarrow> (|\<phi>|\<^sub>1`r) \<phi> (|\<phi>|\<^sub>2`r)"
  using tabulation tabulates_holds by blast


section \<open>Relations\<close>

text \<open>
Functionality for defining relations by writing
  \<open>relation "\<phi>(x1, ..., xn): A \<succ> B" where "(a \<phi> b) \<longleftrightarrow> P(a, b)"\<close>.
\<close>

ML \<open>
Outer_Syntax.local_theory @{command_keyword relation} "Define a relation"
let
  val parser = Parse.term -- (Parse.where_ |-- Parse.prop)

  fun dest_param tm = case tm of
      Free (name, typ) => (tm, name, typ)
    | _ => error "Parameter not atomic"

  (* We call the part between the `relation` and `where` keywords the declaration, and the part
     after the `where` keyword, the definition. *)

  (* Process the declaration and return the relation head constant, parameters, domain, and
     codomain. *)
  fun process_decl tm = case tm of
      @{const "rel_of"} $ rel $ dom $ cod =>
        let val (head, params) = Term.strip_comb rel
        in (head, params, dom, cod) end
    | _ => error "Declaration not accepted"

  (* Process a definition of the form "(a \<phi> b) = P(a, b)" for a relation with given domain and
     codomain. *)
  fun process_def lthy head dom cod def = case def of
      @{const HOL.eq (bool)} $ (@{const "holds"} $ rel' $ var1 $ var2) $ cond =>
        let
          val _ = if not (Term.aconv_untyped (head, rel'))
            then error ("Not a definition for \"" ^
              ((Pretty.string_of o Syntax.pretty_term lthy) head) ^ "\"")
            else ()

          val (var1name, var2name) = apply2 Term.term_name (var1, var2)

          val prop =
            Abs ("\<phi>", @{typ "rel"}, Term.abstract_over (rel',
              @{const "all_elem"} $ dom $
                Abs (var1name, @{typ "elem"}, Term.abstract_over (var1,
                  @{const "all_elem"} $ cod $
                    Abs (var2name, @{typ "elem"}, Term.abstract_over (var2, def))))))

          val cond' =
            Abs (var1name, @{typ "elem"}, Term.abstract_over (var1,
                Abs (var2name, @{typ "elem"}, Term.abstract_over (var2, cond))))
        in
          (prop, cond')
        end
    | _ => error "Definition not accepted"

  fun define_relation lthy head params dom cod prop =
    let
      fun abstract ((param, name, typ), tm) = Abs (name, typ, Term.abstract_over (param, tm))

      val defined_tm =
        List.foldr abstract (@{const "the_rel"} $ dom $ cod $ prop) (map dest_param params)

      val bname = Term.term_name head
    in
      lthy |>
        Local_Theory.define (
          (Binding.qualified_name bname, NoSyn),
          ((Binding.qualified_name (bname ^ "_def"), []), defined_tm)
        )
    end

  fun generate_thms lthy head params dom cod cond def_thm =
    let
      val instantiations = [
          ((("A", 0), @{typ set}), Thm.cterm_of lthy dom),
          ((("B", 0), @{typ set}), Thm.cterm_of lthy cod),
          ((("P", 0), @{typ "elem \<Rightarrow> elem \<Rightarrow> bool"}), Thm.cterm_of lthy cond)
        ]

      val fold_thm =
        let
          (* `def_thm` is the definitional lemma for the defined relation and has the form
             `\<phi> \<equiv> \<lambda>x1 ... xn. B`.
             Return `\<lambda>x1 ... xn. B`. *)
          val lambda = case (Thm.prop_of def_thm) of
              Const ("Pure.eq", _) $ _ $ rhs => rhs
            | _ => error "Not a definitional equation"

          (* Lemma `\<phi> a1 ... an \<equiv> (\<lambda>x1 ... xn. B) a1 ... an` *)
          val def_app_eq_thm =
            let val refl_thm = Thm.reflexive o Thm.cterm_of lthy in
              fold (fn th1 => fn th2 => Thm.combination th2 th1) (map refl_thm params) def_thm
            end

          (* Lemma `(\<lambda>x1 ... xn. B) a1 ... an \<equiv> B[a1/x1, ..., an/xn]` *)
          val lambda_app_eq_thm =
            Thm.beta_conversion true (Thm.cterm_of lthy (Term.list_comb (lambda, params)))
        in
          Thm.transitive def_app_eq_thm lambda_app_eq_thm
        end

      fun quantify params thm =
        let fun quantify' (tm, thm) = Thm.forall_intr (Thm.cterm_of lthy tm) thm
        in List.foldr quantify' thm params end

      val (sort_thm, prop_thm) =
        apply2
          (fn th =>
            (th OF [Thm.instantiate ([], instantiations) @{thm rel_comprehension}])
            |> Local_Defs.fold lthy [fold_thm]
            |> Object_Logic.rulify lthy
            |> quantify params
          ) (@{thm the_rel_sort'}, @{thm the_relI'})

      val name = Term.term_name head
    in
      lthy |>
        Local_Theory.notes [
          ((Binding.qualified_name (name ^ "_sort"), @{attributes [intro!]}), [([sort_thm], [])]),
          ((Binding.qualified_name (name ^ "_prop"), @{attributes [iff]}), [([prop_thm], [])])
        ]
    end

  fun relation_cmd (declstr, defstr) lthy =
    let
      val (head, params, dom, cod) = process_decl (Syntax.read_term lthy declstr)
      val (prop, cond) = process_def lthy head dom cod (Syntax.read_term lthy defstr)
      val ((defined_tm, (_, def_thm)), lthy') = define_relation lthy head params dom cod prop
      val ((sort_thm_name, sort_thm :: _) :: (_, prop_thm :: _) :: _, lthy'') =
        generate_thms lthy' head params dom cod cond def_thm
      val defined_name = Term.term_name defined_tm
    in
      writeln ("relation\n  " ^ defined_name ^ " :: \"" ^
        (Syntax.string_of_typ lthy' (Term.type_of defined_tm)) ^ "\"");
      Output.information ("lemma " ^ defined_name ^ "_sort:\n  " ^
        ((Pretty.string_of o Syntax.pretty_term lthy' o Thm.prop_of) sort_thm));
      Output.information ("lemma " ^ defined_name ^ "_prop:\n  " ^
        ((Pretty.string_of o Syntax.pretty_term lthy' o Thm.prop_of) prop_thm));
      lthy''
    end
in
  parser >> relation_cmd
end
\<close>


section \<open>Function extensionality\<close>

lemma fun_ext:
  assumes "f: A \<rightarrow> B" and "g: A \<rightarrow> B" and "\<forall>x \<in> A. f`x = g`x"
  shows "f = g"
proof -
  have "\<forall>x \<in> A. \<forall>y \<in> B. (x f y) \<longleftrightarrow> (x g y)"
    by (auto intro: assms(1-2) simp: holds_app_iff[OF assms(1)] assms(3)[rule_format])
  thus "f = g"
    using rel_comprehension[where P="\<lambda>x y. (x g y)"] assms(1-2) fun_def by blast
qed


section \<open>Empty and singleton sets\<close>

relation "emptyrel: set \<succ> set" where "(x emptyrel y) \<longleftrightarrow> False"

definition emptyset :: set ("\<emptyset>") where "\<emptyset> \<equiv> |emptyrel|"

(* etc *)

lemma emptyset_ex: "\<exists>X. \<forall>x \<in> X. x \<notin> X"
proof -
  obtain \<phi> where "\<phi>: A \<succ> A" and "\<forall>x \<in> A. \<forall>y \<in> A. \<not>(x \<phi> y)"
    using rel_comprehension[of A A "\<lambda>_ _. False"] by blast

  hence *: "\<forall>x \<in> A. \<forall>y \<in> A. \<not>(\<exists>r \<in> |\<phi>|. |\<phi>|\<^sub>1`r = x \<and> |\<phi>|\<^sub>2`r = y)"
    using tabulatesD1 tabulation[of \<phi> A A] by auto

  have "\<forall>r \<in> |\<phi>|. r \<notin> |\<phi>|"
  proof auto
    fix r assume "r \<in> |\<phi>|"
    then have "|\<phi>|\<^sub>1`r \<in> A" and "|\<phi>|\<^sub>2`r \<in> A" and "\<exists>r' \<in> |\<phi>|. |\<phi>|\<^sub>1`r' = |\<phi>|\<^sub>1`r \<and> |\<phi>|\<^sub>2`r' = |\<phi>|\<^sub>2`r"
      by (auto intro: fst_fun snd_fun appI \<open>\<phi>: A \<succ> A\<close>)
    thus False using * by auto
  qed thus ?thesis ..
qed

lemma singleton_ex: "\<exists>X. \<exists>x \<in> X. \<forall>y \<in> X. y = x"
proof -
  obtain a A where "a \<in> A" using nonempty_ex by blast
  obtain \<phi> where 1: "\<phi>: A \<succ> A" and 2: "\<forall>x \<in> A. \<forall>y \<in> A. (x \<phi> y) \<longleftrightarrow> x = a \<and> y = a"
    using rel_comprehension[of A A "\<lambda>x y. x = a \<and> y = a"] by blast

  hence 3: "\<forall>r \<in> |\<phi>|. |\<phi>|\<^sub>1`r = a \<and> |\<phi>|\<^sub>2`r = a"
    by (auto intro: fst_fun snd_fun appI tabulation tab_holds)

  obtain r where "r \<in> |\<phi>|" using 2 tabulatesD1[OF tabulation[OF 1], of a a] \<open>a \<in> A\<close> by auto
  then have "\<forall>s \<in> |\<phi>|. r = s" using 3 tabulatesD2[OF tabulation[OF 1]] by auto

  thus ?thesis using \<open>r \<in> |\<phi>|\<close> by auto
qed

text \<open>Fix particular choices of empty and singleton set.\<close>

definition emptyset :: set ("\<emptyset>")
  where "\<emptyset> \<equiv> some X. \<forall>x \<in> X. x \<notin> X"

lemma emptysetI: "\<forall>x \<in> \<emptyset>. x \<notin> \<emptyset>"
  unfolding emptyset_def using emptyset_ex some_setI[of "\<lambda>X. \<forall>x \<in> X. x \<notin> X"] by auto

lemma vacuous: "\<forall>x \<in> \<emptyset>. P(x)"
  using emptysetI by blast


definition singleton :: set ("\<one>")
  where "\<one> \<equiv> some X. \<exists>x \<in> X. \<forall>y \<in> X. y = x"

lemma singletonI: "\<exists>!x \<in> \<one>. \<forall>y \<in> \<one>. y = x"
  unfolding singleton_def using singleton_ex some_setI[of "\<lambda>X. \<exists>x \<in> X. \<forall>y \<in> X. y = x"] by auto

lemma singleton_all_eq: "\<lbrakk>x \<in> \<one>; y \<in> \<one>\<rbrakk> \<Longrightarrow> x = y"
  using singletonI by auto

definition pt :: elem
  where "pt \<equiv> the (x \<in> \<one>). \<forall>y \<in> \<one>. y = x"

lemma ptI [intro]: "pt \<in> \<one>"
  unfolding pt_def using singletonI the_elem_sort' by auto

lemma singletonD: "x \<in> \<one> \<Longrightarrow> x = pt"
  unfolding pt_def using the_elemI'[OF singletonI] by auto

lemma singletonE [elim]: "\<lbrakk>x \<in> \<one>; P(pt)\<rbrakk> \<Longrightarrow> P(x)"
  using singletonD by auto


text \<open>The unique function into the singleton \<one>\<close>

lemma singleton_terminal: "\<exists>!f: X \<succ> \<one>. f: X \<rightarrow> \<one>"
proof (auto intro: fun_ext appI singleton_all_eq[rule_format])
  obtain f where 1: "f: X \<succ> \<one>" and 2: "\<forall>x \<in> X. \<forall>y \<in> \<one>. (x f y) \<longleftrightarrow> y = pt"
    using rel_comprehension[of X \<one> "\<lambda>_ y. y = pt"] by blast
  then have "f: X \<rightarrow> \<one>" unfolding fun_def using 2[rule_format] ptI by auto
  thus "\<exists>f: X \<succ> \<one>. f: X \<rightarrow> \<one>" using 1 by auto
qed

definition terminal :: "set \<Rightarrow> rel" ("(terminal\<^bsub>_\<^esub>)")
  where "terminal\<^bsub>X\<^esub> \<equiv> the (f: X \<succ> \<one>). f: X \<rightarrow> \<one>"

lemma terminal_welldef: "terminal\<^bsub>X\<^esub>: X \<rightarrow> \<one>"
  unfolding terminal_def using singleton_terminal the_relI'[where ?P="\<lambda>f. f: X \<rightarrow> \<one>"] by auto

lemma terminal_constant: "\<forall>x \<in> X. \<forall>y \<in> X. terminal\<^bsub>X\<^esub>`x = terminal\<^bsub>X\<^esub>`y"
  using terminal_welldef appI singleton_all_eq by blast


section \<open>Subsets\<close>

definition subset :: "[rel, set] \<Rightarrow> bool" (infix "\<subseteq>" 50)
  where "S \<subseteq> A \<equiv> S: \<one> \<succ> A"

definition elem_subset :: "[elem, rel] \<Rightarrow> bool" (infix "\<in>" 50)
  where "a \<in> S \<equiv> pt S a"

abbreviation not_elem_subset :: "[elem, rel] \<Rightarrow> bool" (infix "\<notin>" 50)
  where "a \<notin> (S::rel) \<equiv> \<not> a \<in> S"

\<comment>\<open>Lots of overloading; may have to fix this later.\<close>

lemmas [iff] =
  subset_def
  elem_subset_def


subsection \<open>Empty and improper subsets\<close>

relation "emptysub(X): \<one> \<succ> X" where "(a emptysub x) \<longleftrightarrow> False"
notation emptysub ("\<emptyset>")

lemma emptysub_subsetI: "\<emptyset>(X) \<subseteq> X" by auto

lemma emptysub_empty: "\<forall>x \<in> X. x \<notin> \<emptyset>(X)" by auto


relation "impropersub(X): \<one> \<succ> X" where "(a impropersub x) \<longleftrightarrow> True"
notation impropersub ("whole")

lemma impropersub_subsetI: "whole(X) \<subseteq> X" by auto

lemma impropersub_full: "\<forall>x \<in> X. x \<in> whole(X)" by auto


\<comment>\<open>Work in progress!\<close>


end
