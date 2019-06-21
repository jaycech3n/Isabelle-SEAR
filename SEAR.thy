chapter \<open>Shulman's ``Sets, Elements, And Relations''\<close>

theory SEAR
imports
  HOL.HOL
  "HOL-Eisbach.Eisbach"
  "HOL-Eisbach.Eisbach_Tools"

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

(* HOL has `allE'`, would we want this? And what about the `atomize` rules? *)


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


declare
  the_set_equality [intro]
  the_elem_equality [intro]
  the_rel_equality [intro]
and
  the_set_equality' [elim?]
  the_elem_equality' [elim?]
  the_rel_equality' [elim?]


subsection \<open>Indefinite description for sets\<close>

axiomatization some_set :: "(set \<Rightarrow> bool) \<Rightarrow> set"
  where some_set_prop: "\<exists>X. P(X) \<Longrightarrow> P(some_set(\<lambda>x. P(x)))"

syntax "_some_set" :: "[set, bool] \<Rightarrow> set" ("(\<epsilon> _. _)")
translations "\<epsilon> X. P" \<rightleftharpoons> "CONST some_set (\<lambda>X. P)"


subsection \<open>Injectivity and surjectivity of relations\<close>

definition injective :: "[rel, set, set] \<Rightarrow> bool" ("(_ : _ \<succ> _ injective)")
  where "\<phi>: A \<succ> B injective \<equiv> \<forall>a \<in> A. \<forall>a' \<in> A. (\<exists>b \<in> B. (a \<phi> b) \<and> (a' \<phi> b)) \<longrightarrow> a = a'"

definition surjective :: "[rel, set, set] \<Rightarrow> bool" ("(_ : _ \<succ> _ surjective)")
  where "\<phi>: A \<succ> B surjective \<equiv> \<forall>b \<in> B. \<exists>a \<in> A. (a \<phi> b)"


subsection \<open>Functions\<close>

subsubsection \<open>Quantifiers\<close>

definition fun :: "[rel, set, set] \<Rightarrow> bool" ("(_ : _ \<rightarrow> _)"[51, 0, 51] 50)
  where "f: A \<rightarrow> B \<equiv> f: A \<succ> B \<and> (\<forall>x \<in> A. \<exists>!y \<in> B. (x f y))"

definition all_fun :: "[set, set, rel \<Rightarrow> bool] \<Rightarrow> bool"
  where "all_fun(A, B, P) \<equiv> ALL f. f: A \<rightarrow> B \<longrightarrow> P(f)"

abbreviation ex_fun :: "[set, set, rel \<Rightarrow> bool] \<Rightarrow> bool"
  where "ex_fun(A, B, P) \<equiv> EX f. f: A \<rightarrow> B \<and> P(f)"

abbreviation ex1_fun :: "[set, set, rel \<Rightarrow> bool] \<Rightarrow> bool"
  where "ex1_fun(A, B, P) \<equiv> EX! f. f: A \<rightarrow> B \<and> P(f)"

syntax
  "_all_fun"  :: "[idt, set, set, bool] \<Rightarrow> bool" ("(\<forall>_: _ \<rightarrow> _./ _)"[0, 0, 0, 10] 11)
  "_ex_fun"   :: "[idt, set, set, bool] \<Rightarrow> bool" ("(\<exists>_: _ \<rightarrow> _./ _)"[0, 0, 0, 10] 11)
  "_ex1_fun"  :: "[idt, set, set, bool] \<Rightarrow> bool" ("(\<exists>!_: _ \<rightarrow> _./ _)"[0, 0, 0, 10] 11)
translations
  "\<forall>f: A \<rightarrow> B. P"  \<rightleftharpoons> "CONST all_fun(A, B, \<lambda>f. P)"
  "\<exists>f: A \<rightarrow> B. P"  \<rightleftharpoons> "CONST ex_fun(A, B, \<lambda>f. P)"
  "\<exists>!f: A \<rightarrow> B. P" \<rightleftharpoons> "CONST ex1_fun(A, B, \<lambda>f. P)"


subsubsection \<open>Application\<close>

axiomatization app :: "[rel, elem] \<Rightarrow> elem" (infixl "`" 100)
  where fun_app_def: "f: A \<rightarrow> B \<Longrightarrow> f`x \<equiv> the (y \<in> B). (x f y)"

subsubsection \<open>Rules\<close>

lemma fun_rel: "f: A \<rightarrow> B \<Longrightarrow> f: A \<succ> B"
  unfolding fun_def by auto

lemma fun_uniq_val': "\<lbrakk>f: A \<rightarrow> B; x \<in> A\<rbrakk> \<Longrightarrow> \<exists>!y \<in> B. (x f y)"
  unfolding fun_def by blast

lemma fun_uniq_val:
  "\<lbrakk>f: A \<rightarrow> B; x \<in> A; y \<in> B; y' \<in> B; x f y; x f y'\<rbrakk> \<Longrightarrow> y = y'"
  by (auto dest: fun_uniq_val')

lemma fun_graph:
  assumes "f: A \<rightarrow> B" and "x \<in> A" 
  shows "x f (f`x)"
  using assms fun_uniq_val' fun_app_def the_elemI'[where ?P="\<lambda>y. (x f y)"]
  by auto

lemma appI:
  assumes "f: A \<rightarrow> B" and "x \<in> A" 
  shows "f`x \<in> B"
  using assms fun_rel fun_graph
  by (intro rel_cod)

lemma holds_app_iff:
  assumes "f: A \<rightarrow> B" and "x \<in> A" and "y \<in> B"
  shows "(x f y) \<longleftrightarrow> y = f`x"
  by (auto intro: assms fun_graph appI fun_uniq_val)


text \<open>Injectivity and surjectivity of functions\<close>

definition fun_inj :: "[rel, set, set] \<Rightarrow> bool" ("(_ : _ \<rightarrow> _ injective)")
  where "f: A \<rightarrow> B injective \<equiv> f: A \<rightarrow> B \<and> (\<forall>a \<in> A. \<forall>a' \<in> A. f`a = f`a' \<longrightarrow> a = a')"

definition fun_surj :: "[rel, set, set] \<Rightarrow> bool" ("(_ : _ \<rightarrow> _ surjective)")
  where "f: A \<rightarrow> B surjective \<equiv> f: A \<rightarrow> B \<and> (\<forall>b \<in> B. \<exists>a \<in> A. f`a = b)"

lemma fun_inj_implies_rel_inj: "f: A \<rightarrow> B injective \<Longrightarrow> f: A \<succ> B injective"
  sorry

lemma rel_inj_fun_implies_fun_inj: "\<lbrakk>f: A \<rightarrow> B; f: A \<succ> B injective\<rbrakk> \<Longrightarrow> f: A \<rightarrow> B injective"
  sorry


section \<open>Axioms\<close>

axiomatization where

  existence: "\<exists>X. EX x. x \<in> X" and

  rel_comprehension: "\<exists>!\<phi>: A \<succ> B. \<forall>x \<in> A. \<forall>y \<in> B. (x \<phi> y) \<longleftrightarrow> P(x, y)"

text \<open>
A tabulation is a reflection of relations into sets.
The third axiom states that tabulations exist.
\<close>

abbreviation (input) is_tabulation_of :: "[set, rel, rel, rel, set, set] \<Rightarrow> bool"
  ("(_, _, _ is'_tabulation'_of _ : _ \<succ> _)")
where
  "T, f1, f2 is_tabulation_of \<phi>: A \<succ> B \<equiv>
    f1: T \<rightarrow> A \<and>
    f2: T \<rightarrow> B \<and>
    (\<forall>x \<in> A. \<forall>y \<in> B. \<phi>(x, y) \<longleftrightarrow> (\<exists>t \<in> T. f1[t] = x \<and> f2[t] = y)) \<and>
    (\<forall>s \<in> T. \<forall>t \<in> T. f1[s] = f1[t] \<and> f2[s] = f2[t] \<longrightarrow> s = t)"

axiomatization
  tab :: "rel \<Rightarrow> set" ("|_|") and
  fst :: "rel \<Rightarrow> rel" ("|_|\<^sub>1") and
  snd :: "rel \<Rightarrow> rel" ("|_|\<^sub>2") where

  tabulation: "\<forall>\<phi>: A \<succ> B. |\<phi>|, |\<phi>|\<^sub>1, |\<phi>|\<^sub>2 is_tabulation_of \<phi>: A \<succ> B"

corollary fst_is_fun: "\<phi>: A \<succ> B \<Longrightarrow> |\<phi>|\<^sub>1: |\<phi>| \<rightarrow> A" using tabulation by auto

corollary snd_is_fun: "\<phi>: A \<succ> B \<Longrightarrow> |\<phi>|\<^sub>2: |\<phi>| \<rightarrow> B" using tabulation by auto

corollary tab_sufficient:
  "\<phi>: A \<succ> B \<Longrightarrow> \<forall>x \<in> A. \<forall>y \<in> B. \<phi>(x, y) \<longleftrightarrow> (\<exists>r \<in> |\<phi>|. |\<phi>|\<^sub>1[r] = x \<and> |\<phi>|\<^sub>2[r] = y)"
    using tabulation by auto

corollary tab_minimal:
  "\<phi>: A \<succ> B \<Longrightarrow> \<forall>r \<in> |\<phi>|. \<forall>s \<in> |\<phi>|. |\<phi>|\<^sub>1[r] = |\<phi>|\<^sub>1[s] \<and> |\<phi>|\<^sub>2[r] = |\<phi>|\<^sub>2[s] \<longrightarrow> r = s"
    using tabulation by blast


section \<open>Basic definitions and results\<close>

subsection \<open>Function extensionality\<close>

lemma fun_ext: "\<forall>f: A \<rightarrow> B. \<forall>g: A \<rightarrow> B. (\<forall>x \<in> A. f[x] = g[x]) \<longrightarrow> f = g"
proof -
  { fix f g :: rel assume
  f_fun: "f: A \<rightarrow> B" and
  g_fun: "g: A \<rightarrow> B" and
  ptwise_eq: "\<forall>x \<in> A. f[x] = g[x]"

  have lemma_1:
  "\<forall>x \<in> A. \<forall>y \<in> B. f(x, y) \<longleftrightarrow> g(x, y)"
  proof -
    { fix x y assume
    x_elem: "x \<in> A" and
    y_elem: "y \<in> B"
    hence "f(x, y) \<longleftrightarrow> y = f[x]"
      using holds_fun_app_equiv f_fun by auto
    moreover have "y = g[x] \<longleftrightarrow> g(x, y)"
      using holds_fun_app_equiv g_fun x_elem y_elem by auto
    ultimately have "f(x, y) \<longleftrightarrow> g(x, y)"
      using ptwise_eq x_elem by simp
    }
    thus ?thesis by auto
  qed

  have easy_observation:
  "\<forall>x \<in> A. \<forall>y \<in> B. g(x, y) \<longleftrightarrow> g(x, y)"
    by simp

  with rel_comprehension[where P="\<lambda>x y. g(x, y)"] lemma_1 have
  "f = g"
    using f_fun g_fun by blast
  }
  thus ?thesis by auto
qed


subsection \<open>Empty and singleton sets\<close>

theorem emptyset_exists: "\<exists>X. \<forall>x \<in> X. x \<notin> X"
proof -
  from existence obtain a A where "a \<in> A" by auto

  from rel_comprehension[of A A "\<lambda>_ _. False"] obtain \<phi> where
  \<phi>_rel: "\<phi>: A \<succ> A" and "\<forall>x \<in> A. \<forall>y \<in> A. \<not>\<phi>(x, y)"
    by auto
  with tabulation have
  lemma_1: "\<forall>x \<in> A. \<forall>y \<in> A. \<not>(\<exists>r \<in> |\<phi>|. |\<phi>|\<^sub>1[r] = x \<and> |\<phi>|\<^sub>2[r] = y)"
    by auto

  have "\<forall>r \<in> |\<phi>|. r \<notin> |\<phi>|"
  proof -
    { fix r assume for_contradiction: "r \<in> |\<phi>|"
    then have "|\<phi>|\<^sub>1[r] \<in> A" and "|\<phi>|\<^sub>2[r] \<in> A"
      using
        fst_is_fun[OF \<phi>_rel]
        snd_is_fun[OF \<phi>_rel]
        fun_image_elem_of
      by auto
    hence
    nonexistence: "\<not>(\<exists>r' \<in> |\<phi>|. |\<phi>|\<^sub>1[r'] = |\<phi>|\<^sub>1[r] \<and> |\<phi>|\<^sub>2[r'] = |\<phi>|\<^sub>2[r])"
      using lemma_1 by auto

    from for_contradiction have
    "\<exists>r' \<in> |\<phi>|. |\<phi>|\<^sub>1[r'] = |\<phi>|\<^sub>1[r] \<and> |\<phi>|\<^sub>2[r'] = |\<phi>|\<^sub>2[r]"
      by auto

    hence False using nonexistence by auto
    }
    thus "\<forall>x \<in> |\<phi>|. x \<notin> |\<phi>|"
      by auto
  qed
  thus ?thesis ..
qed

theorem singleton_exists: "\<exists>X. \<exists>x \<in> X. \<forall>y \<in> X. y = x"
proof -
  from existence obtain a A where
  a_in_A: "a \<in> A" by auto

  from rel_comprehension[of A A "\<lambda>x y. x = a \<and> y = a"]
  obtain \<phi> where
  \<phi>_rel: "\<phi>: A \<succ> A" and "\<forall>x \<in> A. \<forall>y \<in> A. \<phi>(x, y) \<longleftrightarrow> x = a \<and> y = a"
    by auto
  with tabulation have
  lemma_1: "\<forall>x \<in> A. \<forall>y \<in> A. x = a \<and> y = a \<longleftrightarrow> (\<exists>r \<in> |\<phi>|. |\<phi>|\<^sub>1[r] = x \<and> |\<phi>|\<^sub>2[r] = y)"
    by auto
  then obtain r where
  r_elem: "r \<in> |\<phi>|" and "|\<phi>|\<^sub>1[r] = a \<and> |\<phi>|\<^sub>2[r] = a"
    using a_in_A by auto

  have "\<forall>r \<in> |\<phi>|. |\<phi>|\<^sub>1[r] = a \<and> |\<phi>|\<^sub>2[r] = a"
  proof -
    { fix r assume r_elem: "r \<in> |\<phi>|"
    then have "|\<phi>|\<^sub>1[r] \<in> A" and "|\<phi>|\<^sub>2[r] \<in> A"
      using
        fst_is_fun[OF \<phi>_rel]
        snd_is_fun[OF \<phi>_rel]
        fun_image_elem_of
      by auto
    with lemma_1 have "|\<phi>|\<^sub>1[r] = a \<and> |\<phi>|\<^sub>2[r] = a"
      using r_elem by auto
    }
    thus ?thesis by auto
  qed

  with tab_minimal[OF \<phi>_rel] have "\<forall>s \<in> |\<phi>|. r = s" using r_elem by auto
  thus ?thesis using r_elem by auto
qed

text \<open>Fix particular choices of empty and singleton set.\<close>

definition emptyset :: set ("\<emptyset>")
  where "\<emptyset> \<equiv> \<epsilon>set X | \<forall>x \<in> X. x \<notin> X"

definition singleton :: set ("\<one>")
  where "\<one> \<equiv> \<epsilon>set X | \<exists>x \<in> X. \<forall>y \<in> X. y = x"

theorem emptyset_prop: "\<forall>x \<in> \<emptyset>. x \<notin> \<emptyset>"
  using emptyset_exists emptyset_def some_set_def[of "\<lambda>X. \<forall>x \<in> X. x \<notin> X"]
  by auto

theorem vacuous: "\<forall>x \<in> \<emptyset>. P x"
proof -
  { fix x assume assm: "x \<in> \<emptyset>"
  hence "x \<notin> \<emptyset>" using emptyset_prop by auto
  hence "P x" using assm by auto
  }
  thus ?thesis by auto
qed

theorem singleton_prop: "\<exists>x \<in> \<one>. \<forall>y \<in> \<one>. y = x"
  using singleton_exists singleton_def some_set_def[of "\<lambda>X. \<exists>x \<in> X. \<forall>y \<in> X. y = x"]
  by auto

lemma singleton_all_eq: "\<forall>x \<in> \<one>. \<forall>y \<in> \<one>. x = y"
proof -
  from singleton_prop obtain pt where lemma_1:
  "\<forall>x \<in> \<one>. pt = x" by auto
  { fix x y assume "x \<in> \<one>" and "y \<in> \<one>"
  with lemma_1 have "pt = x" and "pt = y" by auto
  hence "x = y" by simp
  }
  thus ?thesis by auto
qed


subsection \<open>The unique function into the singleton \<one>\<close>

lemma singleton_terminal: "EX! f. f: X \<rightarrow> \<one>"
proof
  from singleton_prop
  obtain pt where
  pt_elem: "pt \<in> \<one>"
    by auto
  from rel_comprehension[of X \<one> "\<lambda>_ y. y = pt"]
  obtain f where
  f_rel: "f: X \<succ> \<one>" and
  f_def: "\<forall>x \<in> X. \<forall>y \<in> \<one>. f(x, y) \<longleftrightarrow> y = pt"
    by auto
  thus "EX f. f: X \<rightarrow> \<one>"
    using pt_elem by blast

  fix f g assume
  f_fun: "f: X \<rightarrow> \<one>" and
  g_fun: "g: X \<rightarrow> \<one>"
  have
  "\<forall>x \<in> X. f[x] = g[x]"
    using
      fun_image_elem_of[OF f_fun]
      fun_image_elem_of[OF g_fun]
      singleton_all_eq
    by auto
  with fun_ext show "f = g"
    using f_fun g_fun by auto
qed

definition terminal :: "set \<Rightarrow> rel" ("(terminal\<^bsub>_\<^esub>)")
  where "terminal\<^bsub>X\<^esub> \<equiv> \<iota>rel f: X \<succ> \<one> | (f: X \<rightarrow> \<one>)"

lemma terminal_well_def: "terminal\<^bsub>X\<^esub>: X \<rightarrow> \<one>"
  unfolding terminal_def
  using
    the_rel_sat[of X \<one> "\<lambda>f. f: X \<rightarrow> \<one>"]
    singleton_terminal
  by auto

lemma terminal_constant: "\<forall>x \<in> X. \<forall>y \<in> X. terminal\<^bsub>X\<^esub>[x] = terminal\<^bsub>X\<^esub>[y]"
  using
    terminal_well_def[of X]
    fun_image_elem_of
    singleton_all_eq
  by blast


subsection \<open>Subsets\<close>

text \<open>
Differently from Shulman, we define subsets as tabulations satisfying certain properties.
\<close>

definition subset_of :: "[set, set] \<Rightarrow> bool" (infix "\<subseteq>" 50)
  where "B \<subseteq> A \<equiv>
    \<exists>S: \<one> \<succ> A. EX i. (i: B \<rightarrow> A injective) \<and> (\<forall>pt \<in> \<one>. \<forall>a \<in> A. S(pt, a) \<longleftrightarrow> (\<exists>b \<in> B. i[b] = a))"

lemma subsets_are_tabulations:
  "B \<subseteq> A \<Longrightarrow> \<exists>S: \<one> \<succ> A. \<exists>i: B \<rightarrow> A. (B, terminal\<^bsub>B\<^esub>, i is_tabulation_of S: \<one> \<succ> A)" and
  "\<exists>S: \<one> \<succ> A. \<exists>i: B \<rightarrow> A. (B, terminal\<^bsub>B\<^esub>, i is_tabulation_of S: \<one> \<succ> A) \<Longrightarrow> B \<subseteq> A"
proof -
  assume B_subset_of_A: "B \<subseteq> A"
  then show "\<exists>S: \<one> \<succ> A. \<exists>i: B \<rightarrow> A. (B, terminal\<^bsub>B\<^esub>, i is_tabulation_of S: \<one> \<succ> A)"
  proof -
    have auxiliary_lemma:
    "\<forall>i: B \<rightarrow> A. \<forall>pt \<in> \<one>. \<forall>a \<in> A. (\<exists>b \<in> B. i[b] = a) \<longleftrightarrow> (\<exists>b \<in> B. terminal\<^bsub>B\<^esub>[b] = pt \<and> i[b] = a)"
    proof -
      { fix i pt a assume
      pt_elem: "pt \<in> \<one>"

      have \<Longrightarrow>: "(\<exists>b \<in> B. i[b] = a) \<Longrightarrow> (\<exists>b \<in> B. terminal\<^bsub>B\<^esub>[b] = pt \<and> i[b] = a)"
      proof -
        assume a_in_range_of_i: "\<exists>b \<in> B. i[b] = a"
        then obtain b where
        b_elem: "b \<in> B" and
        b_mapsto_a: "i[b] = a"
          by auto
        have
        "terminal\<^bsub>B\<^esub>[b] = pt"
          using
            fun_image_elem_of[OF terminal_well_def b_elem]
            pt_elem
            singleton_all_eq
          by auto
        thus "\<exists>b \<in> B. terminal\<^bsub>B\<^esub>[b] = pt \<and> i[b] = a"
          using b_elem b_mapsto_a by auto
      qed
      moreover have \<Longleftarrow>: "(\<exists>b \<in> B. terminal\<^bsub>B\<^esub>[b] = pt \<and> i[b] = a) \<Longrightarrow> (\<exists>b \<in> B. i[b] = a)"
        by auto
      ultimately have "(\<exists>b \<in> B. i[b] = a) \<longleftrightarrow> (\<exists>b \<in> B. terminal\<^bsub>B\<^esub>[b] = pt \<and> i[b] = a)" ..
      }
      thus ?thesis by auto
    qed

    from B_subset_of_A obtain S and i where
    S_rel: "S: \<one> \<succ> A" and
    i_inj: "i: B \<rightarrow> A injective" and
    lemma_1: "\<forall>pt \<in> \<one>. \<forall>a \<in> A. S(pt, a) \<longleftrightarrow> (\<exists>b \<in> B. i[b] = a)"
      unfolding subset_of_def by auto

    have i_fun: "i: B \<rightarrow> A" by (fact conjunct1[OF i_inj[unfolded fun_inj_def]])

    moreover have sufficiency:
    "\<forall>pt \<in> \<one>. \<forall>a \<in> A. S(pt, a) \<longleftrightarrow> (\<exists>b \<in> B. terminal\<^bsub>B\<^esub>[b] = pt \<and> i[b] = a)"
    proof -
      { fix pt a assume
      pt_elem: "pt \<in> \<one>" and
      a_elem: "a \<in> A"
  
      with lemma_1 have
      "S(pt, a) \<longleftrightarrow> (\<exists>b \<in> B. i[b] = a)"
        by auto
      with auxiliary_lemma[rule_format, of i pt a] have
      "S(pt, a) \<longleftrightarrow> (\<exists>b \<in> B. terminal\<^bsub>B\<^esub>[b] = pt \<and> i[b] = a)"
        using i_fun pt_elem a_elem
        by auto
      }
      thus ?thesis by auto
    qed

    moreover have minimality:
    "\<forall>b \<in> B. \<forall>b' \<in> B. terminal\<^bsub>B\<^esub>[b] = terminal\<^bsub>B\<^esub>[b'] \<and> i[b] = i[b'] \<longrightarrow> b = b'"
    proof -
      { fix b b' assume
      b_elem: "b \<in> B" and
      b'_elem: "b' \<in> B"
      then have "terminal\<^bsub>B\<^esub>[b] = terminal\<^bsub>B\<^esub>[b'] \<and> i[b] = i[b'] \<longrightarrow> b = b'"
        using
          conjunct2[OF i_inj[unfolded fun_inj_def]]
          terminal_constant
        by blast
      }
      thus ?thesis by auto
    qed

    ultimately have "B, terminal\<^bsub>B\<^esub>, i is_tabulation_of S: \<one> \<succ> A"
      using terminal_well_def by auto

    thus ?thesis using S_rel by auto
  qed

  next assume "\<exists>S: \<one> \<succ> A. \<exists>i: B \<rightarrow> A. (B, terminal\<^bsub>B\<^esub>, i is_tabulation_of S: \<one> \<succ> A)"
  show "B \<subseteq> A" unfolding subset_of_def
    
    sorry
qed


end
