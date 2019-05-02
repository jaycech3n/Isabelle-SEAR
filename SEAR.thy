theory SEAR
imports FOL_Base

begin

text \<open>
Shulman's Sets, Elements, And Relations, formulated as a theory of many-sorted first-order logic.
\<close>

declare[[eta_contract=false]]


section \<open>Logical foundations\<close>

subsection \<open>Meta\<close>

text \<open>
For meta-level nondependent typing: terms are divided into three meta-types.
We (are forced to) lump the dependent sorts of "elements of X" for each set X into a single meta-type @{text elem}, and the sorts "relations from A to B" for each pair of sets A, B into the meta-type @{text rel}.
The finer distinction of each dependent sort has to be done on the object level.
\<close>

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

no_notation
  All (binder "\<forall>" 10) and
  Ex  (binder "\<exists>" 10) and
  Ex1 (binder "\<exists>!" 10)
notation
  All (binder "\<forall>\<forall>" 10) and
  Ex  (binder "\<exists>\<exists>" 10) and
  Ex1 (binder "\<exists>\<exists>!" 10)

abbreviation all_set :: "(set \<Rightarrow> o) \<Rightarrow> o" (binder "\<forall>" 10)
  where "\<forall>x. P x \<equiv> \<forall>\<forall>x::set. P x"

abbreviation ex_set :: "(set \<Rightarrow> o) \<Rightarrow> o" (binder "\<exists>" 10)
  where "\<exists>x. P x \<equiv> \<exists>\<exists>x::set. P x"

abbreviation ex1_set :: "(set \<Rightarrow> o) \<Rightarrow> o" (binder "\<exists>!" 10)
  where "\<exists>!x. P x \<equiv> \<exists>\<exists>!x::set. P x"

abbreviation all_elem :: "[set, elem \<Rightarrow> o] \<Rightarrow> o"
  where "all_elem X P \<equiv> \<forall>\<forall>x. x: X \<longrightarrow> P x"

abbreviation ex_elem :: "[set, elem \<Rightarrow> o] \<Rightarrow> o"
  where "ex_elem X P \<equiv> \<exists>\<exists>x. x: X \<and> P x"

abbreviation ex1_elem :: "[set, elem \<Rightarrow> o] \<Rightarrow> o"
  where "ex1_elem X P \<equiv> \<exists>\<exists>!x. x: X \<and> P x"

abbreviation all_rel :: "[set, set, rel \<Rightarrow> o] \<Rightarrow> o"
  where "all_rel A B P \<equiv> \<forall>\<forall>\<phi>. \<phi>: A \<succ> B \<longrightarrow> P \<phi>"

abbreviation ex_rel :: "[set, set, rel \<Rightarrow> o] \<Rightarrow> o"
  where "ex_rel A B P \<equiv> \<exists>\<exists>\<phi>. \<phi>: A \<succ> B \<and> P \<phi>"

abbreviation ex1_rel :: "[set, set, rel \<Rightarrow> o] \<Rightarrow> o"
  where "ex1_rel A B P \<equiv> \<exists>\<exists>!\<phi>. \<phi>: A \<succ> B \<and> P \<phi>"

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
  holds   :: "[rel, elem, elem] \<Rightarrow> o" ("(_'(_, _'))" [100, 0, 0]) where

  elem_of_sort: "x \<in> X \<Longrightarrow> x: X" and
  holds_dom_sort: "\<lbrakk>\<phi>: A \<succ> B; \<phi>(x, y)\<rbrakk> \<Longrightarrow> x: A" and
  holds_codom_sort: "\<lbrakk>\<phi>: A \<succ> B; \<phi>(x, y)\<rbrakk> \<Longrightarrow> y: B"

abbreviation "not_elem_of" :: "[elem, set] \<Rightarrow> o" (infix "\<notin>" 50)
  where "x \<notin> X \<equiv> \<not> x \<in> X"

lemma all_elem_of_simp:
  assumes "\<forall>x: X. x \<in> X \<longrightarrow> P x"
  shows "\<forall>\<forall>x. x \<in> X \<longrightarrow> P x"
  using assms elem_of_sort by auto

lemma all_elem_of_restr:
  assumes "\<forall>\<forall>x. x \<in> X \<longrightarrow> P x"
  shows "\<forall>x: X. x \<in> X \<longrightarrow> P x"
  using assms by auto


subsubsection \<open>Definite description\<close>

axiomatization
  the_set  :: "(set \<Rightarrow> o) \<Rightarrow> set" and
  the_elem :: "[set, elem \<Rightarrow> o] \<Rightarrow> elem" and
  the_rel  :: "[set, set, rel \<Rightarrow> o] \<Rightarrow> rel" where

  the_set_def: "\<exists>!X. P X \<Longrightarrow> P (the_set P)" and
  the_elem_def: "\<exists>!x: X. Q x \<Longrightarrow> Q (the_elem X Q)" and
  the_rel_def: "\<exists>!\<phi>: A \<succ> B. R \<phi> \<Longrightarrow> R (the_rel A B R)"

syntax
  "_the_set"  :: "[set, o] \<Rightarrow> set" ("(\<iota>set  _ | _)")
  "_the_elem" :: "[elem, set, o] \<Rightarrow> elem" ("(\<iota>elem _ : _ | _)")
  "_the_rel"  :: "[rel, set, set, o] \<Rightarrow> rel" ("(\<iota>rel _ : _ \<succ> _ | _)")
translations
  "\<iota>set X | P" \<rightleftharpoons> "CONST the_set (\<lambda>X. P)"
  "\<iota>elem x: X | Q" \<rightleftharpoons> "CONST the_elem X (\<lambda>x. Q)"
  "\<iota>rel \<phi>: A \<succ> B | R" \<rightleftharpoons> "CONST the_rel A B (\<lambda>\<phi>. R)"


subsubsection \<open>Functions\<close>

abbreviation (input) is_func :: "[rel, set, set] \<Rightarrow> o" ("(_ : _ \<rightarrow> _)" [41, 0, 41] 40)
  where "\<phi>: A \<rightarrow> B \<equiv> \<phi>: A \<succ> B \<and> (\<forall>x: A. x \<in> A \<longrightarrow> (\<exists>!y: B. \<phi>(x, y)))"

axiomatization func_app :: "[rel, elem] \<Rightarrow> elem" ("(_'(_'))" [100, 0])
  where func_app_def: "\<phi>: A \<succ> B \<Longrightarrow> \<phi>(x) \<equiv> \<iota>elem y: B | \<phi>(x, y)"

lemma func_image:
  assumes "\<phi>: A \<rightarrow> B" and "x \<in> A" 
  shows "\<phi>(x, \<phi>(x))"
proof (subst func_app_def)
  show "\<phi>(x, \<iota>elem y: B | \<phi>(x, y))"
  proof (rule the_elem_def, auto simp: assms)
    from assms(1) have "\<forall>\<forall>x. x \<in> A \<longrightarrow> (\<exists>!y: B. \<phi>(x, y))"
      using all_elem_of_simp[of A "\<lambda>x. \<exists>!y: B. \<phi>(x, y)"] by auto
    with assms(2) have
      unique_image: "\<exists>!y: B. \<phi>(x, y)" by auto
    thus "\<exists>y: B. \<phi>(x, y)" by auto

    fix y y' assume "y: B" "y': B" "\<phi>(x, y)" "\<phi>(x, y')"
    thus "y = y'" using unique_image by auto
  qed

  show "\<phi>: A \<succ> B" using assms(1) by auto
qed

lemma func_image_sort:
  assumes "\<phi>: A \<rightarrow> B" and "x \<in> A" 
  shows "(\<phi>::rel)(x): B"
  using assms func_image holds_codom_sort by blast


section \<open>Axioms\<close>

axiomatization where

  existence: "\<exists>X. \<exists>x: X. x \<in> X" and

  comprehension: "\<exists>!\<phi>: A \<succ> B. \<forall>x: A. \<forall>y: B. \<phi>(x, y) \<longleftrightarrow> P x y"

axiomatization
  tab :: "rel \<Rightarrow> set" ("|_|") and
  fst :: "rel \<Rightarrow> rel" ("|_|\<^sub>1") and
  snd :: "rel \<Rightarrow> rel" ("|_|\<^sub>2")where

  tabulation:
    "\<forall>\<phi>: A \<succ> B.
      |\<phi>|\<^sub>1: |\<phi>| \<rightarrow> A \<and>
      |\<phi>|\<^sub>2: |\<phi>| \<rightarrow> B \<and>
      (\<forall>x: A. \<forall>y: B. \<phi>(x, y) \<longleftrightarrow> (\<exists>r: |\<phi>|. |\<phi>|\<^sub>1(r) = x \<and> |\<phi>|\<^sub>2(r) = y)) \<and>
      (\<forall>r: |\<phi>|. \<forall>s: |\<phi>|. |\<phi>|\<^sub>1(r) = |\<phi>|\<^sub>1(s) \<and> |\<phi>|\<^sub>2(r) = |\<phi>|\<^sub>2(s) \<longrightarrow> r = s)"

corollary fst_is_func: "\<phi>: A \<succ> B \<Longrightarrow> |\<phi>|\<^sub>1: |\<phi>| \<rightarrow> A" using tabulation by auto

corollary snd_is_func: "\<phi>: A \<succ> B \<Longrightarrow> |\<phi>|\<^sub>2: |\<phi>| \<rightarrow> B" using tabulation by auto

corollary tab_sufficiency:
  "\<phi>: A \<succ> B \<Longrightarrow> \<forall>x: A. \<forall>y: B. \<phi>(x, y) \<longleftrightarrow> (\<exists>r: |\<phi>|. |\<phi>|\<^sub>1(r) = x \<and> |\<phi>|\<^sub>2(r) = y)"
  using tabulation by auto

corollary tab_minimality:
  "\<phi>: A \<succ> B \<Longrightarrow> \<forall>r: |\<phi>|. \<forall>s: |\<phi>|. |\<phi>|\<^sub>1(r) = |\<phi>|\<^sub>1(s) \<and> |\<phi>|\<^sub>2(r) = |\<phi>|\<^sub>2(s) \<longrightarrow> r = s"
  using tabulation by blast


subsection \<open>Basic consequences of the first three axioms\<close>

theorem emptyset: "\<exists>X. \<forall>x: X. x \<notin> X"
proof -
  from existence obtain a A where "a \<in> A" by auto

  from comprehension[of A A "\<lambda>_ _. False"] obtain \<phi> where
    \<phi>_sort: "\<phi>: A \<succ> A" and "\<forall>x: A. \<forall>y: A. \<not>\<phi>(x, y)"
      by auto
  with tab_sufficiency have
    lemma_1: "\<forall>x: A. \<forall>y: A. \<not>(\<exists>r: |\<phi>|. |\<phi>|\<^sub>1(r) = x \<and> |\<phi>|\<^sub>2(r) = y)"
      by auto

  have "\<forall>r: |\<phi>|. r \<notin> |\<phi>|"
  proof -
    {
    fix r assume r_sort: "r: |\<phi>|"

    assume for_contradiction: "r \<in> |\<phi>|"
    then have "|\<phi>|\<^sub>1(r): A" and "|\<phi>|\<^sub>2(r): A"
      using
        fst_is_func[of \<phi>, OF \<phi>_sort]
        snd_is_func[of \<phi>, OF \<phi>_sort]
        func_image_sort
      by auto
    hence nonexistence: "\<not>(\<exists>r': |\<phi>|. |\<phi>|\<^sub>1(r') = |\<phi>|\<^sub>1(r) \<and> |\<phi>|\<^sub>2(r') = |\<phi>|\<^sub>2(r))"
      using lemma_1 by auto

    from r_sort have
      "\<exists>r': |\<phi>|. |\<phi>|\<^sub>1(r') = |\<phi>|\<^sub>1(r) \<and> |\<phi>|\<^sub>2(r') = |\<phi>|\<^sub>2(r)"
        by auto
    hence False using nonexistence by auto
    }
    thus "\<forall>x: |\<phi>|. x \<notin> |\<phi>|" by auto
  qed

  thus ?thesis by auto
qed


end
