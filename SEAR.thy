theory SEAR
imports FOL_Base

begin

text \<open>
Shulman's Sets, Elements, And Relations, formulated as a theory of triply-sorted first-order logic.
\<close>

declare[[eta_contract=false]]


section \<open>Logical foundations\<close>

subsection \<open>Meta\<close>

class Sort

typedecl set
instance set :: Sort ..

typedecl elem
instance elem :: Sort ..

typedecl rel
instance rel :: Sort ..


subsection \<open>Sorted FOL and set theory\<close>

subsubsection \<open>Basic judgments\<close>

axiomatization
  elem_of :: "[elem, set] \<Rightarrow> o" (infix "\<in>" 50) and
  rel_of  :: "[rel, set, set] \<Rightarrow> o" ("(_ : _ \<succ> _)" [51, 0, 51] 50) and
  holds   :: "[rel, elem, elem] \<Rightarrow> o" ("(_'(_, _'))" [100, 0, 0]) where

  holds_dom: "\<lbrakk>\<phi>: A \<succ> B; \<phi>(x, y)\<rbrakk> \<Longrightarrow> x \<in> A" and
  holds_codom: "\<lbrakk>\<phi>: A \<succ> B; \<phi>(x, y)\<rbrakk> \<Longrightarrow> y \<in> B"

abbreviation "not_elem_of" :: "[elem, set] \<Rightarrow> o" (infix "\<notin>" 50)
  where "x \<notin> X \<equiv> \<not> x \<in> X"


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
  where "all_elem X P \<equiv> \<forall>\<forall>x. x \<in> X \<longrightarrow> P x"

abbreviation ex_elem :: "[set, elem \<Rightarrow> o] \<Rightarrow> o"
  where "ex_elem X P \<equiv> \<exists>\<exists>x. x \<in> X \<and> P x"

abbreviation ex1_elem :: "[set, elem \<Rightarrow> o] \<Rightarrow> o"
  where "ex1_elem X P \<equiv> \<exists>\<exists>!x. x \<in> X \<and> P x"

abbreviation all_rel :: "[set, set, rel \<Rightarrow> o] \<Rightarrow> o"
  where "all_rel A B P \<equiv> \<forall>\<forall>\<phi>. \<phi>: A \<succ> B \<longrightarrow> P \<phi>"

abbreviation ex_rel :: "[set, set, rel \<Rightarrow> o] \<Rightarrow> o"
  where "ex_rel A B P \<equiv> \<exists>\<exists>\<phi>. \<phi>: A \<succ> B \<and> P \<phi>"

abbreviation ex1_rel :: "[set, set, rel \<Rightarrow> o] \<Rightarrow> o"
  where "ex1_rel A B P \<equiv> \<exists>\<exists>!\<phi>. \<phi>: A \<succ> B \<and> P \<phi>"

syntax
  "_all_elem" :: "[idt, set, o] \<Rightarrow> o" ("(\<forall>_ \<in> _./ _)" [0, 0, 10] 11)
  "_ex_elem"  :: "[idt, set, o] \<Rightarrow> o" ("(\<exists>_ \<in> _./ _)" [0, 0, 10] 11)
  "_ex1_elem" :: "[idt, set, o] \<Rightarrow> o" ("(\<exists>!_ \<in> _./ _)" [0, 0, 10] 11)
  "_all_rel"  :: "[idt, set, set, o] \<Rightarrow> o" ("(\<forall>_: _ \<succ> _./ _)" [0, 0, 0, 10] 11)
  "_ex_rel"   :: "[idt, set, set, o] \<Rightarrow> o" ("(\<exists>_: _ \<succ> _./ _)" [0, 0, 0, 10] 11)
  "_ex1_rel"  :: "[idt, set, set, o] \<Rightarrow> o" ("(\<exists>!_: _ \<succ> _./ _)" [0, 0, 0, 10] 11)
translations
  "\<forall>x \<in> X. P"  \<rightleftharpoons> "CONST all_elem X (\<lambda>x. P)"
  "\<exists>x \<in> X. P"  \<rightleftharpoons> "CONST ex_elem X (\<lambda>x. P)"
  "\<exists>!x \<in> X. P" \<rightleftharpoons> "CONST ex1_elem X (\<lambda>x. P)"
  "\<forall>\<phi>: A \<succ> B. P"  \<rightleftharpoons> "CONST all_rel A B (\<lambda>\<phi>. P)"
  "\<exists>\<phi>: A \<succ> B. P"  \<rightleftharpoons> "CONST ex_rel A B (\<lambda>\<phi>. P)"
  "\<exists>!\<phi>: A \<succ> B. P" \<rightleftharpoons> "CONST ex1_rel A B (\<lambda>\<phi>. P)"


subsubsection \<open>Definite description\<close>

axiomatization
  the_set  :: "(set \<Rightarrow> o) \<Rightarrow> set" and
  the_elem :: "[set, elem \<Rightarrow> o] \<Rightarrow> elem" and
  the_rel  :: "[set, set, rel \<Rightarrow> o] \<Rightarrow> rel" where

  the_set_def: "\<exists>!X. P X \<Longrightarrow> P (the_set P)" and

  the_elem_elem_of: "\<exists>!x \<in> X. Q x \<Longrightarrow> the_elem X Q \<in> X" and
  the_elem_sat: "\<exists>!x \<in> X. Q x \<Longrightarrow> Q (the_elem X Q)" and

  the_rel_sort: "\<exists>!\<phi>: A \<succ> B. R \<phi> \<Longrightarrow> the_rel A B R: A \<succ> B" and
  the_rel_sat: "\<exists>!\<phi>: A \<succ> B. R \<phi> \<Longrightarrow> R (the_rel A B R)"

syntax
  "_the_set"  :: "[set, o] \<Rightarrow> set" ("(\<iota>set  _ | _)")
  "_the_elem" :: "[elem, set, o] \<Rightarrow> elem" ("(\<iota>elem _ \<in> _ | _)")
  "_the_rel"  :: "[rel, set, set, o] \<Rightarrow> rel" ("(\<iota>rel _ : _ \<succ> _ | _)")
translations
  "\<iota>set X | P" \<rightleftharpoons> "CONST the_set (\<lambda>X. P)"
  "\<iota>elem x \<in> X | Q" \<rightleftharpoons> "CONST the_elem X (\<lambda>x. Q)"
  "\<iota>rel \<phi>: A \<succ> B | R" \<rightleftharpoons> "CONST the_rel A B (\<lambda>\<phi>. R)"


subsubsection \<open>Indefinite description for sets\<close>

axiomatization some_set :: "(set \<Rightarrow> o) \<Rightarrow> set" where
  some_set_def: "\<exists>X. P X \<Longrightarrow> P (some_set P)"

syntax "_some_set" :: "[set, o] \<Rightarrow> set" ("(\<epsilon>set _ | _)")
translations "\<epsilon>set X | P" \<rightleftharpoons> "CONST some_set (\<lambda>X. P)"


subsubsection \<open>Functions\<close>

abbreviation is_func :: "[rel, set, set] \<Rightarrow> o" ("(_ : _ \<rightarrow> _)" [41, 0, 41] 40)
  where "\<phi>: A \<rightarrow> B \<equiv> \<phi>: A \<succ> B \<and> (\<forall>x \<in> A. \<exists>!y \<in> B. \<phi>(x, y))"

axiomatization func_app :: "[rel, elem] \<Rightarrow> elem" ("(_'(_'))" [100, 0])
  where func_app_def: "\<phi>: A \<rightarrow> B \<Longrightarrow> \<phi>(x) \<equiv> \<iota>elem y \<in> B | \<phi>(x, y)"

lemma func_image:
  assumes "\<phi>: A \<rightarrow> B" and "x \<in> A" 
  shows "\<phi>(x, \<phi>(x))"
  by (simp add: func_app_def [OF assms(1)]) (auto simp: assms the_elem_sat)

lemma func_image_sort:
  assumes "\<phi>: A \<rightarrow> B" and "x \<in> A" 
  shows "(\<phi>::rel)(x) \<in> B"
  using assms func_image holds_codom by blast


section \<open>Axioms\<close>

axiomatization where

  existence: "\<exists>X. \<exists>x \<in> X. True" and

  comprehension: "\<exists>!\<phi>: A \<succ> B. \<forall>x \<in> A. \<forall>y \<in> B. \<phi>(x, y) \<longleftrightarrow> P x y"

axiomatization
  tab :: "rel \<Rightarrow> set" ("|_|") and
  fst :: "rel \<Rightarrow> rel" ("|_|\<^sub>1") and
  snd :: "rel \<Rightarrow> rel" ("|_|\<^sub>2")where

  tabulation:
    "\<forall>\<phi>: A \<succ> B.
      |\<phi>|\<^sub>1: |\<phi>| \<rightarrow> A \<and>
      |\<phi>|\<^sub>2: |\<phi>| \<rightarrow> B \<and>
      (\<forall>x \<in> A. \<forall>y \<in> B. \<phi>(x, y) \<longleftrightarrow> (\<exists>r \<in> |\<phi>|. |\<phi>|\<^sub>1(r) = x \<and> |\<phi>|\<^sub>2(r) = y)) \<and>
      (\<forall>r \<in> |\<phi>|. \<forall>s \<in> |\<phi>|. |\<phi>|\<^sub>1(r) = |\<phi>|\<^sub>1(s) \<and> |\<phi>|\<^sub>2(r) = |\<phi>|\<^sub>2(s) \<longrightarrow> r = s)"

corollary fst_is_func: "\<phi>: A \<succ> B \<Longrightarrow> |\<phi>|\<^sub>1: |\<phi>| \<rightarrow> A" using tabulation by auto

corollary snd_is_func: "\<phi>: A \<succ> B \<Longrightarrow> |\<phi>|\<^sub>2: |\<phi>| \<rightarrow> B" using tabulation by auto

corollary tab_sufficient:
  "\<phi>: A \<succ> B \<Longrightarrow> \<forall>x \<in> A. \<forall>y \<in> B. \<phi>(x, y) \<longleftrightarrow> (\<exists>r \<in> |\<phi>|. |\<phi>|\<^sub>1(r) = x \<and> |\<phi>|\<^sub>2(r) = y)"
  using tabulation by auto

corollary tab_minimal:
  "\<phi>: A \<succ> B \<Longrightarrow> \<forall>r \<in> |\<phi>|. \<forall>s \<in> |\<phi>|. |\<phi>|\<^sub>1(r) = |\<phi>|\<^sub>1(s) \<and> |\<phi>|\<^sub>2(r) = |\<phi>|\<^sub>2(s) \<longrightarrow> r = s"
  using tabulation by blast


section \<open>Basic consequences of the first three axioms\<close>

theorem emptyset_exists: "\<exists>X. \<forall>x \<in> X. x \<notin> X"
proof -
  from existence obtain a A where "a \<in> A" by auto

  from comprehension [of A A "\<lambda>_ _. False"] obtain \<phi> where
    \<phi>_rel: "\<phi>: A \<succ> A" and "\<forall>x \<in> A. \<forall>y \<in> A. \<not>\<phi>(x, y)"
      by auto
  with tab_sufficient have
    lemma_1: "\<forall>x \<in> A. \<forall>y \<in> A. \<not>(\<exists>r \<in> |\<phi>|. |\<phi>|\<^sub>1(r) = x \<and> |\<phi>|\<^sub>2(r) = y)"
      by auto

  have "\<forall>r \<in> |\<phi>|. r \<notin> |\<phi>|"
  proof -
    { fix r assume for_contradiction: "r \<in> |\<phi>|"
      then have "|\<phi>|\<^sub>1(r) \<in> A" and "|\<phi>|\<^sub>2(r) \<in> A"
        using
          fst_is_func [OF \<phi>_rel]
          snd_is_func [OF \<phi>_rel]
          func_image_sort
        by auto
      hence
        nonexistence: "\<not>(\<exists>r' \<in> |\<phi>|. |\<phi>|\<^sub>1(r') = |\<phi>|\<^sub>1(r) \<and> |\<phi>|\<^sub>2(r') = |\<phi>|\<^sub>2(r))"
        using lemma_1 by auto

      from for_contradiction have
        "\<exists>r' \<in> |\<phi>|. |\<phi>|\<^sub>1(r') = |\<phi>|\<^sub>1(r) \<and> |\<phi>|\<^sub>2(r') = |\<phi>|\<^sub>2(r)"
        by auto

      hence False using nonexistence by auto
    }
    thus
      "\<forall>x \<in> |\<phi>|. x \<notin> |\<phi>|"
      by auto
  qed
  thus ?thesis ..
qed

theorem singleton_exists: "\<exists>X. \<exists>x \<in> X. \<forall>y \<in> X. y = x"
proof -
  from existence obtain a A where
    a_in_A: "a \<in> A" by auto

  from comprehension [of A A "\<lambda>x y. x = a \<and> y = a"] obtain \<phi> where
    \<phi>_rel: "\<phi>: A \<succ> A" and "\<forall>x \<in> A. \<forall>y \<in> A. \<phi>(x, y) \<longleftrightarrow> x = a \<and> y = a"
      by auto
  with tab_sufficient have
    lemma_1: "\<forall>x \<in> A. \<forall>y \<in> A. x = a \<and> y = a \<longleftrightarrow> (\<exists>r \<in> |\<phi>|. |\<phi>|\<^sub>1(r) = x \<and> |\<phi>|\<^sub>2(r) = y)"
      by auto
  then obtain r where
    r_elem: "r \<in> |\<phi>|" and "|\<phi>|\<^sub>1(r) = a \<and> |\<phi>|\<^sub>2(r) = a"
    using a_in_A by auto

  have "\<forall>r \<in> |\<phi>|. |\<phi>|\<^sub>1(r) = a \<and> |\<phi>|\<^sub>2(r) = a"
  proof -
    { fix r assume r_elem: "r \<in> |\<phi>|"
    then have "|\<phi>|\<^sub>1(r) \<in> A" and "|\<phi>|\<^sub>2(r) \<in> A"
      using
        fst_is_func [OF \<phi>_rel]
        snd_is_func [OF \<phi>_rel]
        func_image_sort
      by auto
    with lemma_1 have "|\<phi>|\<^sub>1(r) = a \<and> |\<phi>|\<^sub>2(r) = a"
      using r_elem by auto
    }
    thus ?thesis by auto
  qed

  with tab_minimal [OF \<phi>_rel] have "\<forall>s \<in> |\<phi>|. r = s" using r_elem by auto
  thus ?thesis using r_elem by auto
qed

text \<open>Fix particular choices of empty and singleton set.\<close>

definition emptyset :: set ("\<emptyset>")
  where "\<emptyset> \<equiv> \<epsilon>set X | \<forall>x \<in> X. x \<notin> X"

definition singleton :: set ("\<one>")
  where "\<one> \<equiv> \<epsilon>set X | \<exists>x \<in> X. \<forall>y \<in> X. y = x"

theorem emptyset_prop: "\<forall>x \<in> \<emptyset>. x \<notin> \<emptyset>"
  using emptyset_exists emptyset_def some_set_def [of "\<lambda>X. \<forall>x \<in> X. x \<notin> X"]
  by auto

theorem singleton_prop: "\<exists>x \<in> \<one>. \<forall>y \<in> \<one>. y = x"
  using singleton_exists singleton_def some_set_def [of "\<lambda>X. \<exists>x \<in> X. \<forall>y \<in> X. y = x"]
  by auto

lemma vacuous: "\<forall>x \<in> \<emptyset>. P x"
proof -
  { fix x assume assm: "x \<in> \<emptyset>"
    hence "x \<notin> \<emptyset>" using emptyset_prop by auto
    hence "P x" using assm by auto
  }
  thus ?thesis by auto
qed    
  

end
