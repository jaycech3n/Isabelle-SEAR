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
  rel_of  :: "[rel, set, set] \<Rightarrow> o" ("(_ : _ \<succ> _)"[51, 0, 51] 50) and
  holds   :: "[rel, elem, elem] \<Rightarrow> o" ("(_'(_, _'))"[100, 0, 0]) where

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
  "_all_elem" :: "[idt, set, o] \<Rightarrow> o" ("(\<forall>_ \<in> _./ _)"[0, 0, 10] 11)
  "_ex_elem"  :: "[idt, set, o] \<Rightarrow> o" ("(\<exists>_ \<in> _./ _)"[0, 0, 10] 11)
  "_ex1_elem" :: "[idt, set, o] \<Rightarrow> o" ("(\<exists>!_ \<in> _./ _)"[0, 0, 10] 11)
  "_all_rel"  :: "[idt, set, set, o] \<Rightarrow> o" ("(\<forall>_: _ \<succ> _./ _)"[0, 0, 0, 10] 11)
  "_ex_rel"   :: "[idt, set, set, o] \<Rightarrow> o" ("(\<exists>_: _ \<succ> _./ _)"[0, 0, 0, 10] 11)
  "_ex1_rel"  :: "[idt, set, set, o] \<Rightarrow> o" ("(\<exists>!_: _ \<succ> _./ _)"[0, 0, 0, 10] 11)
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


subsubsection \<open>Injectivity and surjectivity\<close>

definition rel_inj :: "[rel, set, set] \<Rightarrow> o" ("(_ : _ \<succ> _ injective)")
  where "\<phi>: A \<succ> B injective \<equiv> \<forall>a \<in> A. \<forall>a' \<in> A. (\<exists>b \<in> B. \<phi>(a, b) \<and> \<phi>(a', b)) \<longrightarrow> a = a'"

definition rel_surj :: "[rel, set, set] \<Rightarrow> o" ("(_ : _ \<succ> _ surjective)")
  where "\<phi>: A \<succ> B surjective \<equiv> \<forall>b \<in> B. \<exists>a \<in> A. \<phi>(a, b)"


subsubsection \<open>Functions\<close>

abbreviation is_fun :: "[rel, set, set] \<Rightarrow> o" ("(_ : _ \<rightarrow> _)"[51, 0, 51] 50)
  where "f: A \<rightarrow> B \<equiv> f: A \<succ> B \<and> (\<forall>x \<in> A. \<exists>!y \<in> B. f(x, y))"

abbreviation all_fun :: "[set, set, rel \<Rightarrow> o] \<Rightarrow> o"
  where "all_fun A B P \<equiv> \<forall>\<forall>f. f: A \<rightarrow> B \<longrightarrow> P f"

abbreviation ex_fun :: "[set, set, rel \<Rightarrow> o] \<Rightarrow> o"
  where "ex_fun A B P \<equiv> \<exists>\<exists>f. f: A \<rightarrow> B \<and> P f"

abbreviation ex1_fun :: "[set, set, rel \<Rightarrow> o] \<Rightarrow> o"
  where "ex1_fun A B P \<equiv> \<exists>\<exists>!f. f: A \<rightarrow> B \<and> P f"

syntax
  "_all_fun"  :: "[idt, set, set, o] \<Rightarrow> o" ("(\<forall>_: _ \<rightarrow> _./ _)"[0, 0, 0, 10] 11)
  "_ex_fun"   :: "[idt, set, set, o] \<Rightarrow> o" ("(\<exists>_: _ \<rightarrow> _./ _)"[0, 0, 0, 10] 11)
  "_ex1_fun"  :: "[idt, set, set, o] \<Rightarrow> o" ("(\<exists>!_: _ \<rightarrow> _./ _)"[0, 0, 0, 10] 11)
translations
  "\<forall>f: A \<rightarrow> B. P"  \<rightleftharpoons> "CONST all_fun A B (\<lambda>f. P)"
  "\<exists>f: A \<rightarrow> B. P"  \<rightleftharpoons> "CONST ex_fun A B (\<lambda>f. P)"
  "\<exists>!f: A \<rightarrow> B. P" \<rightleftharpoons> "CONST ex1_fun A B (\<lambda>f. P)"

axiomatization fun_app :: "[rel, elem] \<Rightarrow> elem" ("(_[_])"[100, 0])
  where fun_app_def: "f: A \<rightarrow> B \<Longrightarrow> f[x] \<equiv> \<iota>elem y \<in> B | f(x, y)"

lemma fun_image:
  assumes "f: A \<rightarrow> B" and "x \<in> A" 
  shows "f(x, f[x])"
  by (simp add: fun_app_def[OF assms(1)]) (auto simp: assms the_elem_sat)

lemma fun_image_elem_of:
  assumes "f: A \<rightarrow> B" and "x \<in> A" 
  shows "f[x] \<in> B"
  using assms fun_image holds_codom by blast

lemma holds_fun_app_equiv:
  assumes "f: A \<rightarrow> B" and "x \<in> A" and "y \<in> B"
  shows "f(x, y) \<longleftrightarrow> y = f[x]"
proof
  show "f(x, y) \<Longrightarrow> y = f[x]"
  proof -
    have observation:
      "f(x, f[x])"
      using assms(1-2) by (fact fun_image)

    assume "f(x, y)"
    with observation show
      "y = f[x]"
      using assms fun_image_elem_of by blast
  qed

  next show "y = f[x] \<Longrightarrow> f(x, y)"
    using assms fun_image by simp
qed

text \<open>Injectivity and surjectivity of functions\<close>

definition fun_inj :: "[rel, set, set] \<Rightarrow> o" ("(_ : _ \<rightarrow> _ injective)")
  where "f: A \<rightarrow> B injective \<equiv> f: A \<rightarrow> B \<and> (\<forall>a \<in> A. \<forall>a' \<in> A. f[a] = f[a'] \<longrightarrow> a = a')"

definition fun_surj :: "[rel, set, set] \<Rightarrow> o" ("(_ : _ \<rightarrow> _ surjective)")
  where "f: A \<rightarrow> B surjective \<equiv> f: A \<rightarrow> B \<and> (\<forall>b \<in> B. \<exists>a \<in> A. f[a] = b)"

lemma fun_inj_implies_rel_inj: "f: A \<rightarrow> B injective \<Longrightarrow> f: A \<succ> B injective"
  sorry

lemma rel_inj_fun_implies_fun_inj: "\<lbrakk>f: A \<rightarrow> B; f: A \<succ> B injective\<rbrakk> \<Longrightarrow> f: A \<rightarrow> B injective"
  sorry


section \<open>Axioms\<close>

axiomatization where

  existence: "\<exists>X. \<exists>\<exists>x. x \<in> X" and

  rel_comprehension: "\<exists>!\<phi>: A \<succ> B. \<forall>x \<in> A. \<forall>y \<in> B. \<phi>(x, y) \<longleftrightarrow> P x y"

text \<open>
A tabulation is a reflection of relations into sets.
The third axiom states that tabulations exist.
\<close>

abbreviation (input) is_tabulation_of :: "[set, rel, rel, rel, set, set] \<Rightarrow> o"
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

lemma singleton_terminal: "\<exists>\<exists>!f. f: X \<rightarrow> \<one>"
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
  thus "\<exists>\<exists>f. f: X \<rightarrow> \<one>"
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

definition subset_of :: "[set, set] \<Rightarrow> o" (infix "\<subseteq>" 50)
  where "B \<subseteq> A \<equiv>
    \<exists>S: \<one> \<succ> A. \<exists>\<exists>i. (i: B \<rightarrow> A injective) \<and> (\<forall>pt \<in> \<one>. \<forall>a \<in> A. S(pt, a) \<longleftrightarrow> (\<exists>b \<in> B. i[b] = a))"

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
