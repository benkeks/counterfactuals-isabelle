theory
  Counterfactuals
imports
  Main
begin

text \<open>
  Local variable naming conventions:
  - world:         w (Lewis: i, j)
  - sphere-system: S (Lewis: $)
  - sphere:        s (Lewis: S, T)
\<close>

subsection \<open>Counterfactuals in terms of sphere systems\<close>

text \<open>p. 14: “the set \<open>{i}\<close> having \<open>i\<close> as its only member belongs to \<open>$\<^sub>i\<close>.”\<close>
definition centered_spheres :: \<open>'world set set \<Rightarrow> 'world \<Rightarrow> bool\<close>
  where
    \<open>centered_spheres S\<^sub>w w \<equiv> {w} \<in> S\<^sub>w\<close>

text \<open>p. 14: “whenever \<open>S\<close> and \<open>T\<close> belong to \<open>$\<^sub>i\<close>,
  either \<open>S\<close> is included in \<open>T\<close> or \<open>T\<close> is included in \<open>S\<close>.”\<close>
definition nested_spheres :: \<open>'world set set \<Rightarrow> bool\<close>
  where
    \<open>nested_spheres S\<^sub>w \<equiv> \<forall>s1 \<in> S\<^sub>w. \<forall>s2 \<in> S\<^sub>w. s1 \<subseteq> s2 \<or> s2 \<subseteq> s1\<close>
\<comment>\<open>I ignore exclusivity of the “either-or” formulation because it only makes
  sense if one also adds distinctiveness of S and T as a prerequisite.\<close>

text \<open>p. 14: “whenever \<open>\<S>\<close> is a subset of \<open>$\<^sub>i\<close> and \<open>\<Union>\<S>\<close> is the set of all worlds 
  \<open>j\<close> such that \<open>j\<close> belongs to some member of \<open>\<S>\<close>, \<open>\<Union>\<S>\<close> belongs to \<open>$\<^sub>i\<close>.”\<close>
definition union_closed_spheres :: \<open>'world set set \<Rightarrow> bool\<close>
  where
    \<open>union_closed_spheres S\<^sub>w \<equiv> \<forall>\<S> \<subseteq> S\<^sub>w. \<Union>\<S> \<in> S\<^sub>w\<close>

text \<open>p. 14: “whenever \<open>\<S>\<close> is a nonempty subset of \<open>$\<^sub>i\<close> and \<open>\<Inter>\<S>\<close> is the set of all worlds 
  \<open>j\<close> such that \<open>j\<close> belongs to every member of \<open>\<S>\<close>, \<open>\<Inter>\<S>\<close> belongs to \<open>$\<^sub>i\<close>.”\<close>
definition intersection_closed_spheres :: \<open>'world set set \<Rightarrow> bool\<close>
  where
    \<open>intersection_closed_spheres S\<^sub>w \<equiv> \<forall>\<S> \<subseteq> S\<^sub>w. \<S> \<noteq> {} \<longrightarrow> \<Inter>\<S> \<in> S\<^sub>w\<close>

text \<open>\<open>centered system of spheres\<close> from p. 14\<close>
abbreviation system_of_spheres :: \<open>('world \<Rightarrow> 'world set set) \<Rightarrow> bool\<close>
  where
    \<open>system_of_spheres S \<equiv> \<forall>w.
      centered_spheres (S w) w \<and>
      nested_spheres (S w) \<and>
      union_closed_spheres (S w) \<and>
      intersection_closed_spheres (S w)\<close>

text \<open>p. 15 “Note that conditions (2) and (3) of closure under union and intersection are
  automatically satisfied when there are only finitely many spheres around \<open>i\<close>, ...”\<close>
lemma closures_trivial_for_finite_spheres:
  assumes
    \<open>nested_spheres S\<^sub>w\<close>
    \<open>finite S\<^sub>w\<close>
    \<open>{} \<in> S\<^sub>w\<close>\<comment>\<open>Lewis does not state this assumption. But he mentions that union closure
      implies the presence of an empty sphere. (Otherwise its absence produces a
      counter example for the union closure (\<open>{} \<subseteq> {x}\<close> but not \<open>\<Union>{} \<in> {x}\<close>).
      So he must implicitly have assumed the empty sphere's presence for his sentence to be true.\<close>
  shows
    \<open>union_closed_spheres S\<^sub>w\<close>
    \<open>intersection_closed_spheres S\<^sub>w\<close>
  using assms unfolding nested_spheres_def union_closed_spheres_def intersection_closed_spheres_def
  by (metis Sup_empty Union_in_chain finite_subset subset_chain_def subset_iff, 
      simp add: Inter_in_chain finite_subset subset_chain_def subset_iff)

datatype ('aa) formula =
  Falsef | Atom 'aa |
  Impl \<open>'aa formula\<close> \<open>'aa formula\<close> (\<open>_ \<rightarrow> _\<close> 27) |
  Would \<open>'aa formula\<close> \<open>'aa formula\<close> (\<open>_ \<box>\<rightarrow> _\<close> 25)

abbreviation Neg :: \<open>'aa formula \<Rightarrow> 'aa formula\<close> (\<open>~~_\<close> [40] 40)
  where \<open>~~\<phi> \<equiv> \<phi> \<rightarrow> Falsef\<close>
abbreviation Or :: \<open>'aa formula \<Rightarrow> 'aa formula \<Rightarrow> 'aa formula\<close>
  where \<open>Or \<phi> \<psi> \<equiv> (~~\<phi>) \<rightarrow> \<psi>\<close>
abbreviation And :: \<open>'aa formula \<Rightarrow> 'aa formula \<Rightarrow> 'aa formula\<close>
  where \<open>And \<phi> \<psi> \<equiv> ~~Or (~~\<phi>) (~~\<psi>)\<close>

locale counterfactuals = 
  fixes
    S :: \<open>'world \<Rightarrow> 'world set set\<close> and
    interpretations :: \<open>'world \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assumes
    sphere_system: \<open>system_of_spheres S\<close>
begin

abbreviation possible_worlds :: \<open>'world \<Rightarrow> 'world set\<close> where
  \<open>possible_worlds w \<equiv> \<Union> (S w)\<close>

primrec is_true_at :: \<open>'a formula \<Rightarrow> 'world \<Rightarrow> bool\<close> (\<open>\<lbrakk> _ \<rbrakk>_\<close> [20] 55) where
    \<open>(\<lbrakk>Falsef\<rbrakk>w) = False\<close> |
    \<open>(\<lbrakk>Atom a\<rbrakk>w) = interpretations w a\<close> |
    \<open>(\<lbrakk>\<phi>\<rightarrow>\<psi>\<rbrakk>w)   = (\<not>(\<lbrakk>\<phi>\<rbrakk>w) \<or> \<lbrakk>\<psi>\<rbrakk>w)\<close>|
    \<comment>\<open>Definition of counterfactuals from p. 16\<close>
    \<open>(\<lbrakk>\<phi>\<box>\<rightarrow>\<psi>\<rbrakk>w) = (
      (\<forall>s \<in> S w. \<not>(\<exists>w\<phi> \<in> s. \<lbrakk>\<phi>\<rbrakk>w\<phi>)) \<or>
      (\<exists>s \<in> S w.  (\<exists>w\<phi> \<in> s. \<lbrakk>\<phi>\<rbrakk>w\<phi>) \<and> (\<forall>ws \<in> s. (\<lbrakk>\<phi>\<rbrakk>ws) \<longrightarrow> \<lbrakk>\<psi>\<rbrakk>ws)))\<close>

lemma double_negation[simp]: \<open>(\<lbrakk>~~(~~\<phi>)\<rbrakk>w) = \<lbrakk>\<phi>\<rbrakk>w\<close> by auto

text \<open>The four cases that might arise for a counterfactual (p. 16f.):
  Vacuous truth, non-vacuous truth, falsity with opposite true, and falsity with opposite false\<close>
lemma four_counterfactual_cases:
  shows
    \<open>((\<lbrakk>\<phi> \<box>\<rightarrow> \<psi>\<rbrakk>w) \<and> \<lbrakk>\<phi> \<box>\<rightarrow> ~~\<psi>\<rbrakk>w) \<or>
     ((\<lbrakk>\<phi> \<box>\<rightarrow> \<psi>\<rbrakk>w) \<and> \<lbrakk>~~(\<phi> \<box>\<rightarrow> ~~\<psi>)\<rbrakk>w) \<or>
     ((\<lbrakk>~~(\<phi> \<box>\<rightarrow> \<psi>)\<rbrakk>w) \<and> \<lbrakk>\<phi> \<box>\<rightarrow> ~~\<psi>\<rbrakk>w) \<or>
     ((\<lbrakk>~~(\<phi> \<box>\<rightarrow> \<psi>)\<rbrakk>w) \<and> \<lbrakk>~~(\<phi> \<box>\<rightarrow> ~~\<psi>)\<rbrakk>w)\<close>
  using is_true_at.simps by blast
end

subsection \<open>The But-if-party Example\<close>

text
\<open>Lewis motivates the need for variably strict conditionals (p. 10, p. 18) with the idea that
one should be able to model “but if” sequences. He gives different examples. We reproduce the
party example:

“If Otto had come, it would have been a lively party;
but if both Otto and Anna had come[,] it would have been a dreary party;
but if Waldo had come as well, it would have been lively; but....”

Lewis sets the negated opposites to implicitly also be held true.\<close>

datatype party_attendence = LivelyParty | Otto | Anna | Waldo
definition party_interpretation :: \<open>nat \<Rightarrow> party_attendence \<Rightarrow> bool\<close>
  where \<open>party_interpretation n x \<equiv>
    (n = 0 \<and> x \<in> {LivelyParty, Otto}) \<or>
    (n = 1 \<and> x \<in> {Otto, Anna}) \<or>
    (n = 2 \<and> x \<in> {LivelyParty, Otto, Anna, Waldo})\<close>

locale party_example = counterfactuals \<open>\<lambda>n. {{0}, {0,1}, {0,1,2}}\<close> \<open>party_interpretation\<close>
begin
  lemma but_if_sequence_works:
  shows
    \<open>is_true_at ((Atom Otto) \<box>\<rightarrow> (Atom LivelyParty)) 0\<close>
    \<open>is_true_at (~~((Atom Otto) \<box>\<rightarrow> ~~(Atom LivelyParty))) 0\<close>
    \<open>is_true_at ((And (Atom Otto) (Atom Anna)) \<box>\<rightarrow> ~~(Atom LivelyParty)) 0\<close>
    \<open>is_true_at (~~((And (Atom Otto) (Atom Anna)) \<box>\<rightarrow> (Atom LivelyParty))) 0\<close>
    \<open>is_true_at ((And (Atom Otto) (And (Atom Anna) (Atom Waldo))) \<box>\<rightarrow> (Atom LivelyParty)) 0\<close>
    \<open>is_true_at (~~((And (Atom Otto) (And (Atom Anna) (Atom Waldo))) \<box>\<rightarrow> ~~(Atom LivelyParty))) 0\<close>
    using is_true_at.simps party_interpretation_def 
    by auto
end

subsection \<open>The Limit Assumption\<close>


context counterfactuals
begin

\<comment>\<open>p. 48 Section 2.3 Comparative Similarity\<close>
abbreviation at_least_as_similar_as :: \<open>'world \<Rightarrow> 'world \<Rightarrow> 'world \<Rightarrow> bool\<close>
  where \<open>at_least_as_similar_as w w1 w2 \<equiv> (\<forall> s \<in> S w. w2 \<in> s \<longrightarrow> w1 \<in> s)\<close>
abbreviation more_similar_than :: \<open>'world \<Rightarrow> 'world \<Rightarrow> 'world \<Rightarrow> bool\<close>
  where \<open>more_similar_than w w1 w2 \<equiv> \<not> at_least_as_similar_as w w2 w1\<close>

interpretation preorder \<open>at_least_as_similar_as w\<close> \<open>more_similar_than w\<close>
  by (standard, auto, meson in_mono nested_spheres_def sphere_system)

end

locale counterfactuals_centered = counterfactuals S
  for S :: \<open>'world \<Rightarrow> 'world set set\<close> +
  fixes aw :: \<open>'world\<close>
  assumes \<open>centered_spheres (S aw) aw\<close>
begin

abbreviation at_least_as_similar_as_c
  where \<open>at_least_as_similar_as_c \<equiv> at_least_as_similar_as aw\<close>
abbreviation more_similar_than_c
  where \<open>more_similar_than_c \<equiv> more_similar_than aw\<close>

interpretation preorder \<open>at_least_as_similar_as_c\<close> \<open>more_similar_than_c\<close>
  by (standard, auto, meson in_mono nested_spheres_def sphere_system)
end

context counterfactuals
begin

definition closest_worlds :: \<open>'world \<Rightarrow> 'a formula \<Rightarrow> 'world set\<close>
  where \<open>closest_worlds w \<phi> \<equiv>
    {wc. wc \<in> possible_worlds w \<and> (\<lbrakk>\<phi>\<rbrakk>wc) \<and>
      \<not>(\<exists>wss. more_similar_than w wss wc \<and> (\<lbrakk>\<phi>\<rbrakk>wss))}\<close>

(*
lemma
  assumes  \<open>wf {(s1, s2). s1 \<in> S w \<and> s2 \<in> S w \<and> s1 \<subset> s2}\<close>
  shows \<open>wf {(w1, w2). w1 \<in> possible_worlds w \<and> w2 \<in> possible_worlds w \<and> more_similar_than w w1 w2}\<close>
proof -
  have \<open> (\<lambda> ) {(s1, s2). s1 \<in> S w \<and> s2 \<in> S w \<and> s1 \<subset> s2}\<close>
*)

lemma
  fixes w \<phi> \<psi>
  assumes
    \<open>wf {(w1, w2). w1 \<in> possible_worlds w \<and> w2 \<in> possible_worlds w \<and> more_similar_than w w1 w2}\<close>
  shows
    \<open>(\<lbrakk>\<phi>\<box>\<rightarrow>\<psi>\<rbrakk>w) = (\<forall>wa \<in> closest_worlds w \<phi>. \<lbrakk>\<psi>\<rbrakk>wa)\<close>
proof safe
  fix wa
  assume \<open>\<lbrakk>\<phi> \<box>\<rightarrow> \<psi>\<rbrakk>w\<close> \<open>wa \<in> closest_worlds w \<phi>\<close>
  then have
    \<open>(\<forall>s \<in> S w. \<not>(\<exists>w\<phi> \<in> s. \<lbrakk>\<phi>\<rbrakk>w\<phi>)) \<or>
    (\<exists>s \<in> S w.  (\<exists>w\<phi> \<in> s. \<lbrakk>\<phi>\<rbrakk>w\<phi>) \<and> (\<forall>ws \<in> s. (\<lbrakk>\<phi>\<rbrakk>ws) \<longrightarrow> \<lbrakk>\<psi>\<rbrakk>ws))\<close> by simp
  then show \<open>\<lbrakk>\<psi>\<rbrakk>wa\<close> 
  proof safe
    assume \<open>\<forall>s \<in> S w. \<not> (\<exists>w\<phi> \<in> s. \<lbrakk>\<phi>\<rbrakk>w\<phi>)\<close>
    then show \<open>\<lbrakk>\<psi>\<rbrakk>wa\<close> using \<open>wa \<in> closest_worlds w \<phi>\<close> unfolding closest_worlds_def by auto
  next
    fix s w\<phi>
    assume
      \<open>s \<in> S w\<close> \<open>\<forall>ws \<in> s. (\<lbrakk>\<phi>\<rbrakk>ws) \<longrightarrow> \<lbrakk>\<psi>\<rbrakk>ws\<close>
      \<open>w\<phi> \<in> s\<close> \<open>\<lbrakk>\<phi>\<rbrakk>w\<phi>\<close>
    then show \<open>\<lbrakk>\<psi>\<rbrakk>wa\<close>
      using sphere_system \<open>wa \<in> closest_worlds w \<phi>\<close>
      unfolding closest_worlds_def nested_spheres_def by blast
  qed
next
  assume \<open>\<forall>wa\<in>closest_worlds w \<phi>. \<lbrakk> \<psi> \<rbrakk>wa\<close>
  then show \<open>\<lbrakk>\<phi> \<box>\<rightarrow> \<psi>\<rbrakk>w\<close> unfolding closest_worlds_def 

(*   
      by (metis dual_order.order_iff_strict mem_Collect_eq subset_iff)
   by (metis mem_Collect_eq nested_spheres_def sphere_system subset_iff subset_not_subset_eq system_of_spheres_def)*)

  (*using assms unfolding closest_worlds_def
  by (smt CollectD basic_trans_rules(31) is_true_at.simps(4) nested_spheres_def sphere_system subset_not_subset_eq system_of_spheres_def)

    by (smt CollectD counterfactuals.closest_worlds_def counterfactuals_axioms nested_spheres_def sphere_system subsetD subset_not_subset_eq system_of_spheres_def)
*)

end

end