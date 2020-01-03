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

abbreviation sphere_order :: \<open>'world \<Rightarrow> 'world set rel\<close> where
  \<open>sphere_order w \<equiv> {(s1, s2). s1 \<in> S w \<and> s2 \<in> S w \<and> s1 \<subseteq> s2}\<close>

lemma sphere_direction:
  assumes \<open>s1 \<in> S w\<close> \<open>s2 \<in> S w\<close>
  shows \<open>(\<not> s2 \<subset> s1) = (s1 \<subseteq> s2)\<close>
  using assms sphere_system unfolding nested_spheres_def by blast

lemma sphere_ordering_total:
  \<open>total_on (S w) (sphere_order w)\<close>
  using sphere_system unfolding nested_spheres_def total_on_def by blast

lemma sphere_ordering_linear:
  \<open>linear_order_on (S w) (sphere_order w)\<close>
proof -
  have \<open>antisym (sphere_order w)\<close>
    unfolding antisym_def by fastforce
  then have \<open>partial_order_on (S w) (sphere_order w)\<close>
    unfolding partial_order_on_def preorder_on_def refl_on_def' trans_def by blast
  then show ?thesis 
    unfolding linear_order_on_def using sphere_ordering_total ..
qed

primrec is_true_at :: \<open>'a formula \<Rightarrow> 'world \<Rightarrow> bool\<close> (\<open>\<lbrakk> _ \<rbrakk>_\<close> [20] 55) where
    \<open>(\<lbrakk>Falsef\<rbrakk>w) = False\<close> |
    \<open>(\<lbrakk>Atom a\<rbrakk>w) = interpretations w a\<close> |
    \<open>(\<lbrakk>\<phi>\<rightarrow>\<psi>\<rbrakk>w)   = (\<not>(\<lbrakk>\<phi>\<rbrakk>w) \<or> \<lbrakk>\<psi>\<rbrakk>w)\<close>|
    \<comment>\<open>Definition of counterfactuals from p. 16\<close>
    \<open>(\<lbrakk>\<phi>\<box>\<rightarrow>\<psi>\<rbrakk>w) = (
      (\<forall>s \<in> S w. \<not>(\<exists>w\<phi> \<in> s. \<lbrakk>\<phi>\<rbrakk>w\<phi>)) \<or>
      (\<exists>s \<in> S w.  (\<exists>w\<phi> \<in> s. \<lbrakk>\<phi>\<rbrakk>w\<phi>) \<and> (\<forall>ws \<in> s. (\<lbrakk>\<phi>\<rbrakk>ws) \<longrightarrow> \<lbrakk>\<psi>\<rbrakk>ws)))\<close>

lemma double_negation[simp]: \<open>(\<lbrakk>~~(~~\<phi>)\<rbrakk>w) = \<lbrakk>\<phi>\<rbrakk>w\<close> by auto

abbreviation permitting_sphere :: \<open>'a formula \<Rightarrow> 'world set \<Rightarrow> bool\<close> where
  \<open>permitting_sphere \<phi> s \<equiv> \<exists>w \<in> s. \<lbrakk>\<phi>\<rbrakk>w\<close>

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

text \<open>
Lewis motivates the need for variably strict conditionals (p. 10, p. 18) with the idea that
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

text \<open>
In \<section> 1.4, Lewis gives an alternative characterization of counterfactuals under the assumption
that there are “smallest spheres” for every formula to be true and thus a “well-ordering” of the
sphere inclusion relation.

However, he rejects this approach on page 20, arguing that the space of possible worlds actually
should rather be dense (i.e. for a world, there are arbitrarily similar, but different worlds).
\<close>

text \<open>The least permitting sphere for a formula (if such a notion makes sense)\<close>
definition (in counterfactuals) smallest_sphere :: \<open>'world \<Rightarrow> 'a formula \<Rightarrow> 'world set\<close>
  where \<open>smallest_sphere w \<phi> \<equiv>
    if \<exists>s \<in> S w. permitting_sphere \<phi> s then
      (SOME s. s \<in> S w \<and>
        permitting_sphere \<phi> s \<and>
        (\<forall>s' \<in> S w. permitting_sphere \<phi> s' \<longrightarrow> s \<subseteq> s'))
    else {}\<close>

locale counterfactuals_limit_assumption = counterfactuals +
  assumes wf_spheres: \<open>wf {(s1, s2). s1 \<in> S w \<and> s2 \<in> S w \<and> s1 \<subset> s2}\<close>
begin

lemma wellfounded_smallest_sphere:
  assumes
    some_sphere: \<open>permitting_sphere \<phi> s\<close>  \<open>s \<in> S w\<close>
  shows 
    \<open>smallest_sphere w \<phi> \<in> S w \<and> permitting_sphere \<phi> (smallest_sphere w \<phi>) \<and>
      (\<forall>s' \<in> S w. permitting_sphere \<phi> s' \<longrightarrow> (smallest_sphere w \<phi>) \<subseteq> s')\<close> 
proof -
  from some_sphere have smallest_sphere_some:
      \<open>smallest_sphere w \<phi> = (SOME s. s \<in> S w \<and>
          permitting_sphere \<phi> s \<and>
          (\<forall>s' \<in> S w. permitting_sphere \<phi> s' \<longrightarrow> s \<subseteq> s'))\<close>
    unfolding smallest_sphere_def by auto
  from assms wf_spheres have
    \<open>\<exists>s' \<in> {s. s \<in> S w \<and> permitting_sphere \<phi> s}. (\<forall>y. (y, s') \<in> {(s1, s2). s1 \<in> S w \<and> s2 \<in> S w \<and> s1 \<subset> s2} 
    \<longrightarrow> (y \<notin> {s. s \<in> S w \<and> permitting_sphere \<phi> s}))\<close>
    unfolding wf_eq_minimal
    by (metis (mono_tags, lifting) CollectI mem_Collect_eq)
  then have
    \<open>\<exists>s'\<in>{s \<in> S w. permitting_sphere \<phi> s}.
      \<forall>s'' \<in> S w. permitting_sphere \<phi> s'' \<longrightarrow> \<not>(s'' \<subset> s')\<close> by auto
  then have
    \<open>\<exists>s'\<in>{s \<in> S w. permitting_sphere \<phi> s}.
      \<forall>s'' \<in> S w. permitting_sphere \<phi> s'' \<longrightarrow> s' \<subseteq> s''\<close>
    using sphere_direction by (metis (no_types, lifting) CollectD)
  then have
    \<open>\<exists>s. s \<in> S w \<and> permitting_sphere \<phi> s \<and> (\<forall>s'\<in>S w. permitting_sphere \<phi> s' \<longrightarrow> s \<subseteq> s')\<close>
    by auto
  from someI_ex[OF this] show ?thesis
    unfolding smallest_sphere_some by blast
qed

lemma vacuous_smallest_sphere:
  assumes
    no_sphere: \<open>\<not> (\<exists>s \<in> S w. permitting_sphere \<phi> s)\<close>
  shows 
    \<open>smallest_sphere w \<phi> \<in> S w \<and> (\<forall>s' \<in> S w. permitting_sphere \<phi> s' \<longrightarrow> (smallest_sphere w \<phi>) \<subseteq> s')\<close> 
proof -
  from no_sphere have smallest_sphere_some:
      \<open>smallest_sphere w \<phi> = {}\<close>
    unfolding smallest_sphere_def by auto
  then show ?thesis
    using sphere_system union_closed_spheres_def by force
qed

lemma smallest_sphere_is_least_permitting:
  assumes
    some_sphere: \<open>permitting_sphere \<phi> s\<close>  \<open>s \<in> S w\<close>
  shows \<open>smallest_sphere w \<phi> \<subseteq> s\<close>
  using  wellfounded_smallest_sphere[OF assms] some_sphere by blast

text \<open>p. 20: “a counterfactual is true at \<open>i\<close> if and only if the consequent
  holds at every antecedent-world closest to \<open>i\<close>”\<close>
lemma counterfactual_smallest_sphere_def:
  \<open>(\<lbrakk>\<phi>\<box>\<rightarrow>\<psi>\<rbrakk>w) = (\<forall>wa \<in> smallest_sphere w \<phi>. (\<lbrakk>\<phi>\<rbrakk>wa) \<longrightarrow> \<lbrakk>\<psi>\<rbrakk>wa)\<close>
proof safe
  fix wa
  assume wa_closest: \<open>wa \<in> smallest_sphere w \<phi>\<close> \<open>\<lbrakk>\<phi>\<rbrakk>wa\<close>
  assume \<open>\<lbrakk>\<phi> \<box>\<rightarrow> \<psi>\<rbrakk>w\<close>
  then have
    \<open>(\<forall>s \<in> S w. \<not>(\<exists>w\<phi> \<in> s. \<lbrakk>\<phi>\<rbrakk>w\<phi>)) \<or>
    (\<exists>s \<in> S w.  (\<exists>w\<phi> \<in> s. \<lbrakk>\<phi>\<rbrakk>w\<phi>) \<and> (\<forall>ws \<in> s. (\<lbrakk>\<phi>\<rbrakk>ws) \<longrightarrow> \<lbrakk>\<psi>\<rbrakk>ws))\<close> by simp
  then show \<open>\<lbrakk>\<psi>\<rbrakk>wa\<close> 
  proof safe
    assume \<open>\<forall>s \<in> S w. \<not> (\<exists>w\<phi> \<in> s. \<lbrakk>\<phi>\<rbrakk>w\<phi>)\<close>
    then show \<open>\<lbrakk>\<psi>\<rbrakk>wa\<close> using \<open>wa \<in> smallest_sphere w \<phi>\<close> unfolding smallest_sphere_def by auto
  next
    fix s w\<phi>
    assume
      \<open>s \<in> S w\<close> \<open>\<forall>ws \<in> s. (\<lbrakk>\<phi>\<rbrakk>ws) \<longrightarrow> \<lbrakk>\<psi>\<rbrakk>ws\<close>
      \<open>w\<phi> \<in> s\<close> \<open>\<lbrakk>\<phi>\<rbrakk>w\<phi>\<close>
    moreover then have \<open>smallest_sphere w \<phi> \<subseteq> s\<close>
      using smallest_sphere_is_least_permitting wf_spheres by blast
    ultimately show \<open>\<lbrakk>\<psi>\<rbrakk>wa\<close> using wa_closest by blast
  qed
next
  assume wa\<phi>\<psi>: \<open>\<forall>wa \<in> smallest_sphere w \<phi>. (\<lbrakk>\<phi>\<rbrakk>wa) \<longrightarrow> \<lbrakk>\<psi>\<rbrakk>wa\<close>
  show \<open>\<lbrakk>\<phi> \<box>\<rightarrow> \<psi>\<rbrakk>w\<close>
  proof (cases \<open>smallest_sphere w \<phi> = {}\<close>)
    case True
    then show ?thesis using wellfounded_smallest_sphere by fastforce
  next
    case False
    then have \<open>smallest_sphere w \<phi> \<in> S w \<and> permitting_sphere \<phi> (smallest_sphere w \<phi>)\<close>
      using wellfounded_smallest_sphere unfolding smallest_sphere_def by meson
    then show ?thesis using wellfounded_smallest_sphere using wa\<phi>\<psi> by auto
  qed
qed

end

text \<open>
Lewis closes \<section> 1.4 stating: “When there is no smallest antecedent-permitting sphere, our truth
conditions amount to this: if there are antecedent-permitting spheres, then as we take smaller
and smaller ones without end, eventually we come to ones in which the consequent holds at every
antecedent-world.” (p. 21)

The wording seems a little confusing. Apparently he has a (inverted?) version of the mathematical
“eventually” in mind. With a temporal reading of “eventually,” the sentence would be wrong.\<close>

subsection \<open>Comparative Similarity\<close>

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

end