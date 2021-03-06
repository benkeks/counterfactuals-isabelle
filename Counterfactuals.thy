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

subsection \<open>A language of counterfactuals (\<section> 1.1)\<close>

datatype ('aa, 'oo) formula =
  Falsef (\<open>\<bottom>\<close>) | Atom 'aa |
  CounterpartPred \<open>'oo \<Rightarrow> ('aa, 'oo) formula\<close> \<open>'oo\<close> |
  Impl \<open>('aa, 'oo) formula\<close> \<open>('aa, 'oo) formula\<close> (\<open>_ \<rightarrow> _\<close> 27) |
  Would \<open>('aa, 'oo) formula\<close> \<open>('aa, 'oo) formula\<close> (\<open>_ \<box>\<rightarrow> _\<close> 25)

abbreviation Neg :: \<open>('aa, 'oo) formula \<Rightarrow> ('aa, 'oo) formula\<close> (\<open>~~_\<close> [40] 40)
  where \<open>~~\<phi> \<equiv> \<phi> \<rightarrow> \<bottom>\<close>
abbreviation Or :: \<open>('aa, 'oo) formula \<Rightarrow> ('aa, 'oo) formula \<Rightarrow> ('aa, 'oo) formula\<close>
  where \<open>Or \<phi> \<psi> \<equiv> (~~\<phi>) \<rightarrow> \<psi>\<close>
abbreviation And :: \<open>('aa, 'oo) formula \<Rightarrow> ('aa, 'oo) formula \<Rightarrow> ('aa, 'oo) formula\<close>
  where \<open>And \<phi> \<psi> \<equiv> ~~Or (~~\<phi>) (~~\<psi>)\<close>
abbreviation Truef :: \<open>('aa, 'oo) formula\<close> (\<open>\<top>\<close>)
  where \<open>\<top> \<equiv> ~~\<bottom>\<close>

text \<open>The might counterfactual is treated as derived from the would counterfactual. (p. 2 and p. 21)\<close>
definition Might :: \<open>('aa, 'oo) formula \<Rightarrow> ('aa, 'oo) formula \<Rightarrow> ('aa, 'oo) formula\<close> (\<open>_ \<diamond>\<rightarrow> _\<close> 25)
  where [simp]: \<open>\<phi>\<diamond>\<rightarrow> \<psi> \<equiv> ~~(\<phi> \<box>\<rightarrow> ~~\<psi>)\<close>
\<comment>\<open>We do not use \<open>abbreviation\<close> here, as we sometimes want to talk about \<open>\<diamond>\<rightarrow>\<close> explicitly. For
 the most time however, we are fine with it being simplified away automatically.\<close>

subsection \<open>Abstract sphere systems\<close>

text \<open>p. 14: ???the set \<open>{i}\<close> having \<open>i\<close> as its only member belongs to \<open>$\<^sub>i\<close>.???\<close>
definition centered_spheres :: \<open>'world set set \<Rightarrow> 'world \<Rightarrow> bool\<close>
  where
    \<open>centered_spheres S\<^sub>w w \<equiv> {w} \<in> S\<^sub>w\<close>

text \<open>p. 14: ???whenever \<open>S\<close> and \<open>T\<close> belong to \<open>$\<^sub>i\<close>,
  either \<open>S\<close> is included in \<open>T\<close> or \<open>T\<close> is included in \<open>S\<close>.???\<close>
definition nested_spheres :: \<open>'world set set \<Rightarrow> bool\<close>
  where
    \<open>nested_spheres S\<^sub>w \<equiv> \<forall>s1 \<in> S\<^sub>w. \<forall>s2 \<in> S\<^sub>w. s1 \<subseteq> s2 \<or> s2 \<subseteq> s1\<close>
\<comment>\<open>I ignore exclusivity of the ???either-or??? formulation because it only makes
  sense if one also adds distinctiveness of S and T as a prerequisite.\<close>

text \<open>p. 14: ???whenever \<open>\<S>\<close> is a subset of \<open>$\<^sub>i\<close> and \<open>\<Union>\<S>\<close> is the set of all worlds 
  \<open>j\<close> such that \<open>j\<close> belongs to some member of \<open>\<S>\<close>, \<open>\<Union>\<S>\<close> belongs to \<open>$\<^sub>i\<close>.???\<close>
definition union_closed_spheres :: \<open>'world set set \<Rightarrow> bool\<close>
  where
    \<open>union_closed_spheres S\<^sub>w \<equiv> \<forall>\<S> \<subseteq> S\<^sub>w. \<Union>\<S> \<in> S\<^sub>w\<close>

text \<open>p. 14: ???whenever \<open>\<S>\<close> is a nonempty subset of \<open>$\<^sub>i\<close> and \<open>\<Inter>\<S>\<close> is the set of all worlds 
  \<open>j\<close> such that \<open>j\<close> belongs to every member of \<open>\<S>\<close>, \<open>\<Inter>\<S>\<close> belongs to \<open>$\<^sub>i\<close>.???\<close>
definition intersection_closed_spheres :: \<open>'world set set \<Rightarrow> bool\<close>
  where
    \<open>intersection_closed_spheres S\<^sub>w \<equiv> \<forall>\<S> \<subseteq> S\<^sub>w. \<S> \<noteq> {} \<longrightarrow> \<Inter>\<S> \<in> S\<^sub>w\<close>

text \<open>\<open>system of spheres\<close> (without centering from p. 14\<close>
abbreviation system_of_spheres :: \<open>('world \<Rightarrow> 'world set set) \<Rightarrow> bool\<close>
  where
    \<open>system_of_spheres S \<equiv> \<forall>w.
      nested_spheres (S w) \<and>
      union_closed_spheres (S w) \<and>
      intersection_closed_spheres (S w)\<close>


text \<open>\<open>centered system of spheres\<close> from p. 14\<close>
abbreviation centered_system_of_spheres :: \<open>('world \<Rightarrow> 'world set set) \<Rightarrow> bool\<close>
  where
    \<open>centered_system_of_spheres S \<equiv>
      system_of_spheres S \<and>
      (\<forall>w. centered_spheres (S w) w)\<close>

text \<open>p. 15 ???Note that conditions (2) and (3) of closure under union and intersection are
  automatically satisfied when there are only finitely many spheres around \<open>i\<close>, ...???\<close>
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

locale counterfactuals = 
  fixes
    S :: \<open>'world \<Rightarrow> 'world set set\<close> and
    interpretations :: \<open>'world \<Rightarrow> 'a \<Rightarrow> bool\<close> and
    objects :: \<open>'o set\<close>
  assumes
    sphere_system: \<open>system_of_spheres S\<close>
begin

subsection \<open>Concrete spheres systems\<close>

\<comment>\<open>The name ???outermost sphere??? is introduced on p. 22\<close>
abbreviation outermost_sphere :: \<open>'world \<Rightarrow> 'world set\<close> where
  \<open>outermost_sphere w \<equiv> \<Union> (S w)\<close>

\<comment>\<open>???\<open>\<Union>$\<^sub>i\<close> is itself a sphere around \<open>i\<close> (p. 22)\<close>
lemma outermost_sphere_is_sphere: \<open>outermost_sphere w \<in> (S w)\<close>
  using sphere_system union_closed_spheres_def by auto

\<comment>\<open>The name ???innermost sphere??? is introduced on p. 29\<close>
abbreviation innermost_sphere :: \<open>'world \<Rightarrow> 'world set\<close> where
  \<open>innermost_sphere w \<equiv> \<Inter> (S w - {{}})\<close>

lemma innermost_in_outermost_sphere:
  assumes non_trivial_system: \<open>s0 \<in> S w\<close> \<open>s0 \<noteq> {}\<close>
  shows \<open>innermost_sphere w \<subseteq> outermost_sphere w\<close>
using non_trivial_system by auto

lemma innermost_sphere_is_sphere:
  assumes non_trivial_system:  \<open>s0 \<in> S w\<close> \<open>s0 \<noteq> {}\<close>
  shows \<open>innermost_sphere w \<in> (S w)\<close>
  using non_trivial_system sphere_system unfolding intersection_closed_spheres_def
  by (meson Diff_eq_empty_iff Diff_subset in_mono singletonD)

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



subsection \<open>Counterfactual semantics defined in terms of sphere systems (\<section> 1.3)\<close>

primrec is_true_at :: \<open>('a, 'o) formula \<Rightarrow> 'world \<Rightarrow> bool\<close> (\<open>\<lbrakk> _ \<rbrakk>_\<close> [20] 55) where
    \<open>(\<lbrakk>\<bottom>\<rbrakk>w) = False\<close> |
    \<open>(\<lbrakk>Atom a\<rbrakk>w) = interpretations w a\<close> |
    \<open>(\<lbrakk>\<phi>\<rightarrow>\<psi>\<rbrakk>w)   = (\<not>(\<lbrakk>\<phi>\<rbrakk>w) \<or> \<lbrakk>\<psi>\<rbrakk>w)\<close>|
    \<comment>\<open>Definition of counterfactuals from p. 16\<close>
    \<open>(\<lbrakk>\<phi>\<box>\<rightarrow>\<psi>\<rbrakk>w) = (
      (\<forall>s \<in> S w. \<not>(\<exists>w\<phi> \<in> s. \<lbrakk>\<phi>\<rbrakk>w\<phi>)) \<or>
      (\<exists>s \<in> S w.  (\<exists>w\<phi> \<in> s. \<lbrakk>\<phi>\<rbrakk>w\<phi>) \<and> (\<forall>ws \<in> s. (\<lbrakk>\<phi>\<rbrakk>ws) \<longrightarrow> \<lbrakk>\<psi>\<rbrakk>ws)))\<close> |
    \<comment>\<open>This just interprets counterpart predicates (pp. 39ff.) with the identity for the
      counterpart relation.\<close>
    \<open>(\<lbrakk>CounterpartPred F obj\<rbrakk>w) = \<lbrakk>F obj\<rbrakk>w\<close>

lemma double_negation[simp]: \<open>(\<lbrakk>~~(~~\<phi>)\<rbrakk>w) = \<lbrakk>\<phi>\<rbrakk>w\<close> by auto

lemma tarski_and[simp]: \<open>(\<lbrakk>And \<phi> \<psi>\<rbrakk>w) = ((\<lbrakk>\<phi>\<rbrakk>w) \<and> (\<lbrakk>\<psi>\<rbrakk>w))\<close> by auto

abbreviation permitting_sphere :: \<open>('a, 'o) formula \<Rightarrow> 'world set \<Rightarrow> bool\<close> where
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
one should be able to model ???but if??? sequences. He gives different examples. We reproduce the
party example:

???If Otto had come, it would have been a lively party;
but if both Otto and Anna had come[,] it would have been a dreary party;
but if Waldo had come as well, it would have been lively; but....???

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

text \<open>The example is also an instance of the fallacy of transitivity from page 32.\<close>
lemma fallacy_of_transitivity:
  assumes \<open>\<And> \<chi> \<phi> \<psi> w.
            is_true_at (\<chi> \<box>\<rightarrow> \<phi>) w \<Longrightarrow>
            is_true_at (\<phi> \<box>\<rightarrow> \<psi>) w 
          \<Longrightarrow> is_true_at (\<chi> \<box>\<rightarrow> \<psi>) w\<close>
  shows \<open>False\<close>
proof -
  have
    \<open>is_true_at ((Atom Anna) \<box>\<rightarrow> (Atom Otto)) 0\<close>
    \<open>is_true_at ((Atom Otto) \<box>\<rightarrow> (Atom LivelyParty)) 0\<close>
    using is_true_at.simps party_interpretation_def 
    by auto
  hence 
    \<open>is_true_at ((Atom Anna) \<box>\<rightarrow> (Atom LivelyParty)) 0\<close>
    using assms by blast
  thus \<open>False\<close>
    using is_true_at.simps party_interpretation_def 
    by auto
qed

text \<open>The example is an instance of the fallacy of contraposition from page 35.\<close>
lemma fallacy_of_contraposition:
  assumes \<open>\<And> \<phi> \<psi>.
            is_true_at (\<phi> \<box>\<rightarrow> \<psi>) w
          \<Longrightarrow> is_true_at (~~\<psi> \<box>\<rightarrow> ~~\<phi>) w\<close>
  shows \<open>False\<close>
proof-
  have \<open>is_true_at (Atom Otto \<box>\<rightarrow> ~~(Atom Anna)) w\<close>
    using is_true_at.simps party_interpretation_def by simp
  from assms[OF this] have \<open>is_true_at (Atom Anna \<box>\<rightarrow> ~~(Atom Otto)) w\<close>
    unfolding is_true_at.simps by auto
  also have \<open>is_true_at (Atom Anna \<box>\<rightarrow> ~~(Atom Otto)) w = False\<close>
    using is_true_at.simps party_interpretation_def by simp
  finally show \<open>False\<close> .
qed

end

subsection \<open>The Limit Assumption (\<section> 1.4)\<close>

text \<open>
In \<section> 1.4, Lewis gives an alternative characterization of counterfactuals under the assumption
that there are ???smallest spheres??? for every formula to be true and thus a ???well-ordering??? of the
sphere inclusion relation.

However, he rejects this approach on page 20, arguing that the space of possible worlds actually
should rather be dense (i.e. for a world, there are arbitrarily similar, but different worlds).
\<close>

text \<open>The least permitting sphere for a formula (if such a notion makes sense)\<close>
definition (in counterfactuals) smallest_sphere :: \<open>'world \<Rightarrow> ('a, 'o) formula \<Rightarrow> 'world set\<close>
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

text \<open>p. 20: ???a counterfactual is true at \<open>i\<close> if and only if the consequent
  holds at every antecedent-world closest to \<open>i\<close>???\<close>
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


lemma most_fitting_sphere:
  assumes \<open>s \<in> S w\<close> \<open>w' \<in> s\<close>
  shows \<open>\<exists> s' \<in> S w. w' \<in> s' \<and> (\<forall> s'' \<in> S w. w' \<in> s'' \<longrightarrow> s' \<subseteq> s'')\<close>
proof -
  have \<open>\<not>(\<forall> s' \<in> S w. w' \<in> s' \<longrightarrow> (\<exists> s'' \<in> S w. w' \<in> s'' \<and> \<not>(s' \<subseteq> s'')))\<close>
  proof clarify
    assume \<open>\<forall>s'\<in>S w. w' \<in> s' \<longrightarrow> (\<exists>s''\<in>S w. w' \<in> s'' \<and> \<not> s' \<subseteq> s'')\<close>
    with assms obtain s'' where \<open>s''\<in>S w\<close> \<open>w' \<in> s''\<close> \<open>\<not> s \<subseteq> s''\<close> by blast
    hence \<open>s'' \<subseteq> s\<close> using assms(1) sphere_system unfolding nested_spheres_def by blast
    thus False sorry
  qed
  thus ?thesis by blast
  oops

end

text \<open>
Lewis closes \<section> 1.4 stating: ???When there is no smallest antecedent-permitting sphere, our truth
conditions amount to this: if there are antecedent-permitting spheres, then as we take smaller
and smaller ones without end, eventually we come to ones in which the consequent holds at every
antecedent-world.??? (p. 21)

The wording seems a little confusing. Apparently he has a (inverted?) version of the mathematical
???eventually??? in mind. With a temporal reading of ???eventually,??? the sentence would be wrong.\<close>

subsection \<open>???Might??? counterfactuals (\<section> 1.5)\<close>

text \<open>Derived truth conditions for ???might???, p. 21\<close>
lemma (in counterfactuals) might_characterization:
  \<open>(\<lbrakk>\<phi>\<diamond>\<rightarrow>\<psi>\<rbrakk>w) = (
      (\<exists>s \<in> S w. \<exists>w\<phi> \<in> s. \<lbrakk>\<phi>\<rbrakk>w\<phi>) \<and>
      (\<forall>s \<in> S w.  (\<exists>w\<phi> \<in> s. \<lbrakk>\<phi>\<rbrakk>w\<phi>) \<longrightarrow> (\<exists>ws \<in> s. (\<lbrakk>\<phi>\<rbrakk>ws) \<and>\<lbrakk>\<psi>\<rbrakk>ws)))\<close>
  by auto
\<comment>\<open>This is not quite in line with everyday English:
???If spheres were flat, earth might be flat.??? and ???If spheres were flat, earth would be flat.???
seem to include the same statement or non-statement about the possibility of worlds where
spheres are flat...\<close>

text \<open>???Under the Limit assumption, we could restate the derived truth conditions for ???might???...???\<close>
lemma (in counterfactuals_limit_assumption) might_characterization_limited:
  \<open>(\<lbrakk>\<phi>\<diamond>\<rightarrow>\<psi>\<rbrakk>w) = (\<exists>wa \<in> smallest_sphere w \<phi>. (\<lbrakk>\<phi>\<rbrakk>wa) \<and> \<lbrakk>\<psi>\<rbrakk>wa)\<close>
  using counterfactual_smallest_sphere_def unfolding Might_def by (metis is_true_at.simps(1,3))

lemma (in counterfactuals) non_vacuously_would_implies_might:
  assumes 
    \<open>\<lbrakk>\<phi> \<box>\<rightarrow> \<psi>\<rbrakk>w\<close>
    \<open>permitting_sphere \<phi> s\<close> \<open>s \<in> S w\<close>
  shows \<open>\<lbrakk>\<phi> \<diamond>\<rightarrow> \<psi>\<rbrakk>w\<close>
  using assms by (auto, meson in_mono psubsetD sphere_direction)
\<comment>\<open>This is analogous to the fact that non-empty all-quantification implies existential quanatification.\<close>

lemma (in counterfactuals) neither_would_nor_wouldnt_still_might:
  assumes 
    \<open>\<not>\<lbrakk>\<phi> \<box>\<rightarrow> \<psi>\<rbrakk>w\<close> \<open>\<not>\<lbrakk>\<phi> \<box>\<rightarrow> ~~\<psi>\<rbrakk>w\<close>
  shows \<open>\<lbrakk>\<phi> \<diamond>\<rightarrow> \<psi>\<rbrakk>w\<close> \<open>\<lbrakk>\<phi> \<diamond>\<rightarrow> ~~\<psi>\<rbrakk>w\<close>
  using assms by auto
\<comment>\<open>???this is the case in which \<open>\<psi>\<close> is true at some of the closest \<open>\<phi>\<close> worlds and \<open>~~\<psi>\<close>
  is true at others of them.??? (p. 21)\<close>

text \<open>Pp. 22f. reinstate the standard modalities (in Kripke style).\<close>

definition Necessary :: \<open>('aa, 'oo) formula \<Rightarrow> ('aa, 'oo) formula\<close> (\<open>\<box> _\<close> 20)
  where [simp]: \<open>\<box>\<phi> \<equiv> (~~\<phi>) \<box>\<rightarrow> \<bottom>\<close>

definition Possibly :: \<open>('aa, 'oo) formula \<Rightarrow> ('aa, 'oo) formula\<close> (\<open>\<diamond> _\<close> 20)
  where [simp]: \<open>\<diamond>\<phi> \<equiv> \<phi> \<diamond>\<rightarrow> ~~\<bottom>\<close>

lemma (in counterfactuals) modal_duality:
  \<open>(\<lbrakk>\<box>\<phi>\<rbrakk>w) = \<lbrakk>~~(\<diamond>~~\<phi>)\<rbrakk>w\<close>
  \<open>(\<lbrakk>\<diamond>\<phi>\<rbrakk>w) = \<lbrakk>~~(\<box>~~\<phi>)\<rbrakk>w\<close>
  by auto

lemma (in counterfactuals) Necessary_ext_def:
   \<open>(\<lbrakk>\<box>\<phi>\<rbrakk>w) = (\<forall>s \<in> S w. \<forall>wo \<in> s. \<lbrakk>\<phi>\<rbrakk>wo)\<close>
  by auto

lemma (in counterfactuals) Possibly_ext_def:
   \<open>(\<lbrakk>\<diamond>\<phi>\<rbrakk>w) = (\<exists>s \<in> S w. \<exists>wo \<in> s. \<lbrakk>\<phi>\<rbrakk>wo)\<close>
  by auto

lemma (in counterfactuals) Necessary_outermost_def:
   \<open>(\<lbrakk>\<box>\<phi>\<rbrakk>w) = (\<forall>wo \<in> outermost_sphere w. \<lbrakk>\<phi>\<rbrakk>wo)\<close>
  by auto

lemma (in counterfactuals) Possibly_outermost_def:
   \<open>(\<lbrakk>\<diamond>\<phi>\<rbrakk>w) = (\<exists>wo \<in> outermost_sphere w. \<lbrakk>\<phi>\<rbrakk>wo)\<close>
  by auto
\<comment>\<open>(That's why Lewis calls them ???outer modalities.???)\<close>

text \<open>???the outer strict conditional implies the counterfactual???\<close>
lemma (in counterfactuals) outer_strict_conditional:
  assumes \<open>\<lbrakk>\<box>(\<phi>\<rightarrow>\<psi>)\<rbrakk>w\<close>
  shows \<open>\<lbrakk>\<phi>\<box>\<rightarrow>\<psi>\<rbrakk>w\<close>
  using assms by auto

subsection \<open>Impossible antecedents and strength of counterfactuals (\<section> 1.6)\<close>

text \<open> (p. 26)\<close>
definition Might_weak :: \<open>('aa, 'oo) formula \<Rightarrow> ('aa, 'oo) formula \<Rightarrow> ('aa, 'oo) formula\<close> (\<open>_ \<diamond>\<Rightarrow> _\<close> 25)
  where [simp]: \<open>\<phi> \<diamond>\<Rightarrow> \<psi> \<equiv> ((\<phi> \<diamond>\<rightarrow> \<phi>) \<rightarrow> (\<phi> \<diamond>\<rightarrow> \<psi>))\<close>

text \<open>Implicit dual definition (p. 25)\<close>
definition Would_strong :: \<open>('aa, 'oo) formula \<Rightarrow> ('aa, 'oo) formula \<Rightarrow> ('aa, 'oo) formula\<close> (\<open>_ \<box>\<Rightarrow> _\<close> 25)
  where [simp]: \<open>\<phi> \<box>\<Rightarrow> \<psi> \<equiv> ~~(\<phi> \<diamond>\<Rightarrow> ~~\<psi>)\<close>

context counterfactuals
begin

lemma might_weak_truth_def:
  \<open>(\<lbrakk>\<phi> \<diamond>\<Rightarrow> \<psi>\<rbrakk>w) =
      (\<forall>s \<in> S w.  (\<exists>w\<phi> \<in> s. \<lbrakk>\<phi>\<rbrakk>w\<phi>) \<longrightarrow> (\<exists>ws \<in> s. (\<lbrakk>\<phi>\<rbrakk>ws) \<and>\<lbrakk>\<psi>\<rbrakk>ws))\<close>
  by auto

lemma would_strong_truth_def:
  \<open>(\<lbrakk>\<phi> \<box>\<Rightarrow> \<psi>\<rbrakk>w) =
      (\<exists>s \<in> S w.  (\<exists>w\<phi> \<in> s. \<lbrakk>\<phi>\<rbrakk>w\<phi>) \<and> (\<forall>ws \<in> s. (\<lbrakk>\<phi>\<rbrakk>ws) \<longrightarrow> \<lbrakk>\<psi>\<rbrakk>ws))\<close>
  by auto

text \<open> (p. 26)\<close>
lemma would_by_strong_def:
  \<open>(\<lbrakk>\<phi> \<box>\<rightarrow> \<psi>\<rbrakk>w) =
      (\<lbrakk>(\<phi> \<box>\<Rightarrow> \<phi>) \<rightarrow> (\<phi> \<box>\<Rightarrow> \<psi>)\<rbrakk>w)\<close>
  by auto
end

subsection \<open>Actual antecedents (\<section> 1.7)\<close>

locale counterfactuals_centered = counterfactuals +
  assumes centered_spheres: \<open>(\<forall>w. centered_spheres (S w) w)\<close>
begin

lemma conditional_collapse_for_actual_antecedent:
  assumes \<open>\<lbrakk>\<phi>\<rbrakk>w\<close>
  shows
    \<open>(\<lbrakk>\<phi> \<box>\<rightarrow> \<psi>\<rbrakk>w) = \<lbrakk>\<psi>\<rbrakk>w\<close>
proof -
  from assms have
    \<open>\<exists>w\<phi> \<in> {w}. \<lbrakk>\<phi>\<rbrakk>w\<phi>\<close> \<open>(\<forall>ws \<in> {w}. (\<lbrakk>\<phi>\<rbrakk>ws) \<longrightarrow> \<lbrakk>\<psi>\<rbrakk>ws) = \<lbrakk>\<psi>\<rbrakk>w\<close>
    by (blast+)
  moreover have
    \<open>{w} \<in> S w\<close>
    using centered_spheres unfolding centered_spheres_def by blast
  ultimately show ?thesis
    unfolding is_true_at.simps
    using singleton_iff subsetD psubsetD sphere_direction
    by smt
qed

lemma conditional_collapse_for_actual_antecedent_general:
  assumes \<open>\<lbrakk>\<phi>\<rbrakk>w\<close>
  shows
    \<open>((\<lbrakk>\<phi> \<box>\<Rightarrow> \<psi>\<rbrakk>w) = \<lbrakk>\<psi>\<rbrakk>w) \<and>
    ((\<lbrakk>\<phi> \<diamond>\<Rightarrow> \<psi>\<rbrakk>w)  = \<lbrakk>\<psi>\<rbrakk>w) \<and>
    ((\<lbrakk>\<phi> \<diamond>\<rightarrow> \<psi>\<rbrakk>w)  = \<lbrakk>\<psi>\<rbrakk>w) \<and>
    ((\<lbrakk>\<phi> \<rightarrow> \<psi>\<rbrakk>w)   = \<lbrakk>\<psi>\<rbrakk>w)\<close>
  unfolding Might_def Might_weak_def would_strong_truth_def
  using conditional_collapse_for_actual_antecedent[OF assms] is_true_at.simps(1,3,4)
  by smt


lemma conditional_collapse_for_actual_antecedent_general_unfold:
  assumes \<open>\<lbrakk>\<phi>\<rbrakk>w\<close>
  shows
    \<open>(\<lbrakk>\<phi> \<box>\<Rightarrow> \<psi>\<rbrakk>w) = \<lbrakk>\<psi>\<rbrakk>w\<close>
    \<open>(\<lbrakk>\<phi> \<diamond>\<Rightarrow> \<psi>\<rbrakk>w)  = \<lbrakk>\<psi>\<rbrakk>w\<close>
    \<open>(\<lbrakk>\<phi> \<diamond>\<rightarrow> \<psi>\<rbrakk>w)  = \<lbrakk>\<psi>\<rbrakk>w\<close>
    \<open>(\<lbrakk>\<phi> \<rightarrow> \<psi>\<rbrakk>w)   = \<lbrakk>\<psi>\<rbrakk>w\<close>
  using assms conditional_collapse_for_actual_antecedent_general by auto

text \<open>???In short: counterfactuals with true antecedents reduce to material conditionals.??? (p. 26)\<close>
lemma counterfactuals_are_material_conditional_for_actual_antecedent:
  assumes \<open>\<lbrakk>\<phi>\<rbrakk>w\<close>
  shows \<open>{\<lbrakk>\<phi> \<box>\<rightarrow> \<psi>\<rbrakk>w, \<lbrakk>\<phi> \<box>\<Rightarrow> \<psi>\<rbrakk>w, \<lbrakk>\<phi> \<diamond>\<Rightarrow> \<psi>\<rbrakk>w, \<lbrakk>\<phi> \<diamond>\<rightarrow> \<psi>\<rbrakk>w} = {\<lbrakk>\<phi>\<rightarrow>\<psi>\<rbrakk>w}\<close>
  using assms conditional_collapse_for_actual_antecedent
    conditional_collapse_for_actual_antecedent_general by auto

lemma counterfactual_implies_material_conditional:
  assumes \<open>\<lbrakk>\<phi> \<box>\<rightarrow> \<psi>\<rbrakk>w\<close>
  shows \<open>\<lbrakk>\<phi> \<rightarrow> \<psi>\<rbrakk>w\<close>
  using assms conditional_collapse_for_actual_antecedent by (simp, blast)

lemma counterfactual_modus_ponens:
  assumes \<open>\<lbrakk>\<phi> \<box>\<rightarrow> \<psi>\<rbrakk>w\<close> \<open>\<lbrakk>\<phi>\<rbrakk>w\<close>
  shows \<open>\<lbrakk>\<psi>\<rbrakk>w\<close>
  using assms conditional_collapse_for_actual_antecedent by blast

end

text \<open>\<open>weakly centered system of spheres\<close> with assumption (W) from page 29\<close>
locale counterfactuals_weakly_centered = counterfactuals +
  assumes weakly_centered_spheres: \<open>\<forall>w. (\<forall>s \<in> (S w). s \<noteq> {} \<longrightarrow> w \<in> s) \<and> (\<exists>s \<in> (S w). s \<noteq> {})\<close>

text \<open>???The world \<open>i\<close> itself is one of the closest worlds to \<open>i\<close>;
  but there may be others as well??? (p. 29)\<close>
lemma (in counterfactuals_weakly_centered) innermost_sphere_contains_center:
    \<open>w \<in> innermost_sphere w\<close>
  using weakly_centered_spheres by blast

text \<open>Definition of inner necessity and possibility (p. 30)\<close>

definition InnerlyNecessary :: \<open>('aa, 'oo) formula \<Rightarrow> ('aa, 'oo) formula\<close> (\<open>\<box>\<bullet> _\<close> 20)
  where [simp]: \<open>\<box>\<bullet>\<phi> \<equiv> \<top> \<box>\<Rightarrow> \<phi>\<close>

definition InnerlyPossibly :: \<open>('aa, 'oo) formula \<Rightarrow> ('aa, 'oo) formula\<close> (\<open>\<diamond>\<bullet> _\<close> 20)
  where [simp]: \<open>\<diamond>\<bullet>\<phi> \<equiv> \<top> \<diamond>\<Rightarrow> \<phi>\<close>

lemma (in counterfactuals) inner_modality_duality:
  \<open>(\<lbrakk>\<box>\<bullet>\<phi>\<rbrakk>w) = (\<lbrakk>~~(\<diamond>\<bullet> ~~\<phi>)\<rbrakk>w)\<close>
  by simp

lemma (in counterfactuals) InnerlyNecessary_ext_def:
   \<open>(\<lbrakk>\<box>\<bullet>\<phi>\<rbrakk>w) = (\<exists>s \<in> S w. s \<noteq> {} \<and> (\<forall>wo \<in> s. \<lbrakk>\<phi>\<rbrakk>wo))\<close>
  by auto

lemma (in counterfactuals) InnerlyPossibly_ext_def:
   \<open>(\<lbrakk>\<diamond>\<bullet>\<phi>\<rbrakk>w) = (\<forall>s \<in> S w.  s \<noteq> {} \<longrightarrow> (\<exists>wo \<in> s. \<lbrakk>\<phi>\<rbrakk>wo))\<close>
  by auto

lemma (in counterfactuals_weakly_centered) InnerlyNecessary_innermost_def:
   \<open>(\<lbrakk>\<box>\<bullet>\<phi>\<rbrakk>w) = (\<forall>wi \<in> innermost_sphere w. \<lbrakk>\<phi>\<rbrakk>wi)\<close>
  unfolding InnerlyNecessary_ext_def
  using weakly_centered_spheres innermost_sphere_is_sphere
  by (auto, metis all_not_in_conv innermost_sphere_contains_center)

lemma (in counterfactuals_weakly_centered) InnerlyPossibly_innermost_def:
   \<open>(\<lbrakk>\<diamond>\<bullet>\<phi>\<rbrakk>w) = (\<exists>wi \<in> innermost_sphere w. \<lbrakk>\<phi>\<rbrakk>wi)\<close>
  unfolding InnerlyPossibly_ext_def
  using weakly_centered_spheres innermost_sphere_is_sphere
  by (auto, metis innermost_sphere_contains_center insert_absorb insert_not_empty)

lemma (in counterfactuals_weakly_centered) inner_necessity_weaker:
  assumes \<open>\<lbrakk>\<box>\<phi>\<rbrakk>w\<close>
  shows \<open>\<lbrakk>\<box>\<bullet>\<phi>\<rbrakk>w\<close>
  using assms innermost_in_outermost_sphere weakly_centered_spheres by fastforce

lemma (in counterfactuals_weakly_centered) inner_possibiliy_stronger:
  assumes \<open>\<lbrakk>\<diamond>\<bullet>\<phi>\<rbrakk>w\<close>
  shows \<open>\<lbrakk>\<diamond>\<phi>\<rbrakk>w\<close>
  using assms innermost_in_outermost_sphere weakly_centered_spheres by fastforce

lemma (in counterfactuals_weakly_centered) weakly_centered_simple_inner_modalities:
  shows 
    \<open>(\<lbrakk>\<box>\<bullet>\<phi>\<rbrakk>w) = \<lbrakk>\<top> \<box>\<rightarrow> \<phi>\<rbrakk>w\<close>
    \<open>(\<lbrakk>\<diamond>\<bullet>\<phi>\<rbrakk>w) = \<lbrakk>\<top> \<diamond>\<rightarrow> \<phi>\<rbrakk>w\<close>
  using inner_necessity_weaker is_true_at.simps(3)
  unfolding  InnerlyNecessary_def Necessary_ext_def would_by_strong_def
  by (metis) (auto simp add: weakly_centered_spheres)

lemma (in counterfactuals_weakly_centered) counterfactual_implies_material_conditional:
  assumes \<open>\<lbrakk>\<phi> \<box>\<rightarrow> \<psi>\<rbrakk>w\<close>
  shows \<open>\<lbrakk>\<phi> \<rightarrow> \<psi>\<rbrakk>w\<close>
  using assms using weakly_centered_spheres by auto

\<comment>\<open>first sentence of page 31\<close>
  
lemma (in counterfactuals_centered) centered_trivial_inner_modalities:
  shows 
    \<open>(\<lbrakk>\<box>\<bullet>\<phi>\<rbrakk>w) = \<lbrakk>\<phi>\<rbrakk>w\<close>
    \<open>(\<lbrakk>\<diamond>\<bullet>\<phi>\<rbrakk>w) = \<lbrakk>\<phi>\<rbrakk>w\<close>
  unfolding  InnerlyNecessary_def InnerlyPossibly_def
  using conditional_collapse_for_actual_antecedent_general is_true_at.simps(3)
  by blast+

subsection \<open>Counterfactual inference patterns and fallacies (\<section> 1.8)\<close>

text \<open>The Counterfactual Fallacies (\<section> 1.8) cannot really be rendered in Isabelle's locale framework,
  as there are instantiations where they are not fallacious. However, the fallacy of transitivity
  is already present in the But-if-party example, @{thm party_example.fallacy_of_transitivity}.\<close>

lemma (in counterfactuals) counterfactual_biimplication:
  assumes \<open>\<lbrakk>\<phi> \<box>\<rightarrow> \<psi>\<rbrakk>w\<close> \<open>\<lbrakk>\<psi> \<box>\<rightarrow> \<phi>\<rbrakk>w\<close>
  shows \<open>(\<exists>s \<in> S w. permitting_sphere \<phi> s \<and> (\<forall> w \<in> s. (\<lbrakk>\<phi>\<rbrakk>w) \<longleftrightarrow> \<lbrakk>\<psi>\<rbrakk>w)) \<or>
    \<not>(\<exists>s \<in> S w. permitting_sphere \<phi> s)\<close>
  using assms
  by (simp, smt sphere_direction subsetD subset_not_subset_eq)

text \<open>(inference pattern at the end of p. 33)\<close>
lemma (in counterfactuals) counterfactual_weak_transitivity:
  assumes \<open>\<lbrakk>\<phi> \<box>\<rightarrow> \<chi>\<rbrakk>w\<close> \<open>\<lbrakk>\<chi> \<box>\<rightarrow> \<phi>\<rbrakk>w\<close> \<open>\<lbrakk>\<phi> \<box>\<rightarrow> \<psi>\<rbrakk>w\<close>
  shows \<open>\<lbrakk>\<chi> \<box>\<rightarrow> \<psi>\<rbrakk>w\<close>
proof -
  from assms(1,2) have
    \<open>(\<exists>s \<in> S w. permitting_sphere \<phi> s \<and> (\<forall> w \<in> s. (\<lbrakk>\<phi>\<rbrakk>w) \<longleftrightarrow> \<lbrakk>\<chi>\<rbrakk>w)) \<or>
    \<not>(\<exists>s \<in> S w. permitting_sphere \<phi> s)\<close>
    using counterfactual_biimplication by simp
  then show ?thesis
  proof safe
    fix s wa
    assume subassms: \<open>s \<in> S w\<close> \<open>\<forall>w \<in> s. (\<lbrakk>\<phi>\<rbrakk>w) = \<lbrakk>\<chi>\<rbrakk>w\<close> \<open>wa \<in> s\<close> \<open>\<lbrakk>\<phi>\<rbrakk>wa\<close>
    with assms(3) obtain s' where s'_spec:
      \<open>s' \<in> S w \<and> s' \<subseteq> s \<and> permitting_sphere \<phi> s' \<and> (\<forall>ws \<in> s'. (\<lbrakk>\<phi>\<rbrakk>ws) \<longrightarrow> \<lbrakk>\<psi>\<rbrakk>ws)\<close>
      using sphere_system sphere_direction unfolding nested_spheres_def
      by (simp, meson psubsetD)
    with subassms(2) have \<open>permitting_sphere \<chi> s'\<close> \<open>\<forall>ws \<in> s'. (\<lbrakk>\<chi>\<rbrakk>ws) \<longrightarrow> \<lbrakk>\<psi>\<rbrakk>ws\<close> by blast+
    with s'_spec show ?thesis by auto
  next
    assume \<open>\<not>(\<exists>s \<in> S w. permitting_sphere \<phi> s)\<close>
    with assms(2) have \<open>\<not>(\<exists>s \<in> S w. permitting_sphere \<chi> s)\<close> by auto
    thus ?thesis by simp
  qed
qed

text \<open>(second inference pattern of p. 34)\<close>
lemma (in counterfactuals) counterfactual_special_transitivity:
  assumes \<open>\<lbrakk>\<chi> \<box>\<rightarrow> \<phi>\<rbrakk>w\<close> \<open>\<lbrakk>(And \<chi> \<phi>) \<box>\<rightarrow> \<psi>\<rbrakk>w\<close>
  shows \<open>\<lbrakk>\<chi> \<box>\<rightarrow> \<psi>\<rbrakk>w\<close>
proof -
  have \<open>\<lbrakk>(And \<chi> \<phi>) \<box>\<rightarrow> \<chi>\<rbrakk>w\<close> using assms by auto
  moreover from assms(1) have \<open>\<lbrakk>\<chi> \<box>\<rightarrow> (And \<chi> \<phi>)\<rbrakk>w\<close> by simp
  ultimately show ?thesis using assms(2) counterfactual_weak_transitivity by blast
qed

lemma (in counterfactuals) counterfactual_inference_by_weakening_the_consequent:
  assumes \<open>\<lbrakk>\<chi> \<box>\<rightarrow> \<phi>\<rbrakk>w\<close> \<open>\<lbrakk>\<box>(\<phi> \<rightarrow> \<psi>)\<rbrakk>w\<close>
  shows \<open>\<lbrakk>\<chi> \<box>\<rightarrow> \<psi>\<rbrakk>w\<close>
  using assms by auto

\<comment>\<open>Page 36 states that the following modus tollens for counterfactuals is valid.
The remark does not mention that this is only the case assuming (at least weak)
centering of the spheres. (The other inference patterns do not rely on this
assumption.)\<close>
lemma (in counterfactuals_weakly_centered) counterfactual_modus_tollens:
  assumes \<open>\<lbrakk>\<phi> \<box>\<rightarrow> \<psi>\<rbrakk>w\<close> \<open>\<lbrakk>~~\<psi>\<rbrakk>w\<close>
  shows \<open>\<lbrakk>~~\<phi>\<rbrakk>w\<close>
  using assms counterfactual_implies_material_conditional
  by (meson is_true_at.simps(3))

subsection \<open>Potentialities (\<section> 1.9)\<close>

text \<open>This section is largely concerned with the \<open>de re\<close> nature of many counterfactual
statements. This means that they are talking about \<open>the same\<close> object in different
worlds. The object name usually is fixed in the actual world.

One instance are dispositions where ???a thing has disposition D iff, subjected to test
T, it would give response R??? is analysed by Lewis (p. 38) as:\<close>


locale counterparts = counterfactuals S interpretations objects
  for
    S :: \<open>'world \<Rightarrow> 'world set set\<close> and
    interpretations :: \<open>'world \<Rightarrow> 'a \<Rightarrow> bool\<close> and
    objects :: \<open>'o set\<close> +
  fixes
    counterparts :: \<open>('world \<times> 'o) rel\<close>
  assumes
    \<comment>\<open>???anything is its own unique counterpart at its own world???\<close>
    unique_self_counterpart:
      \<open>((w,n), (w,n)) \<in> counterparts\<close>
      \<open>((w,n), (w,n')) \<in> counterparts \<Longrightarrow> n = n'\<close>
begin

text \<open>???the abstract entities that exist alike from the standpoint of all worlds, but inhabit
  none, are their own unique counterparts at all worlds???\<close>
definition abstract_entity :: \<open>'o \<Rightarrow> bool\<close>
  where \<open>abstract_entity n \<equiv>
    \<forall>w1. \<forall>w2. ((w1,n), (w2,n)) \<in> counterparts \<and>
      (\<forall>n'. (((w1,n), (w2,n')) \<in> counterparts \<or> ((w2,n), (w1,n')) \<in> counterparts)
        \<longrightarrow> n = n')\<close>

\<comment>\<open>This definition follows a \<open>dynamic scoping\<close> of counterparts: For nested counterfactuals,
  one is talking about the counterpart of the counterpart.\<close>
definition assignments :: \<open>('o \<Rightarrow> 'o option) \<Rightarrow> 'world \<Rightarrow> 'world \<Rightarrow> ('o \<Rightarrow> 'o option) set\<close> where
  \<open>assignments \<Gamma> w1 w2 = {f.
    \<forall>obj0. \<forall>obj1. \<forall>obj2.
      ((\<Gamma> obj0 = Some obj1 \<and> Some obj2 = f obj0) \<longrightarrow> ((w1,obj1), (w2,obj2)) \<in> counterparts) \<and>
      ((\<Gamma> obj0 = Some obj1 \<and> ((w1,obj1), (w2,obj2)) \<in> counterparts) \<longrightarrow> f obj0 \<noteq> None) }\<close>

definition initialAssignment :: \<open>'world \<Rightarrow> ('o \<Rightarrow> 'o option)\<close> where
  \<open>initialAssignment w obj \<equiv> if ((w,obj), (w,obj)) \<in> counterparts then Some obj else None\<close>
\<comment>\<open>TODO: for now, everything is defined everywhere, isnt it?\<close>

end

\<comment>\<open>Definition of counterfactuals with counterpart from p. 42\<close>
primrec (in counterparts) is_true_at_objs ::
  \<open>('a, 'o) formula \<Rightarrow> 'world \<Rightarrow> ('o \<Rightarrow> 'o option) \<Rightarrow> bool\<close> (\<open>x\<lbrakk> _ \<rbrakk>_|_\<close> [20] 55)
  where
    \<open>(x\<lbrakk>\<bottom>\<rbrakk>w|\<Gamma>) = False\<close> |
    \<open>(x\<lbrakk>Atom a\<rbrakk>w|\<Gamma>) = interpretations w a\<close> |
    \<open>(x\<lbrakk>\<phi>\<rightarrow>\<psi>\<rbrakk>w|\<Gamma>)   = (\<not>(x\<lbrakk>\<phi>\<rbrakk>w|\<Gamma>) \<or> x\<lbrakk>\<psi>\<rbrakk>w|\<Gamma>)\<close> |
    \<comment>\<open>Definition of counterfactuals with counterpart from p. 42\<close>
    \<open>(x\<lbrakk>\<phi>\<box>\<rightarrow>\<psi>\<rbrakk>w|\<Gamma>) = (
      (\<forall>s \<in> S w. \<not>(\<exists>w\<phi> \<in> s. \<exists>\<Gamma>' \<in> assignments \<Gamma> w w\<phi>. x\<lbrakk>\<phi>\<rbrakk>w\<phi>|\<Gamma>')) \<or>
      (\<exists>s \<in> S w.  (\<exists>w\<phi> \<in> s. \<exists>\<Gamma>' \<in> assignments \<Gamma> w w\<phi>. x\<lbrakk>\<phi>\<rbrakk>w\<phi>|\<Gamma>') \<and> 
                  (\<forall>ws \<in> s. \<forall>\<Gamma>' \<in> assignments \<Gamma> w ws. (x\<lbrakk>\<phi>\<rbrakk>ws|\<Gamma>') \<longrightarrow> x\<lbrakk>\<psi>\<rbrakk>ws|\<Gamma>')))\<close> |
    \<open>(x\<lbrakk>CounterpartPred F obj\<rbrakk>w|\<Gamma>) = (\<exists> o' \<in> set_option (\<Gamma> obj). x\<lbrakk>F o'\<rbrakk>w|\<Gamma>)\<close>
    \<comment>\<open>I just assume that a sentence about an object is false if it has now counterpart.\<close>

text \<open>Page 42f. introduce the idea, that there could be multiple counterpart relations
  operational at the same time. This is virtually impossible to make precise in a formal way.
  When exactly does the picking of the counterpart relations take place?\<close>

text \<open>By the way, I also disagree with the whole argument. Lewis argues that ???If I were you ...???
  sentences should be interpreted as referring to worlds where ???I??? and ???you??? are vicariously
  identical, but picked by different counterpart relations such that the shared counterpart
  is similar to ???me??? with respect to ideas and to ???you??? with respect to predicament.

  I think this is a bit of a stretch. If the teacher says to their student ???If I were you, I'd 
  treat my teachers with more respect.??? this definitely is not a sentence about a world where the
  teacher and the student are the same person. Rather, one should probably understand such sentences
  de-re in only with respect to ???you???, that is, ???If (the counterpart-)you would behave like
  (the actual-world-)me, you would ...???.\<close>

definition (in counterparts) disposed_to :: 
  \<open>('o \<Rightarrow> ('a, 'o) formula) \<Rightarrow> ('o \<Rightarrow> ('a, 'o) formula) \<Rightarrow> 'o \<Rightarrow> 'world \<Rightarrow> bool\<close>
  where
    \<open>disposed_to test response x w \<equiv> 
      x\<lbrakk> CounterpartPred test x \<box>\<rightarrow> CounterpartPred response x \<rbrakk>w|(initialAssignment w)\<close>


context counterfactuals
begin
subsection \<open>Comparative Similarity\<close>

\<comment>\<open>p. 48 Section 2.3 Comparative Similarity\<close>
abbreviation at_least_as_similar_as :: \<open>'world \<Rightarrow> 'world \<Rightarrow> 'world \<Rightarrow> bool\<close>
  where \<open>at_least_as_similar_as w w1 w2 \<equiv> (\<forall> s \<in> S w. w2 \<in> s \<longrightarrow> w1 \<in> s)\<close>
abbreviation more_similar_than :: \<open>'world \<Rightarrow> 'world \<Rightarrow> 'world \<Rightarrow> bool\<close>
  where \<open>more_similar_than w w1 w2 \<equiv> \<not> at_least_as_similar_as w w2 w1\<close>

interpretation preorder \<open>at_least_as_similar_as w\<close> \<open>more_similar_than w\<close>
  by (standard, auto, meson in_mono nested_spheres_def sphere_system)

text \<open>condition 4 from p. 48 ???The world \<open>i\<close> is strictly \<open>\<le>\<^sub>i-minimal\<close>???\<close>
lemma actual_world_minimal:
  assumes
    \<open>centered_spheres (S w) w\<close>
    \<open>w \<noteq> w'\<close>
  shows
    \<open>more_similar_than w w w'\<close>
  using assms unfolding centered_spheres_def by fastforce

text \<open>condition 5 from p. 48 ???Inaccessible worlds are \<open>\<le>\<^sub>i-maximal\<close>???\<close>
lemma inaccessible_worlds_maximal:
  assumes
    \<open>w_max \<notin> outermost_sphere w\<close>
  shows
    \<open>at_least_as_similar_as w w' w_max\<close>
  using assms by blast


text \<open>condition 6 from p. 48 ???Accessible worlds are more similar to \<open>i\<close> than inaccessible wolrds???\<close>
lemma accessible_worlds_more_similar_than_inaccessible:
  assumes
    \<open>w' \<in> outermost_sphere w\<close>
    \<open>w_max \<notin> outermost_sphere w\<close>
  shows
    \<open>more_similar_than w w' w_max\<close>
  using assms by blast

lemma similarity_implies_sphere_order:
  assumes
    \<open>more_similar_than w w1 w2\<close>
  shows
    \<open>\<forall>s2 \<in> S w. w2 \<in> s2 \<longrightarrow> (\<exists>s1 \<in> S w. w1 \<in> s1 \<and> s1 \<subset> s2)\<close>
  using assms sphere_direction
  by (meson in_mono)

lemma similarity_implies_sphere_weak_order:
  assumes
    \<open>at_least_as_similar_as w w1 w2\<close>
    \<open>\<exists>s \<in> S w. w1 \<in> s \<and> w2 \<notin> s\<close>
  shows
    \<open>\<forall>s2 \<in> S w. w2 \<in> s2 \<longrightarrow> (\<exists>s1 \<in> S w. w1 \<in> s1 \<and> s1 \<subset> s2)\<close>
  using assms
  by (meson similarity_implies_sphere_order)

(*lemma similarity_implies_sphere_order:
  assumes
    \<open>w2 \<in> outermost_sphere w\<close>
    \<open>at_least_as_similar_as w w1 w2\<close>
  shows
    \<open>\<exists>s1 \<in> S w. w1 \<in> s1 \<and> (\<forall>s2 \<in> S w. w2 \<in> s2 \<longrightarrow> s1 \<subseteq> s2)\<close>
  using assms sledgehammer
   using nested_spheres_def sphere_system *)

lemma spheres_from_similarity_order:
    \<open>\<forall>w\<phi>. w\<phi> \<in> outermost_sphere w \<longrightarrow> 
    {w' \<in> outermost_sphere w. at_least_as_similar_as w w' w\<phi>} \<in> S w\<close>
proof (rule classical, clarify)
  fix w\<phi> w\<phi>' s
  assume assms:
    \<open>w\<phi> \<in> s\<close> \<open>s \<in> S w\<close> 
    \<open>{w' \<in> outermost_sphere w. at_least_as_similar_as w w' w\<phi>} \<notin> S w\<close>
  hence \<open>\<forall>s \<in> S w. \<exists>w''.
    w'' \<in> s \<longleftrightarrow> w'' \<notin> {w' \<in> outermost_sphere w. at_least_as_similar_as w w' w\<phi>}\<close>
    by (smt antisym subsetI)
  hence \<open>\<forall>s \<in> S w. \<exists>w''.
    w'' \<in> s \<longleftrightarrow> (w'' \<notin> outermost_sphere w \<or> \<not>at_least_as_similar_as w w'' w\<phi>)\<close>
    by auto
  hence \<open>\<forall>s \<in> S w. \<exists>w'' \<in> outermost_sphere w.
    (w'' \<in> s \<longleftrightarrow> (more_similar_than w w\<phi> w''))\<close>
    by (metis Union_iff)
  with assms obtain w'' where w''_spec:
    \<open>w'' \<in> outermost_sphere w\<close>
    \<open>w'' \<in> s \<longleftrightarrow> (more_similar_than w w\<phi> w'')\<close> by blast
  have \<open>False\<close>
  proof (cases \<open>w'' \<in> s\<close>)
    case True
    hence \<open>more_similar_than w w\<phi> w''\<close> using w''_spec by blast
    hence \<open>\<exists>s \<in> S w. w\<phi> \<in> s \<and> w'' \<notin> s\<close> by blast
    then show ?thesis sorry
  next
    case False
    then show ?thesis sorry
  qed
  with assms outermost_sphere_is_sphere have
    \<open>\<exists> w''. w'' \<in> outermost_sphere w \<and> \<not>at_least_as_similar_as w w'' w\<phi>\<close> by meson
  hence \<open>\<exists> w''. more_similar_than w w\<phi> w''\<close> by blast
  show \<open>{w' \<in> outermost_sphere w. at_least_as_similar_as w w' w\<phi>'} \<in> S w \<close> sorry
qed

lemma would_comparative_similarity_def:
  \<open>(\<lbrakk>\<phi> \<box>\<rightarrow> \<psi>\<rbrakk>w) =
      (\<not>permitting_sphere \<phi> (outermost_sphere w) \<or>
      (\<exists>w\<phi> \<in> outermost_sphere w. (\<lbrakk>\<phi>\<rbrakk> w\<phi>)
      \<and> (\<forall>w' \<in> outermost_sphere w. at_least_as_similar_as w w' w\<phi> \<longrightarrow> \<lbrakk>\<phi> \<rightarrow> \<psi>\<rbrakk> w')))\<close>
proof safe
  fix wa s
  assume \<open>\<lbrakk> \<phi> \<box>\<rightarrow> \<psi> \<rbrakk>w\<close> \<open>wa \<in> s\<close> \<open>s \<in> S w\<close> \<open>\<lbrakk> \<phi> \<rbrakk>wa\<close>
    \<open>\<not> (\<exists>w\<phi>\<in>outermost_sphere w. (\<lbrakk> \<phi> \<rbrakk>w\<phi>) \<and> (\<forall>w'\<in>outermost_sphere w. at_least_as_similar_as w w' w\<phi> \<longrightarrow> \<lbrakk> \<phi> \<rightarrow> \<psi> \<rbrakk>w'))\<close>
  then show False by auto
next
  assume \<open>\<not> permitting_sphere \<phi> (outermost_sphere w)\<close>
  then show \<open>\<lbrakk> \<phi> \<box>\<rightarrow> \<psi> \<rbrakk>w\<close> by auto
next
  fix w\<phi> s
  assume subassms: \<open>w\<phi> \<in> s\<close> \<open>s \<in> S w\<close> \<open>\<lbrakk> \<phi> \<rbrakk>w\<phi>\<close>
    \<open>\<forall>w'\<in>outermost_sphere w. at_least_as_similar_as w w' w\<phi> \<longrightarrow> \<lbrakk> \<phi> \<rightarrow> \<psi> \<rbrakk>w'\<close>
  then have \<open>w\<phi> \<in> outermost_sphere w\<close> by blast
  from subassms have
    \<open>permitting_sphere \<phi> {w' \<in> outermost_sphere w. at_least_as_similar_as w w' w\<phi>}
    \<and> (\<forall>ws\<in>{w' \<in> outermost_sphere w. at_least_as_similar_as w w' w\<phi>}. (\<lbrakk> \<phi> \<rbrakk>ws) \<longrightarrow> \<lbrakk> \<psi> \<rbrakk>ws)\<close>
    by auto
  with spheres_from_similarity_order \<open>w\<phi> \<in> outermost_sphere w\<close> show
    \<open>\<lbrakk> \<phi> \<box>\<rightarrow> \<psi> \<rbrakk>w\<close> by (meson is_true_at.simps(4))
qed

subsection \<open>Comparative Possibility\<close>


definition At_least_as_possible ::
  \<open>('aa, 'oo) formula \<Rightarrow> ('aa, 'oo) formula \<Rightarrow> ('aa, 'oo) formula\<close> (\<open>_ \<preceq> _\<close> 23)
  where [simp]: \<open>\<phi> \<preceq> \<psi> \<equiv> ((Or \<phi> \<psi>) \<diamond>\<Rightarrow> \<phi>)\<close>

lemma At_least_as_possible_ext_def:
  \<open>(\<lbrakk>\<phi> \<preceq> \<psi>\<rbrakk>w) = (\<forall>s \<in> S w. permitting_sphere \<psi> s \<longrightarrow> permitting_sphere \<phi> s)\<close>
  by auto

end

subsection \<open>Temporal logics\<close>

definition system_of_semi_future_spheres :: \<open>(('w::linorder) \<Rightarrow> 'w set set) \<Rightarrow> bool\<close> where
  \<open>system_of_semi_future_spheres S \<equiv> \<forall>w. S w = {{w .. t}|t. w \<le> t} \<union> {{w ..< t}|t. w < t} \<union> {{w ..}}\<close>

locale counterfactuals_time = counterfactuals S
  for S :: \<open>('w::linorder) \<Rightarrow> 'w set set\<close> +
  assumes semi_future: \<open>system_of_semi_future_spheres S\<close>
begin

lemma temporal_centered_spheres:
  shows \<open>centered_spheres (S t) t\<close>
  using semi_future
  unfolding system_of_semi_future_spheres_def centered_spheres_def
  by (auto, metis atLeastAtMost_singleton order_refl)

lemma temporal_globally: \<open>(\<lbrakk>\<box> \<phi>\<rbrakk>t) = (\<forall>t' \<ge> t. \<lbrakk>\<phi>\<rbrakk>t')\<close>
  using semi_future unfolding system_of_semi_future_spheres_def Necessary_ext_def by auto

lemma temporal_eventually: \<open>(\<lbrakk>\<diamond> \<phi>\<rbrakk>t) = (\<exists>t' \<ge> t. \<lbrakk>\<phi>\<rbrakk>t')\<close>
  using semi_future unfolding system_of_semi_future_spheres_def Possibly_ext_def by auto

lemma temporal_before:
  \<open>(\<lbrakk>\<phi> \<preceq> \<psi>\<rbrakk>t) = 
    (\<forall>t'. (t \<le> t' \<and> \<lbrakk>\<psi>\<rbrakk>t') \<longrightarrow> (\<exists>t''. t \<le> t'' \<and> t'' \<le> t' \<and> (\<lbrakk>\<phi>\<rbrakk>t'')))\<close>
proof safe
  fix t'
  assume assms: \<open>\<lbrakk> \<phi> \<preceq> \<psi> \<rbrakk>t\<close> \<open>t \<le> t'\<close> \<open>\<lbrakk> \<psi> \<rbrakk>t'\<close>
  hence \<open>permitting_sphere \<psi> {t..t'}\<close> using atLeastAtMost_iff by blast
  moreover have \<open>{t..t'} \<in> S t\<close>
    using semi_future assms(2) unfolding system_of_semi_future_spheres_def by blast
  ultimately have \<open>permitting_sphere \<phi> {t..t'}\<close>
    using assms(1) unfolding At_least_as_possible_ext_def by blast
  thus \<open>\<exists>t''\<ge>t. t'' \<le> t' \<and> \<lbrakk> \<phi> \<rbrakk>t''\<close> by auto
next
  assume \<open>\<forall>t'. (t \<le> t' \<and> \<lbrakk> \<psi> \<rbrakk>t') \<longrightarrow> (\<exists>t''\<ge>t. t'' \<le> t' \<and> \<lbrakk> \<phi> \<rbrakk>t'')\<close>
  thus \<open>\<lbrakk> \<phi> \<preceq> \<psi> \<rbrakk>t\<close>
    using semi_future unfolding system_of_semi_future_spheres_def At_least_as_possible_ext_def
    by (auto, meson atLeastAtMost_iff order_trans, meson atLeastLessThan_iff le_less_trans)
qed

end


locale counterfactuals_discrete_time =
  counterfactuals_time + counterfactuals_limit_assumption
begin

lemma end_of_time_trimmable:
  assumes
    \<open>{t .. t'} \<in> S t\<close>
  shows
    \<open>{t ..< t'} \<in> S t\<close>
  using assms wf_spheres semi_future unfolding system_of_semi_future_spheres_def
  sorry
  

lemma temporal_until:
  assumes
    \<open>(\<lbrakk>And (\<phi> \<preceq> ~~\<psi>) (\<diamond> \<phi>)\<rbrakk>t)\<close>
  shows
    \<open>\<exists>t' \<ge> t. (\<lbrakk>\<phi>\<rbrakk>t') \<and> (\<forall>t''. t \<le> t'' \<and> t'' < t' \<longrightarrow> (\<lbrakk>\<psi>\<rbrakk>t''))\<close>
proof -
  from assms obtain t\<phi> where \<open>t\<phi> \<ge> t\<close> \<open>\<lbrakk>\<phi>\<rbrakk>t\<phi>\<close>
    unfolding tarski_and temporal_eventually by blast
  hence t\<phi>_spec2: \<open>permitting_sphere \<phi> {t..t\<phi>} \<and> {t..t\<phi>} \<in> S t\<close>
    using semi_future unfolding system_of_semi_future_spheres_def
    by auto
  hence first: \<open>smallest_sphere t \<phi> \<in> S t \<and> permitting_sphere \<phi> (smallest_sphere t \<phi>) \<and>
      (\<forall>t'' \<in> S t. permitting_sphere \<phi> t'' \<longrightarrow> (smallest_sphere t \<phi>) \<subseteq> t'')\<close>
    using wellfounded_smallest_sphere by blast
  hence \<open>smallest_sphere t \<phi> \<subseteq> {t..t\<phi>}\<close>
    using t\<phi>_spec2 by blast
  hence \<open>smallest_sphere t \<phi> = {t..} \<Longrightarrow> smallest_sphere t \<phi> = {t..t\<phi>}\<close> by auto
  hence \<open>\<exists>t'. smallest_sphere t \<phi> = {t..t'} \<or> smallest_sphere t \<phi> = {t ..< t'}\<close>
    using semi_future first unfolding system_of_semi_future_spheres_def by auto
  then obtain t' where t'_spec:
    \<open>smallest_sphere t \<phi> = {t..t'} \<or> smallest_sphere t \<phi> = {t ..< t'}\<close> by blast
  hence \<open>\<forall>s \<in> S t. s \<subset> {t .. t'} \<longrightarrow> \<not>permitting_sphere \<phi> s\<close>
    using first
    sorry
    (* {t ..< t'} by (smt Diff_empty Diff_insert0 atLeastLessThan_eq_atLeastAtMost_diff
         insert_Diff insert_subset psubsetE)*)
  hence \<open>\<forall>s \<in> S t. s \<subset> {t .. t'} \<longrightarrow> \<not>permitting_sphere (~~\<psi>) s\<close>
    using assms unfolding tarski_and At_least_as_possible_ext_def by blast
  hence \<open>\<forall>s \<in> S t. s \<subseteq> {t ..< t'} \<longrightarrow> \<not>permitting_sphere (~~\<psi>) s\<close>
    by (smt Diff_subset atLeastAtMost_iff atLeastLessThan_eq_atLeastAtMost_diff atLeastLessThan_iff atLeastatMost_psubset_iff order_refl order_trans psubsetI subset_antisym)
  moreover have \<open>{t ..< t'} \<in> S t\<close>
    using first t'_spec end_of_time_trimmable by auto
  ultimately have \<open>\<not>permitting_sphere (~~\<psi>) {t ..< t'}\<close> by blast
  hence \<open>(\<forall>t''. t \<le> t'' \<and> t'' < t' \<longrightarrow> \<lbrakk> \<psi> \<rbrakk>t'')\<close> by auto
  moreover have \<open>\<lbrakk>\<phi>\<rbrakk>t'\<close>
    using first
    by (smt Diff_subset \<open>\<forall>s\<in>S t. s \<subset> {t..t'} \<longrightarrow> \<not> permitting_sphere \<phi> s\<close> \<open>{t..<t'} \<in> S t\<close> atLeastAtMost_iff atLeastLessThan_eq_atLeastAtMost_diff atLeastLessThan_iff atLeastatMost_empty_iff empty_iff le_less not_le sphere_direction t'_spec)
  moreover have \<open>t' \<ge> t\<close>
    using first t'_spec by force
  ultimately show ?thesis
    by blast
qed

end





end

locale counterfactuals_centered2 = counterfactuals S
  for S :: \<open>'world \<Rightarrow> 'world set set\<close> +
  fixes aw :: \<open>'world\<close>
begin

abbreviation at_least_as_similar_as_c
  where \<open>at_least_as_similar_as_c \<equiv> at_least_as_similar_as aw\<close>
abbreviation more_similar_than_c
  where \<open>more_similar_than_c \<equiv> more_similar_than aw\<close>

interpretation preorder \<open>at_least_as_similar_as_c\<close> \<open>more_similar_than_c\<close>
  by (standard, auto, meson in_mono nested_spheres_def sphere_system)



end

end