theory Misc_Tensor_Product
  imports Complex_Bounded_Operators.Complex_L2
begin

unbundle cblinfun_notation

(* TODO move, explain *)
lemma local_defE: "(\<And>x. x=y \<Longrightarrow> P) \<Longrightarrow> P" by metis

lemma on_closure_leI:
  fixes f g :: \<open>'a::topological_space \<Rightarrow> 'b::linorder_topology\<close>
  assumes eq: \<open>\<And>x. x \<in> S \<Longrightarrow> f x \<le> g x\<close>
  assumes xS: \<open>x \<in> closure S\<close>
  assumes cont: \<open>continuous_on UNIV f\<close> \<open>continuous_on UNIV g\<close> (* Is "isCont f x" "isCont g x" sufficient? *)
  shows \<open>f x \<le> g x\<close>
proof -
  define X where \<open>X = {x. f x \<le> g x}\<close>
  have \<open>closed X\<close>
    using cont by (simp add: X_def closed_Collect_le)
  moreover have \<open>S \<subseteq> X\<close>
    by (simp add: X_def eq subsetI)
  ultimately have \<open>closure S \<subseteq> X\<close>
    using closure_minimal by blast
  with xS have \<open>x \<in> X\<close>
    by auto
  then show ?thesis
    using X_def by blast
qed

lemma norm_cblinfun_bound_dense:
  assumes \<open>0 \<le> b\<close>
  assumes S: \<open>closure S = UNIV\<close>
  assumes bound: \<open>\<And>x. x\<in>S \<Longrightarrow> norm (cblinfun_apply f x) \<le> b * norm x\<close>
  shows \<open>norm f \<le> b\<close>
proof -
  have 1: \<open>continuous_on UNIV (\<lambda>a. norm (f *\<^sub>V a))\<close>
    apply (intro continuous_on_norm linear_continuous_on)
    by (simp add: Complex_Vector_Spaces.bounded_clinear.bounded_linear cblinfun.bounded_clinear_right)
  have 2: \<open>continuous_on UNIV (\<lambda>a. b * norm a)\<close>
    using continuous_on_mult_left continuous_on_norm_id by blast
  have \<open>norm (cblinfun_apply f x) \<le> b * norm x\<close> for x
    apply (rule on_closure_leI[where x=x and S=S])
    using S bound 1 2 by auto
  then show \<open>norm f \<le> b\<close>
    apply (rule_tac norm_cblinfun_bound)
    using \<open>0 \<le> b\<close> by auto
qed

lemma orthogonal_complement_of_cspan: \<open>orthogonal_complement A = orthogonal_complement (cspan A)\<close>
  by (metis (no_types, opaque_lifting) closed_csubspace.subspace complex_vector.span_minimal complex_vector.span_superset double_orthogonal_complement_increasing orthogonal_complement_antimono orthogonal_complement_closed_subspace subset_antisym)

lemma orthogonal_complement_orthogonal_complement_closure_cspan:
  \<open>orthogonal_complement (orthogonal_complement S) = closure (cspan S)\<close> for S :: \<open>'a::chilbert_space set\<close>
proof -
  have \<open>orthogonal_complement (orthogonal_complement S) = orthogonal_complement (orthogonal_complement (closure (cspan S)))\<close>
    by (simp flip: orthogonal_complement_of_closure orthogonal_complement_of_cspan)
  also have \<open>\<dots> = closure (cspan S)\<close>
    by simp
  finally show \<open>orthogonal_complement (orthogonal_complement S) = closure (cspan S)\<close>
    by -
qed

lemma dense_span_separating: \<open>closure (cspan S) = UNIV \<Longrightarrow> bounded_clinear F \<Longrightarrow> bounded_clinear G \<Longrightarrow> (\<forall>x\<in>S. F x = G x) \<Longrightarrow> F = G\<close>
proof -
  fix F G :: \<open>'a \<Rightarrow> 'b\<close>
  assume dense: \<open>closure (cspan S) = UNIV\<close>
  assume [simp]: \<open>bounded_clinear F\<close> \<open>bounded_clinear G\<close>
  assume \<open>\<forall>x\<in>S. F x = G x\<close>
  then have \<open>F x = G x\<close> if \<open>x \<in> cspan S\<close> for x
    apply (rule_tac complex_vector.linear_eq_on[of F G _ S])
    using that by (auto simp: bounded_clinear.clinear)
  then show \<open>F = G\<close>
    apply (rule_tac ext)
    apply (rule on_closure_eqI[of \<open>cspan S\<close> F G])
    using dense by (auto intro!: continuous_at_imp_continuous_on clinear_continuous_at)
qed

lemma separating_dense_span: 
  assumes \<open>\<And>F G :: 'a::chilbert_space \<Rightarrow> 'b::{complex_normed_vector,not_singleton}. 
           bounded_clinear F \<Longrightarrow> bounded_clinear G \<Longrightarrow> (\<forall>x\<in>S. F x = G x) \<Longrightarrow> F = G\<close>
  shows \<open>closure (cspan S) = UNIV\<close>
proof -
  have \<open>\<psi> = 0\<close> if \<open>\<psi> \<in> orthogonal_complement S\<close> for \<psi>
  proof -
    obtain \<phi> :: 'b where \<open>\<phi> \<noteq> 0\<close>
      by fastforce
    have \<open>(\<lambda>x. cinner \<psi> x *\<^sub>C \<phi>) = (\<lambda>_. 0)\<close> 
      apply (rule assms[rule_format])
      using orthogonal_complement_orthoI that
      by (auto simp add: bounded_clinear_cinner_right bounded_clinear_scaleC_const)
    then have \<open>cinner \<psi> \<psi> = 0\<close>
      by (meson \<open>\<phi> \<noteq> 0\<close> scaleC_eq_0_iff)
    then show \<open>\<psi> = 0\<close>
      by auto
  qed
  then have \<open>orthogonal_complement (orthogonal_complement S) = UNIV\<close>
    by (metis UNIV_eq_I cinner_zero_right orthogonal_complementI)
  then show \<open>closure (cspan S) = UNIV\<close>
    by (simp add: orthogonal_complement_orthogonal_complement_closure_cspan)
qed


lemma ortho_basis_exists: 
  fixes S :: \<open>'a::chilbert_space set\<close>
  assumes \<open>is_ortho_set S\<close>
  shows \<open>\<exists>B. B \<supseteq> S \<and> is_ortho_set B \<and> closure (cspan B) = UNIV\<close>
proof -
  define on where \<open>on B \<longleftrightarrow> B \<supseteq> S \<and> is_ortho_set B\<close> for B :: \<open>'a set\<close>
  have \<open>\<exists>B\<in>Collect on. \<forall>B'\<in>Collect on. B \<subseteq> B' \<longrightarrow> B' = B\<close>
  proof (rule subset_Zorn_nonempty; simp)
    show \<open>\<exists>S. on S\<close>
      apply (rule exI[of _ S])
      using assms on_def by fastforce
  next
    fix C :: \<open>'a set set\<close>
    assume \<open>C \<noteq> {}\<close>
    assume \<open>subset.chain (Collect on) C\<close>
    then have C_on: \<open>B \<in> C \<Longrightarrow> on B\<close> and C_order: \<open>B \<in> C \<Longrightarrow> B' \<in> C \<Longrightarrow> B \<subseteq> B' \<or> B' \<subseteq> B\<close> for B B'
      by (auto simp: subset.chain_def)
    have \<open>is_orthogonal x y\<close> if \<open>x\<in>\<Union>C\<close> \<open>y\<in>\<Union>C\<close> \<open>x \<noteq> y\<close> for x y
      by (smt (verit) UnionE C_order C_on on_def is_ortho_set_def subsetD that(1) that(2) that(3))
    moreover have \<open>0 \<notin> \<Union> C\<close>
      by (meson UnionE C_on is_ortho_set_def on_def)
    moreover have \<open>\<Union>C \<supseteq> S\<close>
      using C_on \<open>C \<noteq> {}\<close> on_def by blast
    ultimately show \<open>on (\<Union> C)\<close>
      unfolding on_def is_ortho_set_def by simp
  qed
  then obtain B where \<open>on B\<close> and B_max: \<open>B' \<supseteq> B \<Longrightarrow> on B' \<Longrightarrow> B=B'\<close> for B'
    by auto
  have \<open>\<psi> = 0\<close> if \<psi>ortho: \<open>\<forall>b\<in>B. is_orthogonal \<psi> b\<close> for \<psi> :: 'a
  proof (rule ccontr)
    assume \<open>\<psi> \<noteq> 0\<close>
    define \<phi> B' where \<open>\<phi> = \<psi> /\<^sub>R norm \<psi>\<close> and \<open>B' = B \<union> {\<phi>}\<close>
    have [simp]: \<open>norm \<phi> = 1\<close>
      using \<open>\<psi> \<noteq> 0\<close> by (auto simp: \<phi>_def)
    have \<phi>ortho: \<open>is_orthogonal \<phi> b\<close> if \<open>b \<in> B\<close> for b
      using \<psi>ortho that \<phi>_def  apply auto
      by (simp add: scaleR_scaleC)
    have orthoB': \<open>is_orthogonal x y\<close> if \<open>x\<in>B'\<close> \<open>y\<in>B'\<close> \<open>x \<noteq> y\<close> for x y
      using that \<open>on B\<close> \<phi>ortho \<phi>ortho[THEN is_orthogonal_sym[THEN iffD1]]
      by (auto simp: B'_def on_def is_ortho_set_def)
    have B'0: \<open>0 \<notin> B'\<close>
      using B'_def \<open>norm \<phi> = 1\<close> \<open>on B\<close> is_ortho_set_def on_def by fastforce
    have \<open>S \<subseteq> B'\<close>
      using B'_def \<open>on B\<close> on_def by auto
    from orthoB' B'0 \<open>S \<subseteq> B'\<close> have \<open>on B'\<close>
      by (simp add: on_def is_ortho_set_def)
    with B_max have \<open>B = B'\<close>
      by (metis B'_def Un_upper1)
    then have \<open>\<phi> \<in> B\<close>
      using B'_def by blast
    then have \<open>is_orthogonal \<phi> \<phi>\<close>
      using \<phi>ortho by blast
    then show False
      using B'0 \<open>B = B'\<close> \<open>\<phi> \<in> B\<close> by fastforce
  qed 
  then have \<open>orthogonal_complement B = {0}\<close>
    by (auto simp: orthogonal_complement_def)
  then have \<open>UNIV = orthogonal_complement (orthogonal_complement B)\<close>
    by simp
  also have \<open>\<dots> = orthogonal_complement (orthogonal_complement (closure (cspan B)))\<close>
    by (metis (mono_tags, opaque_lifting) \<open>orthogonal_complement B = {0}\<close> cinner_zero_left complex_vector.span_superset empty_iff insert_iff orthogonal_complementI orthogonal_complement_antimono orthogonal_complement_of_closure subsetI subset_antisym)
  also have \<open>\<dots> = closure (cspan B)\<close>
    apply (rule double_orthogonal_complement_id)
    by simp
  finally have \<open>closure (cspan B) = UNIV\<close>
    by simp
  with \<open>on B\<close> show ?thesis
    by (auto simp: on_def)
qed

lemma (in vector_space) span_image_scale:
  assumes nz: "\<And>x. x \<in> S \<Longrightarrow> c x \<noteq> 0"
  shows "span ((\<lambda>x. c x *s x) ` S) = span S"
proof
  have \<open>((\<lambda>x. c x *s x) ` S) \<subseteq> span S\<close>
    by (metis (mono_tags, lifting) image_subsetI in_mono local.span_superset local.subspace_scale local.subspace_span)
  then show \<open>span ((\<lambda>x. c x *s x) ` S) \<subseteq> span S\<close>
    by (simp add: local.span_minimal)
next
  have \<open>x \<in> span ((\<lambda>x. c x *s x) ` S)\<close> if \<open>x \<in> S\<close> for x
  proof -
    have \<open>x = inverse (c x) *s c x *s x\<close>
      by (simp add: nz that)
    moreover have \<open>c x *s x \<in> (\<lambda>x. c x *s x) ` S\<close>
      using that by blast
    ultimately show ?thesis
      by (metis local.span_base local.span_scale)
  qed
  then show \<open>span S \<subseteq> span ((\<lambda>x. c x *s x) ` S)\<close>
    by (simp add: local.span_minimal subsetI)
qed

lemma orthonormal_basis_exists: 
  fixes S :: \<open>'a::chilbert_space set\<close>
  assumes \<open>is_ortho_set S\<close> and \<open>\<And>x. x\<in>S \<Longrightarrow> norm x = 1\<close>
  shows \<open>\<exists>B. B \<supseteq> S \<and> is_ortho_set B \<and> (\<forall>b\<in>B. norm b = 1) \<and> closure (cspan B) = UNIV\<close>
proof -
  from \<open>is_ortho_set S\<close>
  obtain B where \<open>is_ortho_set B\<close> and \<open>B \<supseteq> S\<close> and \<open>closure (cspan B) = UNIV\<close>
    using ortho_basis_exists by blast
  define B' where \<open>B' = (\<lambda>x. x /\<^sub>R norm x) ` B\<close>
  have \<open>S = (\<lambda>x. x /\<^sub>R norm x) ` S\<close>
    by (simp add: assms(2))
  then have \<open>B' \<supseteq> S\<close>
    using B'_def \<open>S \<subseteq> B\<close> by blast
  moreover have \<open>closure (cspan B') = UNIV\<close>
    apply (simp add: B'_def scaleR_scaleC)
    apply (subst complex_vector.span_image_scale)
    using \<open>is_ortho_set B\<close> \<open>closure (cspan B) = UNIV\<close> is_ortho_set_def by auto
  moreover have \<open>is_ortho_set B'\<close>
    using \<open>is_ortho_set B\<close> apply (auto simp: B'_def is_ortho_set_def)
    by (metis cinner_simps(5) is_orthogonal_sym mult_zero_right scaleR_scaleC)
  moreover have \<open>\<forall>b\<in>B'. norm b = 1\<close>
    using \<open>is_ortho_set B\<close> apply (auto simp: B'_def is_ortho_set_def)
    by (metis field_class.field_inverse norm_eq_zero)
  ultimately show ?thesis
    by auto
qed


lemma bounded_clinear_equal_ket:
  fixes f g :: \<open>'a ell2 \<Rightarrow> _\<close>
  assumes \<open>bounded_clinear f\<close>
  assumes \<open>bounded_clinear g\<close>
  assumes \<open>\<And>i. f (ket i) = g (ket i)\<close>
  shows \<open>f = g\<close>
  apply (rule ext)
  apply (rule bounded_clinear_eq_on[of f g \<open>range ket\<close>])
  using assms by auto

lemma cspan_eqI:
  assumes \<open>\<And>a. a\<in>A \<Longrightarrow> a\<in>cspan B\<close>
  assumes \<open>\<And>b. b\<in>B \<Longrightarrow> b\<in>cspan A\<close>
  shows \<open>cspan A = cspan B\<close>
  apply (rule complex_vector.span_subspace[rotated])
    apply (rule complex_vector.span_minimal)
  using assms by auto

unbundle no_cblinfun_notation

end
