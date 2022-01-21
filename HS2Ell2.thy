theory HS2Ell2
  imports Complex_Bounded_Operators.Complex_L2
begin

unbundle cblinfun_notation

(* TODO move *)
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

(* TODO move *)
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

(* TODO move *)
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

definition some_chilbert_basis :: \<open>'a::chilbert_space set\<close> where
  \<open>some_chilbert_basis = (SOME B::'a set. is_ortho_set B \<and> (\<forall>b\<in>B. norm b = 1) \<and> closure (cspan B) = UNIV)\<close>

lemma
  defines \<open>basis == some_chilbert_basis :: 'a::chilbert_space set\<close>
  shows is_ortho_set_some_chilbert_basis: \<open>is_ortho_set basis\<close>
    and is_normal_some_chilbert_basis: \<open>\<And>x. x \<in> basis \<Longrightarrow> norm x = 1\<close>
    and span_some_chilbert_basis[simp]: \<open>closure (cspan basis) = UNIV\<close>
proof -
  define P where \<open>P B \<longleftrightarrow> is_ortho_set B \<and> (\<forall>b\<in>B. norm b = 1) \<and> closure (cspan B) = UNIV\<close> for B :: \<open>'a set\<close>
  with orthonormal_basis_exists[OF is_ortho_set_empty] have ex: \<open>\<exists>B. P B\<close>
    by auto
  have \<open>basis = (SOME B. P B)\<close>
    using P_def basis_def some_chilbert_basis_def by auto
  with ex have \<open>P basis\<close>
    by (simp add: someI_ex)
  then show \<open>is_ortho_set basis\<close>
    using P_def by simp
  show \<open>\<And>x. x \<in> basis \<Longrightarrow> norm x = 1\<close>
    using P_def \<open>P basis\<close> by simp
  show \<open>closure (cspan basis) = UNIV\<close>
    using P_def \<open>P basis\<close> by simp
qed

lemma ccspan_some_chilbert_basis[simp]: \<open>ccspan some_chilbert_basis = \<top>\<close>
  apply transfer by (rule span_some_chilbert_basis)

lemma some_chilbert_basis_nonempty: \<open>(some_chilbert_basis :: 'a::{chilbert_space, not_singleton} set) \<noteq> {}\<close>
proof (rule ccontr, simp)
  define B :: \<open>'a set\<close> where \<open>B = some_chilbert_basis\<close>
  assume [simp]: \<open>B = {}\<close>
  have \<open>UNIV = closure (cspan B)\<close>
    using B_def span_some_chilbert_basis by blast
  also have \<open>\<dots> = {0}\<close>
    by simp
  also have \<open>\<dots> \<noteq> UNIV\<close>
    using Extra_General.UNIV_not_singleton by blast
  finally show False
    by simp
qed

typedef (overloaded) 'a::\<open>{chilbert_space, not_singleton}\<close> chilbert2ell2 = \<open>some_chilbert_basis :: 'a set\<close>
  using some_chilbert_basis_nonempty by auto

definition ell2_to_hilbert where \<open>ell2_to_hilbert = cblinfun_extension (range ket) (Rep_chilbert2ell2 o inv ket)\<close>

lemma ell2_to_hilbert_ket: \<open>ell2_to_hilbert *\<^sub>V ket x = Rep_chilbert2ell2 x\<close>
proof -
  have \<open>cblinfun_extension_exists (range ket) (Rep_chilbert2ell2 o inv ket)\<close>
    apply (rule cblinfun_extension_exists_ortho[where B=1])
       apply auto
    apply (metis Rep_chilbert2ell2 Rep_chilbert2ell2_inject is_ortho_set_def is_ortho_set_some_chilbert_basis)
    by (simp add: Rep_chilbert2ell2 is_normal_some_chilbert_basis)
  then show ?thesis
    apply (simp add: ell2_to_hilbert_def)
    apply (subst cblinfun_extension_apply)
    by simp_all
qed

lemma norm_ell2_to_hilbert: \<open>norm ell2_to_hilbert = 1\<close>
proof (rule order.antisym)
  show \<open>norm ell2_to_hilbert \<le> 1\<close>
    unfolding ell2_to_hilbert_def
    apply (rule cblinfun_extension_exists_ortho_norm[where B=1])
       apply auto
    apply (metis Rep_chilbert2ell2 Rep_chilbert2ell2_inject is_ortho_set_def is_ortho_set_some_chilbert_basis)
    by (simp add: Rep_chilbert2ell2 is_normal_some_chilbert_basis)
  show \<open>norm ell2_to_hilbert \<ge> 1\<close>
    apply (rule cblinfun_norm_geqI[where x=\<open>ket undefined\<close>])
    apply (auto simp: ell2_to_hilbert_ket)
    by (simp add: Rep_chilbert2ell2 is_normal_some_chilbert_basis)
qed

lemma unitary_ell2_to_hilbert: \<open>unitary ell2_to_hilbert\<close>
proof (rule surj_isometry_is_unitary)
  show \<open>isometry (ell2_to_hilbert :: 'a chilbert2ell2 ell2 \<Rightarrow>\<^sub>C\<^sub>L _)\<close>
  proof (rule orthogonal_on_basis_is_isometry)
    show \<open>ccspan (range ket) = \<top>\<close>
      by auto
    fix x y :: \<open>'a chilbert2ell2 ell2\<close>
    assume \<open>x \<in> range ket\<close> \<open>y \<in> range ket\<close>
    then obtain x' y' where [simp]: \<open>x = ket x'\<close> \<open>y = ket y'\<close>
      by auto
    show \<open>(ell2_to_hilbert *\<^sub>V x) \<bullet>\<^sub>C (ell2_to_hilbert *\<^sub>V y) = x \<bullet>\<^sub>C y\<close>
    proof (cases \<open>x'=y'\<close>)
      case True
      then show ?thesis
        apply (auto simp: ell2_to_hilbert_ket)
        using Rep_chilbert2ell2 cnorm_eq_1 is_normal_some_chilbert_basis by blast
    next
      case False
      then show ?thesis
        apply (auto simp: ell2_to_hilbert_ket cinner_ket)
        by (metis Rep_chilbert2ell2 Rep_chilbert2ell2_inject is_ortho_set_def is_ortho_set_some_chilbert_basis)
    qed
  qed
  have \<open>cblinfun_apply ell2_to_hilbert ` range ket \<supseteq> some_chilbert_basis\<close>
    by (metis Rep_chilbert2ell2_cases UNIV_I ell2_to_hilbert_ket image_eqI subsetI)
  then have \<open>ell2_to_hilbert *\<^sub>S \<top> \<ge> ccspan some_chilbert_basis\<close> (is \<open>_ \<ge> \<dots>\<close>)
    by (smt (verit, del_insts) cblinfun_image_ccspan ccspan_mono ccspan_range_ket)
  also have \<open>\<dots> = \<top>\<close>
    by simp
  finally show \<open>ell2_to_hilbert *\<^sub>S \<top> = \<top>\<close>
    by (simp add: top.extremum_unique)
qed

lemma ell2_to_hilbert_adj_ket: \<open>ell2_to_hilbert* *\<^sub>V \<psi> = ket (Abs_chilbert2ell2 \<psi>)\<close> if \<open>\<psi> \<in> some_chilbert_basis\<close>
  using ell2_to_hilbert_ket unitary_ell2_to_hilbert
  by (metis (no_types, lifting) cblinfun_apply_cblinfun_compose cblinfun_id_cblinfun_apply that type_definition.Abs_inverse type_definition_chilbert2ell2 unitaryD1)

unbundle no_cblinfun_notation

end
