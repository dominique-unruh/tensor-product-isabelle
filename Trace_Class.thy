theory Trace_Class
  imports Complex_Bounded_Operators.Complex_L2 Misc_Tensor_Product HS2Ell2
    "HOL-Cardinals.Cardinals"
begin

unbundle cblinfun_notation

no_notation elt_set_eq (infix "=o" 50)

lemma space_as_set_bot[simp]: \<open>space_as_set \<bottom> = {0}\<close>
  by (rule bot_ccsubspace.rep_eq)

lemma card_prod_omega: \<open>X *c natLeq =o X\<close> if \<open>Cinfinite X\<close>
  by (simp add: Cinfinite_Cnotzero cprod_infinite1' natLeq_Card_order natLeq_cinfinite natLeq_ordLeq_cinfinite that)

lemma countable_leq_natLeq: \<open>|X| \<le>o natLeq\<close> if \<open>countable X\<close>
  using subset_range_from_nat_into[OF that]
  by (meson card_of_nat ordIso_iff_ordLeq ordLeq_transitive surj_imp_ordLeq)

lemma norm_Proj_leq1: \<open>norm (Proj M) \<le> 1\<close>
  apply transfer
  by (metis (no_types, opaque_lifting) mult.left_neutral onorm_bound projection_reduces_norm zero_less_one_class.zero_le_one)

lemma Proj_orthog_ccspan_insert:
  assumes "\<And>y. y \<in> Y \<Longrightarrow> is_orthogonal x y"
  shows \<open>Proj (ccspan (insert x Y)) = proj x + Proj (ccspan Y)\<close>
  apply (subst asm_rl[of \<open>insert x Y = {x} \<union> Y\<close>], simp)
  apply (rule Proj_orthog_ccspan_union)
  using assms by auto

(* TODO following conway functional, Prop 4.14 *)
lemma all_onbs_same_card:
  fixes E F :: \<open>'a::chilbert_space set\<close>
    (* TODO: ortho basis is sufficient *)
  assumes \<open>is_onb E\<close> \<open>is_onb F\<close>
  shows \<open>\<exists>f. bij_betw f E F\<close>
proof -
  have \<open>|F| \<le>o |E|\<close> if \<open>infinite E\<close> and \<open>is_onb E\<close> and \<open>is_onb F\<close> for E F :: \<open>'a set\<close>
  proof -
    define F' where \<open>F' e = {f\<in>F. \<not> is_orthogonal f e}\<close> for e
    have \<open>\<exists>e\<in>E. f \<bullet>\<^sub>C e \<noteq> 0\<close> if \<open>f \<in> F\<close> for f
    proof (rule ccontr, simp)
      assume \<open>\<forall>e\<in>E. is_orthogonal f e\<close>
      then have \<open>f \<in> orthogonal_complement E\<close>
        by (simp add: orthogonal_complementI)
      also have \<open>\<dots> = orthogonal_complement (closure (cspan E))\<close>
        using orthogonal_complement_of_closure orthogonal_complement_of_cspan by blast
      also have \<open>\<dots> = space_as_set (- ccspan E)\<close>
        apply transfer by simp
      also have \<open>\<dots> = space_as_set (- \<top>)\<close>
        by (metis \<open>is_onb E\<close> is_onb_def)
      also have \<open>\<dots> = {0}\<close>
        by auto
      finally have \<open>f = 0\<close>
        by simp
      with \<open>f \<in> F\<close> \<open>is_onb F\<close> show False
        by (simp add: is_onb_def is_ortho_set_def)
    qed
    then have F'_union: \<open>F = (\<Union>e\<in>E. F' e)\<close>
      unfolding F'_def by auto
    have \<open>countable (F' e)\<close> for e
    proof -
      have \<open>(\<Sum>f\<in>M. (cmod (f \<bullet>\<^sub>C e))\<^sup>2) \<le> (norm e)\<^sup>2\<close> if \<open>finite M\<close> and \<open>M \<subseteq> F\<close> for M
      proof -
        have [simp]: \<open>is_ortho_set M\<close>
          by (meson \<open>is_onb F\<close> is_onb_def is_ortho_set_antimono that(2))
        have [simp]: \<open>norm x = 1\<close> if \<open>x \<in> M\<close> for x
          using \<open>M \<subseteq> F\<close> \<open>is_onb F\<close> is_onb_def that by blast
        have \<open>(\<Sum>f\<in>M. (cmod (f \<bullet>\<^sub>C e))\<^sup>2) = (\<Sum>f\<in>M. (norm ((f \<bullet>\<^sub>C e) *\<^sub>C f))\<^sup>2)\<close>
          apply (rule sum.cong[OF refl])
          by simp
        also have \<open>\<dots> = (norm (\<Sum>f\<in>M. ((f \<bullet>\<^sub>C e) *\<^sub>C f)))\<^sup>2\<close>
          apply (rule pythagorean_theorem_sum[symmetric])
          using that apply auto
          by (metis \<open>is_ortho_set M\<close> is_ortho_set_def)
        also have \<open>\<dots> = (norm (\<Sum>f\<in>M. proj f e))\<^sup>2\<close>
          by (metis (mono_tags, lifting) \<open>is_onb F\<close> butterfly_apply butterfly_eq_proj is_onb_def subset_eq sum.cong that(2))
        also have \<open>\<dots> = (norm (Proj (ccspan M) e))\<^sup>2\<close>
          apply (rule arg_cong[where f=\<open>\<lambda>x. (norm x)\<^sup>2\<close>])
          using \<open>finite M\<close> \<open>is_ortho_set M\<close> apply induction
           apply simp
          by (smt (verit, ccfv_threshold) Proj_orthog_ccspan_insert insertCI is_ortho_set_def plus_cblinfun.rep_eq sum.insert)
        also have \<open>\<dots> \<le> (norm (Proj (ccspan M)) * norm e)\<^sup>2\<close>
          by (auto simp: norm_cblinfun intro!: power_mono)
        also have \<open>\<dots> \<le> (norm e)\<^sup>2\<close>
          apply (rule power_mono)
           apply (metis norm_Proj_leq1 mult_left_le_one_le norm_ge_zero)
          by simp
        finally show ?thesis
          by -
      qed
      then have \<open>(\<lambda>f. (cmod (cinner f e))\<^sup>2) abs_summable_on F\<close>
        apply (intro nonneg_bdd_above_summable_on bdd_aboveI)
        by auto
      then have \<open>countable {x \<in> F. (cmod (x \<bullet>\<^sub>C e))\<^sup>2 \<noteq> 0}\<close>
        by (rule abs_summable_countable)
      then show ?thesis
        unfolding F'_def
        by (smt (verit, ccfv_SIG) Collect_cong norm_eq_zero power_not_zero zero_power2)
    qed
    then have F'_leq: \<open>|F' e| \<le>o natLeq\<close> for e
      using countable_leq_natLeq by auto

    from F'_union have \<open>|F| \<le>o |Sigma E F'|\<close> (is \<open>_ \<le>o \<dots>\<close>)
      using card_of_UNION_Sigma by blast
    also have \<open>\<dots> \<le>o |E \<times> (UNIV::nat set)|\<close> (is \<open>_ \<le>o \<dots>\<close>)
      apply (rule card_of_Sigma_mono1)
      using F'_leq
      using card_of_nat ordIso_symmetric ordLeq_ordIso_trans by blast
    also have \<open>\<dots> =o |E| *c natLeq\<close> (is \<open>_ =o \<dots>\<close>)
      by (metis Field_card_of Field_natLeq card_of_ordIso_subst cprod_def)
    also have \<open>\<dots> =o |E|\<close>
      apply (rule card_prod_omega)
      using that by (simp add: cinfinite_def)
    finally show \<open>|F| \<le>o |E|\<close>
      by -
  qed
  then have infinite: \<open>|E| =o |F|\<close> if \<open>infinite E\<close> and \<open>infinite F\<close>
    by (simp add: assms(1) assms(2) ordIso_iff_ordLeq that(1) that(2))

  have \<open>|E| =o |F|\<close> if \<open>finite E\<close> and \<open>is_onb E\<close> and \<open>is_onb F\<close> for E F :: \<open>'a set\<close>
  proof -
    have \<open>card E = card F\<close>
      using that 
      by (metis bij_betw_same_card ccspan.rep_eq closure_finite_cspan complex_vector.bij_if_span_eq_span_bases 
          complex_vector.independent_span_bound is_onb_def is_ortho_set_cindependent top_ccsubspace.rep_eq top_greatest)
    with \<open>finite E\<close> have \<open>finite F\<close>
      by (metis ccspan.rep_eq closure_finite_cspan complex_vector.independent_span_bound is_onb_def is_ortho_set_cindependent that(2) that(3) top_ccsubspace.rep_eq top_greatest)
    with \<open>card E = card F\<close> that show ?thesis
      apply (rule_tac finite_card_of_iff_card[THEN iffD2])
      by auto
  qed

  with infinite assms have \<open>|E| =o |F|\<close>
    by (meson ordIso_symmetric)

  then show ?thesis
    by (simp add: card_of_ordIso)
qed


definition bij_between_bases where \<open>bij_between_bases E F = (SOME f. bij_betw f E F)\<close> for E F :: \<open>'a::chilbert_space set\<close>

lemma
  fixes E F :: \<open>'a::chilbert_space set\<close>
  assumes \<open>is_onb E\<close> \<open>is_onb F\<close>
  shows bij_between_bases_bij: \<open>bij_betw (bij_between_bases E F) E F\<close>
  using all_onbs_same_card
  by (metis assms(1) assms(2) bij_between_bases_def someI)

definition unitary_between where \<open>unitary_between E F = cblinfun_extension E (bij_between_bases E F)\<close>

lemma unitary_between_apply:
  fixes E F :: \<open>'a::chilbert_space set\<close>
  assumes \<open>is_onb E\<close> \<open>is_onb F\<close> \<open>e \<in> E\<close>
  shows \<open>unitary_between E F *\<^sub>V e = bij_between_bases E F e\<close>
proof -
  from \<open>is_onb E\<close> \<open>is_onb F\<close>
  have EF: \<open>bij_between_bases E F e \<in> F\<close> if \<open>e \<in> E\<close> for e
    by (meson bij_betwE bij_between_bases_bij that)
  have ortho: \<open>is_orthogonal (bij_between_bases E F x) (bij_between_bases E F y)\<close> if \<open>x \<noteq> y\<close> and \<open>x \<in> E\<close> and \<open>y \<in> E\<close> for x y
    by (smt (verit, del_insts) assms(1) assms(2) bij_betw_iff_bijections bij_between_bases_bij is_onb_def is_ortho_set_def that(1) that(2) that(3))
  have spanE: \<open>closure (cspan E) = UNIV\<close>
    by (metis assms(1) ccspan.rep_eq is_onb_def top_ccsubspace.rep_eq)
  show ?thesis
    unfolding unitary_between_def
    apply (rule cblinfun_extension_apply)
     apply (rule cblinfun_extension_exists_ortho[where B=1])
    using assms EF ortho spanE
    by (auto simp: is_onb_def)
qed


lemma unitary_between_unitary:
  fixes E F :: \<open>'a::chilbert_space set\<close>
  assumes \<open>is_onb E\<close> \<open>is_onb F\<close>
  shows \<open>unitary (unitary_between E F)\<close>
proof -
  have \<open>(unitary_between E F *\<^sub>V b) \<bullet>\<^sub>C (unitary_between E F *\<^sub>V c) = b \<bullet>\<^sub>C c\<close> if \<open>b \<in> E\<close> and \<open>c \<in> E\<close> for b c
  proof (cases \<open>b = c\<close>)
    case True
    from \<open>is_onb E\<close> that have 1: \<open>b \<bullet>\<^sub>C b = 1\<close>
      using cnorm_eq_1 is_onb_def by blast
    from that have \<open>unitary_between E F *\<^sub>V b \<in> F\<close>
      by (metis assms(1) assms(2) bij_betw_apply bij_between_bases_bij unitary_between_apply)
    with \<open>is_onb F\<close> have 2: \<open>(unitary_between E F *\<^sub>V b) \<bullet>\<^sub>C (unitary_between E F *\<^sub>V b) = 1\<close>
      by (simp add: cnorm_eq_1 is_onb_def)
    from 1 2 True show ?thesis
      by simp
  next
    case False
    from \<open>is_onb E\<close> that have 1: \<open>b \<bullet>\<^sub>C c = 0\<close>
      by (simp add: False is_onb_def is_ortho_set_def)
    from that have inF: \<open>unitary_between E F *\<^sub>V b \<in> F\<close> \<open>unitary_between E F *\<^sub>V c \<in> F\<close>
      by (metis assms(1) assms(2) bij_betw_apply bij_between_bases_bij unitary_between_apply)+
    have neq: \<open>unitary_between E F *\<^sub>V b \<noteq> unitary_between E F *\<^sub>V c\<close>
      by (metis (no_types, lifting) False assms(1) assms(2) bij_betw_iff_bijections bij_between_bases_bij that(1) that(2) unitary_between_apply)
    from inF neq \<open>is_onb F\<close> have 2: \<open>(unitary_between E F *\<^sub>V b) \<bullet>\<^sub>C (unitary_between E F *\<^sub>V c) = 0\<close>
      by (simp add: is_onb_def is_ortho_set_def)
    from 1 2 show ?thesis
      by simp
  qed
  then have iso: \<open>isometry (unitary_between E F)\<close>
    apply (rule_tac orthogonal_on_basis_is_isometry[where B=E])
    using assms(1) is_onb_def by auto
  have \<open>unitary_between E F *\<^sub>S \<top> = unitary_between E F *\<^sub>S ccspan E\<close>
    by (metis assms(1) is_onb_def)
  also have \<open>\<dots> \<ge> ccspan (unitary_between E F ` E)\<close> (is \<open>_ \<ge> \<dots>\<close>)
    by (simp add: cblinfun_image_ccspan)
  also have \<open>\<dots> = ccspan (bij_between_bases E F ` E)\<close>
    by (metis assms(1) assms(2) image_cong unitary_between_apply)
  also have \<open>\<dots> = ccspan F\<close>
    by (metis assms(1) assms(2) bij_betw_imp_surj_on bij_between_bases_bij)
  also have \<open>\<dots> = \<top>\<close>
    using assms(2) is_onb_def by blast
  finally have surj: \<open>unitary_between E F *\<^sub>S \<top> = \<top>\<close>
    by (simp add: top.extremum_unique)
  from iso surj show ?thesis
    by (rule surj_isometry_is_unitary)
qed

lemma is_onb_ket[simp]: \<open>is_onb (range ket)\<close>
  by (auto simp: is_onb_def)

lemma isometry_preserves_norm: \<open>isometry U \<Longrightarrow> norm (U *\<^sub>V \<psi>) = norm \<psi>\<close>
  by (metis (no_types, lifting) cblinfun_apply_cblinfun_compose cblinfun_id_cblinfun_apply cinner_adj_right cnorm_eq isometryD)

lemma parseval_infsum_aux1: 
  fixes h :: \<open>'a ell2\<close>
  assumes \<open>is_onb E\<close>
  shows \<open>(\<Sum>\<^sub>\<infinity>e\<in>E. (cmod (h \<bullet>\<^sub>C e))\<^sup>2) = (norm h)\<^sup>2\<close>
proof -
  define U h' where \<open>U = unitary_between (range ket) E\<close> and \<open>h' = U* *\<^sub>V h\<close>
  have [simp]: \<open>unitary U\<close>
    using U_def assms is_onb_ket unitary_between_unitary by blast
  have \<open>(\<Sum>\<^sub>\<infinity>e\<in>E. (cmod (h \<bullet>\<^sub>C e))\<^sup>2) = (\<Sum>\<^sub>\<infinity>k\<in>range ket. (cmod (h \<bullet>\<^sub>C bij_between_bases (range ket) E k))\<^sup>2)\<close>
    apply (rule infsum_reindex_bij_betw[symmetric])
    using assms bij_between_bases_bij is_onb_ket by blast
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>i. (cmod (h \<bullet>\<^sub>C bij_between_bases (range ket) E (ket i)))\<^sup>2)\<close>
    apply (subst infsum_reindex)
    by (auto simp: o_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>i. (cmod (h \<bullet>\<^sub>C U (ket i)))\<^sup>2)\<close>
    by (simp add: U_def assms unitary_between_apply)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>i. (cmod (h' \<bullet>\<^sub>C ket i))\<^sup>2)\<close>
    by (simp add: cinner_adj_left h'_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>i. (cmod (Rep_ell2 h' i))\<^sup>2)\<close>
    by (simp add: cinner_ket_right)
  also have \<open>\<dots> = (norm h')\<^sup>2\<close>
    by (simp add: ell2_norm_square norm_ell2.rep_eq)
  also have \<open>\<dots> = (norm h)\<^sup>2\<close>
    by (simp add: h'_def isometry_preserves_norm)
  finally show ?thesis
    by -
qed

definition \<open>cr_chilbert2ell2_ell2 x y \<longleftrightarrow> ell2_to_hilbert *\<^sub>V x = y\<close>


lemma bi_unique_cr_chilbert2ell2_ell2[transfer_rule]: \<open>bi_unique cr_chilbert2ell2_ell2\<close>
  by (metis (no_types, opaque_lifting) bi_unique_def cblinfun_apply_cblinfun_compose cr_chilbert2ell2_ell2_def id_cblinfun_apply unitaryD1 unitary_ell2_to_hilbert)
lemma bi_total_cr_chilbert2ell2_ell2[transfer_rule]: \<open>bi_total cr_chilbert2ell2_ell2\<close>
  by (metis (no_types, opaque_lifting) bi_total_def cblinfun_apply_cblinfun_compose cr_chilbert2ell2_ell2_def id_cblinfun_apply unitaryD2 unitary_ell2_to_hilbert)

named_theorems c2l2l2

lemma c2l2l2_cinner[c2l2l2]: 
  includes lifting_syntax
  shows \<open>(cr_chilbert2ell2_ell2 ===> cr_chilbert2ell2_ell2 ===> (=)) cinner cinner\<close>
proof -
  have *: \<open>ket x \<bullet>\<^sub>C ket y = (ell2_to_hilbert *\<^sub>V ket x) \<bullet>\<^sub>C (ell2_to_hilbert *\<^sub>V ket y)\<close> for x y :: \<open>'a chilbert2ell2\<close>
    by (metis Rep_chilbert2ell2 Rep_chilbert2ell2_inverse cinner_adj_right ell2_to_hilbert_adj_ket ell2_to_hilbert_ket)
  have \<open>x \<bullet>\<^sub>C y = (ell2_to_hilbert *\<^sub>V x) \<bullet>\<^sub>C (ell2_to_hilbert *\<^sub>V y) \<close> for x y :: \<open>'a chilbert2ell2 ell2\<close>
    apply (rule fun_cong[where x=x])
    apply (rule bounded_antilinear_equal_ket)
      apply (intro bounded_linear_intros)
     apply (intro bounded_linear_intros)
    apply (rule fun_cong[where x=y])
    apply (rule bounded_clinear_equal_ket)
      apply (intro bounded_linear_intros)
     apply (intro bounded_linear_intros)
    by (simp add: *)
  then show ?thesis
    by (auto intro!: rel_funI simp: cr_chilbert2ell2_ell2_def)
qed

lemma c2l2l2_norm[c2l2l2]: 
  includes lifting_syntax
  shows \<open>(cr_chilbert2ell2_ell2 ===> (=)) norm norm\<close>
  apply (subst norm_eq_sqrt_cinner[abs_def])
  apply (subst (2) norm_eq_sqrt_cinner[abs_def])
  using c2l2l2_cinner[transfer_rule] apply fail?
  by transfer_prover

lemma c2l2l2_scaleC[c2l2l2]:
  includes lifting_syntax
  shows \<open>((=) ===> cr_chilbert2ell2_ell2 ===> cr_chilbert2ell2_ell2) scaleC scaleC\<close>
proof -
  have \<open>ell2_to_hilbert *\<^sub>V c *\<^sub>C x = c *\<^sub>C (ell2_to_hilbert *\<^sub>V x)\<close> for c and x :: \<open>'a chilbert2ell2 ell2\<close>
    by (simp add: cblinfun.scaleC_right)
  then show ?thesis
    by (auto intro!: rel_funI simp: cr_chilbert2ell2_ell2_def)
qed

lemma infsum_transfer[transfer_rule]: 
  includes lifting_syntax
  assumes \<open>bi_unique R\<close>
  shows \<open>((R ===> (=)) ===> (rel_set R) ===> (=)) infsum infsum\<close>
proof (intro rel_funI, rename_tac f g A B)
  fix f :: \<open>'a \<Rightarrow> 'c\<close> and g :: \<open>'b \<Rightarrow> 'c\<close> and A B
  assume \<open>rel_set R A B\<close>
  with \<open>bi_unique R\<close>
  obtain m where \<open>B = m ` A\<close> and \<open>inj_on m A\<close> and Rm: \<open>\<forall>x\<in>A. R x (m x)\<close>
    apply (rule bi_unique_rel_set_lemma)
    by auto
  then have bij_m: \<open>bij_betw m A B\<close>
    by (simp add: inj_on_imp_bij_betw)

  assume \<open>(R ===> (=)) f g\<close>
  then have \<open>f x = g y\<close> if \<open>R x y\<close> for x y
    thm rel_funD
    using that by (rule rel_funD)
  with Rm have fg: \<open>f x = g (m x)\<close> if \<open>x\<in>A\<close> for x
    using that by blast

  show \<open>infsum f A = infsum g B\<close>
    apply (subst infsum_reindex_bij_betw[OF bij_m, symmetric])
    apply (rule infsum_cong)
    using fg by simp
qed

lemma summable_on_transfer[transfer_rule]: 
  includes lifting_syntax
  assumes \<open>bi_unique R\<close>
  shows \<open>((R ===> (=)) ===> (rel_set R) ===> (=)) Infinite_Sum.summable_on Infinite_Sum.summable_on\<close>
proof (intro rel_funI, rename_tac f g A B)
  fix f :: \<open>'a \<Rightarrow> 'c\<close> and g :: \<open>'b \<Rightarrow> 'c\<close> and A B
  assume \<open>rel_set R A B\<close>
  with \<open>bi_unique R\<close>
  obtain m where \<open>B = m ` A\<close> and \<open>inj_on m A\<close> and Rm: \<open>\<forall>x\<in>A. R x (m x)\<close>
    apply (rule bi_unique_rel_set_lemma)
    by auto
  then have bij_m: \<open>bij_betw m A B\<close>
    by (simp add: inj_on_imp_bij_betw)

  assume \<open>(R ===> (=)) f g\<close>
  then have \<open>f x = g y\<close> if \<open>R x y\<close> for x y
    thm rel_funD
    using that by (rule rel_funD)
  with Rm have fg: \<open>f x = g (m x)\<close> if \<open>x\<in>A\<close> for x
    using that by blast

  show \<open>(f summable_on A) = (g summable_on B)\<close>
    apply (subst summable_on_reindex_bij_betw[OF bij_m, symmetric])
    apply (rule summable_on_cong)
    using fg by simp
qed

(* lemma c2l2l2_infsum'[c2l2l2]:
  includes lifting_syntax
  shows \<open>((R ===> cr_chilbert2ell2_ell2) ===> (rel_set R) ===> cr_chilbert2ell2_ell2) infsum infsum\<close>
  by - *)

lemma c2l2l2_zero[c2l2l2]: 
  includes lifting_syntax
  shows \<open>cr_chilbert2ell2_ell2 0 0\<close>
  unfolding cr_chilbert2ell2_ell2_def by simp

lemma c2l2l2_is_ortho_set[c2l2l2]: 
  includes lifting_syntax
  shows \<open>(rel_set cr_chilbert2ell2_ell2 ===> (=)) is_ortho_set (is_ortho_set :: 'a::{chilbert_space,not_singleton} set \<Rightarrow> bool)\<close>
  unfolding is_ortho_set_def
  using c2l2l2[where 'a='a, transfer_rule] apply fail?
  by transfer_prover

definition \<open>rel_ccsubspace R x y = rel_set R (space_as_set x) (space_as_set y)\<close>


lemma space_as_set_image_commute:
  assumes UV: \<open>U o\<^sub>C\<^sub>L V = id_cblinfun\<close> and VU: \<open>V o\<^sub>C\<^sub>L U = id_cblinfun\<close> (* TODO: I think only one of them is needed *)
  shows \<open>(*\<^sub>V) U ` space_as_set T = space_as_set (U *\<^sub>S T)\<close>
proof -
  have \<open>space_as_set (U *\<^sub>S T) = U ` V ` space_as_set (U *\<^sub>S T)\<close>
    by (simp add: image_image UV flip: cblinfun_apply_cblinfun_compose)
  also have \<open>\<dots> \<subseteq> U ` space_as_set (V *\<^sub>S U *\<^sub>S T)\<close>
    by (metis cblinfun_image.rep_eq closure_subset image_mono)
  also have \<open>\<dots> = U ` space_as_set T\<close>
    by (simp add: VU cblinfun_assoc_left(2))
  finally have 1: \<open>space_as_set (U *\<^sub>S T) \<subseteq> U ` space_as_set T\<close>
    by -
  have 2: \<open>U ` space_as_set T \<subseteq> space_as_set (U *\<^sub>S T)\<close>
    by (simp add: cblinfun_image.rep_eq closure_subset)
  from 1 2 show ?thesis
    by simp
qed

lemma c2l2l2_ccspan[c2l2l2]:
  includes lifting_syntax
  shows \<open>(rel_set cr_chilbert2ell2_ell2 ===> rel_ccsubspace cr_chilbert2ell2_ell2) ccspan ccspan\<close>
proof (rule rel_funI, rename_tac A B)
  fix A and B :: \<open>'a set\<close>
  assume \<open>rel_set cr_chilbert2ell2_ell2 A B\<close>
  then have \<open>B = ell2_to_hilbert ` A\<close>
    by (metis (no_types, lifting) bi_unique_cr_chilbert2ell2_ell2 bi_unique_rel_set_lemma cr_chilbert2ell2_ell2_def image_cong)
  then have \<open>space_as_set (ccspan B) = ell2_to_hilbert ` space_as_set (ccspan A)\<close>
    apply (subst space_as_set_image_commute[where V=\<open>ell2_to_hilbert*\<close>])
    by (auto intro: unitaryD2 simp: cblinfun_image_ccspan unitary_ell2_to_hilbert)
  then have \<open>rel_set cr_chilbert2ell2_ell2 (space_as_set (ccspan A)) (space_as_set (ccspan B))\<close>
    by (smt (verit, best) cr_chilbert2ell2_ell2_def image_iff rel_setI)
  then show \<open>rel_ccsubspace cr_chilbert2ell2_ell2 (ccspan A) (ccspan B)\<close>
    by (simp add: rel_ccsubspace_def)
qed

lemma left_unique_rel_ccsubspace[transfer_rule]: \<open>left_unique (rel_ccsubspace R)\<close> if \<open>left_unique R\<close>
proof (rule left_uniqueI)
  fix S T :: \<open>'a ccsubspace\<close> and U
  assume assms: \<open>rel_ccsubspace R S U\<close> \<open>rel_ccsubspace R T U\<close>
  have \<open>space_as_set S = space_as_set T\<close>
    apply (rule left_uniqueD)
      using that apply (rule left_unique_rel_set)
    using assms unfolding rel_ccsubspace_def by auto
  then show \<open>S = T\<close>
    by (simp add: space_as_set_inject)
qed

lemma right_unique_rel_ccsubspace[transfer_rule]: \<open>right_unique (rel_ccsubspace R)\<close> if \<open>right_unique R\<close>
  by (metis rel_ccsubspace_def right_unique_def right_unique_rel_set space_as_set_inject that)

lemma bi_unique_rel_ccsubspace[transfer_rule]: \<open>bi_unique (rel_ccsubspace R)\<close> if \<open>bi_unique R\<close>
  by (metis (no_types, lifting) bi_unique_def bi_unique_rel_set rel_ccsubspace_def space_as_set_inject that)

lemma right_total_rel_ccsubspace:
  fixes R :: \<open>'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector \<Rightarrow> bool\<close>
  assumes UV: \<open>U o\<^sub>C\<^sub>L V = id_cblinfun\<close>
  assumes VU: \<open>V o\<^sub>C\<^sub>L U = id_cblinfun\<close>
  assumes R_def: \<open>\<And>x y. R x y \<longleftrightarrow> x = U *\<^sub>V y\<close>
  shows \<open>right_total (rel_ccsubspace R)\<close>
proof (rule right_totalI)
  fix T :: \<open>'b ccsubspace\<close>
  show \<open>\<exists>S. rel_ccsubspace R S T\<close>
    apply (rule exI[of _ \<open>U *\<^sub>S T\<close>])
    using UV VU by (auto simp add: rel_ccsubspace_def R_def rel_set_def simp flip: space_as_set_image_commute)
qed

lemma converse_rel_ccsubspace: \<open>conversep (rel_ccsubspace R) = rel_ccsubspace (conversep R)\<close>
  by (auto simp: rel_ccsubspace_def[abs_def])

lemma left_total_rel_ccsubspace:
  fixes R :: \<open>'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector \<Rightarrow> bool\<close>
  assumes UV: \<open>U o\<^sub>C\<^sub>L V = id_cblinfun\<close>
  assumes VU: \<open>V o\<^sub>C\<^sub>L U = id_cblinfun\<close>
  assumes R_def: \<open>\<And>x y. R x y \<longleftrightarrow> y = U *\<^sub>V x\<close>
  shows \<open>left_total (rel_ccsubspace R)\<close>
proof -
  have \<open>right_total (rel_ccsubspace (conversep R))\<close>
    apply (rule right_total_rel_ccsubspace)
    using assms by auto
  then show ?thesis
    by (auto intro!: right_total_conversep[THEN iffD1] simp: converse_rel_ccsubspace)
qed

lemma [transfer_rule]: \<open>bi_total (rel_ccsubspace cr_chilbert2ell2_ell2)\<close>
  apply (rule bi_totalI)
   apply (rule left_total_rel_ccsubspace[where U=ell2_to_hilbert and V=\<open>ell2_to_hilbert*\<close>])
     apply (auto simp: unitary_ell2_to_hilbert cr_chilbert2ell2_ell2_def)[3]
   apply (rule right_total_rel_ccsubspace[where U=\<open>ell2_to_hilbert*\<close> and V=\<open>ell2_to_hilbert\<close>])
     apply (auto simp: unitary_ell2_to_hilbert cr_chilbert2ell2_ell2_def)[3]
  by (metis cblinfun_apply_cblinfun_compose cblinfun_id_cblinfun_apply unitary_def unitary_ell2_to_hilbert)+

lemma [simp]: \<open>space_as_set \<top> = UNIV\<close>
  by (rule top_ccsubspace.rep_eq)

lemma c2l2l2_top[c2l2l2]:
  includes lifting_syntax
  shows \<open>(rel_ccsubspace cr_chilbert2ell2_ell2) top top\<close>
  unfolding rel_ccsubspace_def apply auto
  by (simp add: UNIV_transfer bi_total_cr_chilbert2ell2_ell2)

lemma c2l2l2_is_onb[c2l2l2]: 
  includes lifting_syntax
  shows \<open>(rel_set cr_chilbert2ell2_ell2 ===> (=)) is_onb is_onb\<close>
  unfolding is_onb_def
  using c2l2l2[where 'a='a, transfer_rule] apply fail?
  by transfer_prover

lemma
  fixes h :: \<open>'b::{chilbert_space,not_singleton}\<close>
  assumes \<open>is_onb E\<close>
  shows parseval_infsum_aux2: \<open>(\<Sum>\<^sub>\<infinity>e\<in>E. (cmod (h \<bullet>\<^sub>C e))\<^sup>2) = (norm h)\<^sup>2\<close>
  using c2l2l2[where 'a = 'b, transfer_rule] apply fail?
  using assms apply transfer
  by (rule parseval_infsum_aux1)

lemma 
  fixes h :: \<open>'b::{chilbert_space, CARD_1}\<close>
  assumes \<open>is_onb E\<close>
  shows parseval_infsum_aux3: \<open>(\<Sum>\<^sub>\<infinity>e\<in>E. (cmod (h \<bullet>\<^sub>C e))\<^sup>2) = (norm h)\<^sup>2\<close>
  apply (subst everything_the_same[where y=0])
  by simp

lemma 
  fixes h :: \<open>'a::{chilbert_space}\<close>
  assumes \<open>is_onb E\<close>
  shows parseval_infsum: \<open>(\<Sum>\<^sub>\<infinity>e\<in>E. (cmod (h \<bullet>\<^sub>C e))\<^sup>2) = (norm h)\<^sup>2\<close>
  apply (cases \<open>class.not_singleton TYPE('a)\<close>)
   apply (rule parseval_infsum_aux2[internalize_sort \<open>'b :: {chilbert_space,not_singleton}\<close>])
     apply (auto intro!: assms chilbert_space_axioms)[3]
   apply (rule parseval_infsum_aux3[internalize_sort \<open>'b :: {chilbert_space,CARD_1}\<close>])
  by (auto intro!: assms chilbert_space_axioms not_singleton_vs_CARD_1)

lemma 
  fixes h :: \<open>'a::{chilbert_space}\<close>
  assumes \<open>is_onb E\<close>
  shows parseval_abs_summable: \<open>(\<lambda>e. (cmod (h \<bullet>\<^sub>C e))\<^sup>2) abs_summable_on E\<close>
proof (cases \<open>h = 0\<close>)
  case True
  then show ?thesis by simp
next
  case False
  then have \<open>(\<Sum>\<^sub>\<infinity>e\<in>E. (cmod (h \<bullet>\<^sub>C e))\<^sup>2) \<noteq> 0\<close>
    by (simp add: assms parseval_infsum)
  then show ?thesis
    using infsum_not_exists by auto
qed

(* TODO: conway, op, 18.1 Proposition (part) *)
lemma TODO_name1:
  fixes E :: \<open>'a::complex_inner set\<close> and F :: \<open>'b::chilbert_space set\<close>
  assumes \<open>is_onb E\<close> and \<open>is_onb F\<close>
  shows \<open>has_sum (\<lambda>e. (norm (A *\<^sub>V e))\<^sup>2) E t \<longleftrightarrow> has_sum (\<lambda>(e,f). (cmod ((A *\<^sub>V e) \<bullet>\<^sub>C f))\<^sup>2) (E\<times>F) t\<close>
proof
  assume asm: \<open>has_sum (\<lambda>e. (norm (A *\<^sub>V e))\<^sup>2) E t\<close>
  have sum1: \<open>t = (\<Sum>\<^sub>\<infinity>e\<in>E. (norm (A *\<^sub>V e))\<^sup>2)\<close>
    using asm infsumI by blast
  have abs1: \<open>(\<lambda>e. (norm (A *\<^sub>V e))\<^sup>2) abs_summable_on E\<close>
    using asm summable_on_def by auto
  have sum2: \<open>t = (\<Sum>\<^sub>\<infinity>e\<in>E. \<Sum>\<^sub>\<infinity>f\<in>F. (cmod ((A *\<^sub>V e) \<bullet>\<^sub>C f))\<^sup>2)\<close>
    apply (subst sum1)
    apply (rule infsum_cong)
    using assms(2) by (rule parseval_infsum[symmetric])
  have abs2: \<open>(\<lambda>e. \<Sum>\<^sub>\<infinity>f\<in>F. (cmod ((A *\<^sub>V e) \<bullet>\<^sub>C f))\<^sup>2) abs_summable_on E\<close>
    using _ abs1 apply (rule summable_on_cong[THEN iffD2])
    apply (subst parseval_infsum)
    using assms(2) by auto
  have abs3: \<open>(\<lambda>(x, y). (cmod ((A *\<^sub>V x) \<bullet>\<^sub>C y))\<^sup>2) abs_summable_on E \<times> F\<close>
    apply (rule abs_summable_on_Sigma_iff[THEN iffD2], rule conjI)
    using abs2 apply (auto simp del: real_norm_def)
    using assms(2) parseval_abs_summable apply blast
    by auto
  have sum3: \<open>t = (\<Sum>\<^sub>\<infinity>(e,f)\<in>E\<times>F. (cmod ((A *\<^sub>V e) \<bullet>\<^sub>C f))\<^sup>2)\<close>
    apply (subst sum2)
    apply (subst infsum_Sigma'_banach[symmetric])
    using abs3 abs_summable_summable apply blast
    by auto
  then show \<open>has_sum (\<lambda>(e,f). (cmod ((A *\<^sub>V e) \<bullet>\<^sub>C f))\<^sup>2) (E\<times>F) t\<close>
    using abs3 abs_summable_summable has_sum_infsum by blast
next
  assume asm: \<open>has_sum (\<lambda>(e,f). (cmod ((A *\<^sub>V e) \<bullet>\<^sub>C f))\<^sup>2) (E\<times>F) t\<close>
  have abs3: \<open>(\<lambda>(x, y). (cmod ((A *\<^sub>V x) \<bullet>\<^sub>C y))\<^sup>2) abs_summable_on E \<times> F\<close>
    using asm summable_on_def summable_on_iff_abs_summable_on_real by blast
  have sum3: \<open>t = (\<Sum>\<^sub>\<infinity>(e,f)\<in>E\<times>F. (cmod ((A *\<^sub>V e) \<bullet>\<^sub>C f))\<^sup>2)\<close>
    using asm infsumI by blast
  have sum2: \<open>t = (\<Sum>\<^sub>\<infinity>e\<in>E. \<Sum>\<^sub>\<infinity>f\<in>F. (cmod ((A *\<^sub>V e) \<bullet>\<^sub>C f))\<^sup>2)\<close>
    by (metis (mono_tags, lifting) asm infsum_Sigma'_banach infsum_cong sum3 summable_iff_has_sum_infsum)
  have abs2: \<open>(\<lambda>e. \<Sum>\<^sub>\<infinity>f\<in>F. (cmod ((A *\<^sub>V e) \<bullet>\<^sub>C f))\<^sup>2) abs_summable_on E\<close>
    by (smt (verit, del_insts) abs3 summable_on_Sigma_banach summable_on_cong summable_on_iff_abs_summable_on_real)
  have sum1: \<open>t = (\<Sum>\<^sub>\<infinity>e\<in>E. (norm (A *\<^sub>V e))\<^sup>2)\<close>
    apply (subst sum2)
    apply (rule infsum_cong)
    using assms(2) parseval_infsum by blast
  have abs1: \<open>(\<lambda>e. (norm (A *\<^sub>V e))\<^sup>2) abs_summable_on E\<close>
    using abs2 assms(2) parseval_infsum by fastforce
  show \<open>has_sum (\<lambda>e. (norm (A *\<^sub>V e))\<^sup>2) E t\<close>
    using abs1 sum1 by auto
qed

(* TODO: conway, op, 18.1 Proposition (2nd part) *)
lemma TODO_name2:
  fixes E :: \<open>'a::chilbert_space set\<close> and F :: \<open>'b::chilbert_space set\<close>
  assumes \<open>is_onb E\<close> and \<open>is_onb F\<close>
  shows \<open>has_sum (\<lambda>e. (norm (A *\<^sub>V e))\<^sup>2) E t \<longleftrightarrow> has_sum (\<lambda>f. (norm (A* *\<^sub>V f))\<^sup>2) F t\<close>
proof -
  have \<open>has_sum (\<lambda>e. (norm (A *\<^sub>V e))\<^sup>2) E t \<longleftrightarrow> has_sum (\<lambda>(e,f). (cmod ((A *\<^sub>V e) \<bullet>\<^sub>C f))\<^sup>2) (E\<times>F) t\<close>
    using TODO_name1 assms by blast
  also have \<open>\<dots> \<longleftrightarrow> has_sum (\<lambda>(e,f). (cmod ((A* *\<^sub>V f) \<bullet>\<^sub>C e))\<^sup>2) (E\<times>F) t\<close>
    apply (subst cinner_adj_left) apply (subst cinner_commute)
    apply (subst complex_mod_cnj) by rule
  also have \<open>\<dots> \<longleftrightarrow> has_sum (\<lambda>(f,e). (cmod ((A* *\<^sub>V f) \<bullet>\<^sub>C e))\<^sup>2) (F\<times>E) t\<close>
    apply (subst asm_rl[of \<open>F\<times>E = prod.swap ` (E\<times>F)\<close>])
     apply force
    apply (subst has_sum_reindex)
    by (auto simp: o_def)
  also have \<open>\<dots> \<longleftrightarrow> has_sum (\<lambda>f. (norm (A* *\<^sub>V f))\<^sup>2) F t\<close>
    using TODO_name1 assms by blast
  finally show ?thesis
    by -
qed

definition sqrt_op :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a) \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'a)\<close> where \<open>sqrt_op a = (SOME b. b \<ge> 0 \<and> b* o\<^sub>C\<^sub>L b = a)\<close>

lemma 
  assumes \<open>a \<ge> 0\<close>
  shows sqrt_op_pos[simp]: \<open>sqrt_op a \<ge> 0\<close> and sqrt_op_square[simp]: \<open>(sqrt_op a)* o\<^sub>C\<^sub>L sqrt_op a = a\<close>
proof -
  have *: \<open>\<exists>b. b \<ge> 0 \<and> b* o\<^sub>C\<^sub>L b = a\<close>
(* For an elementary proof (w/o functional calculus, see maybe
https://www.jstor.org/stable/2028176?seq=1#metadata_info_tab_contents or references [2,3] therein.
[2]: https://libgen.rocks/ads.php?md5=c66b6b15b434e145a5adf92ba3900144&downloadname=10.1007/bf01448052 -- short proof = https://link.springer.com/article/10.1007%2FBF01448052:-)
[3]: https://libgen.rocks/ads.php?md5=0b8573c90cf9d9a0e51b0746bcb22452 -- Didn't find elementary proof *)
    sorry
  show \<open>sqrt_op a \<ge>0\<close> and \<open>(sqrt_op a)* o\<^sub>C\<^sub>L sqrt_op a = a\<close>
    using * apply (smt (verit, ccfv_threshold) someI_ex sqrt_op_def)
    using * by (metis (mono_tags, lifting) someI_ex sqrt_op_def)
qed

(* Also in the "elementary proof" mentioned in sqrt_op_pos *)
lemma sqrt_op_unique:
  assumes \<open>b \<ge> 0\<close> and \<open>b* o\<^sub>C\<^sub>L b = a\<close>
  shows \<open>b = sqrt_op a\<close>
  sorry

lemma sqrt_op_0[simp]: \<open>sqrt_op 0 = 0\<close>
  apply (rule sqrt_op_unique[symmetric])
  by auto

definition abs_op :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_inner \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> where \<open>abs_op a = sqrt_op (a* o\<^sub>C\<^sub>L a)\<close>

lemma abs_op_pos[simp]: \<open>abs_op a \<ge> 0\<close>
  by (simp add: abs_op_def positive_cblinfun_squareI sqrt_op_pos)

lemma abs_op_0[simp]: \<open>abs_op 0 = 0\<close>
  unfolding abs_op_def by auto

lemma abs_op_idem[simp]: \<open>abs_op (abs_op a) = abs_op a\<close>
  by (metis abs_op_def abs_op_pos sqrt_op_unique)

lemma abs_op_uminus[simp]: \<open>abs_op (- a) = abs_op a\<close>
  by (simp add: abs_op_def adj_uminus bounded_cbilinear.minus_left 
      bounded_cbilinear.minus_right bounded_cbilinear_cblinfun_compose)

lemma cblinfun_compose_uminus_left: \<open>(- a) o\<^sub>C\<^sub>L b = - (a o\<^sub>C\<^sub>L b)\<close>
  by (simp add: bounded_cbilinear.minus_left bounded_cbilinear_cblinfun_compose)

lemma cblinfun_compose_uminus_right: \<open>a o\<^sub>C\<^sub>L (- b) = - (a o\<^sub>C\<^sub>L b)\<close>
  by (simp add: bounded_cbilinear.minus_right bounded_cbilinear_cblinfun_compose)

(* TODO: conway op, 18.2 Corollary *)
lemma trace_norm_basis_invariance:
  assumes \<open>is_onb E\<close> and \<open>is_onb F\<close>
  shows \<open>has_sum (\<lambda>e. cmod ((abs_op A *\<^sub>V e) \<bullet>\<^sub>C e)) E t \<longleftrightarrow> has_sum (\<lambda>f. cmod ((abs_op A *\<^sub>V f) \<bullet>\<^sub>C f)) F t\<close>
proof -
  define B where \<open>B = sqrt_op (abs_op A)\<close>
  have \<open>complex_of_real (cmod ((abs_op A *\<^sub>V e) \<bullet>\<^sub>C e)) = (B* *\<^sub>V B*\<^sub>V e) \<bullet>\<^sub>C e\<close> for e
    apply (simp add: B_def flip: cblinfun_apply_cblinfun_compose)
    by (metis (no_types, lifting) abs_op_pos cblinfun.zero_left cinner_commute cinner_zero_right complex_cnj_complex_of_real complex_of_real_cmod less_eq_cblinfun_def)
  also have \<open>\<dots> e = complex_of_real ((norm (B *\<^sub>V e))\<^sup>2)\<close> for e
    apply (subst cdot_square_norm[symmetric])
    apply (subst cinner_adj_left[symmetric])
    by (simp add: B_def)
  finally have *: \<open>cmod ((abs_op A *\<^sub>V e) \<bullet>\<^sub>C e) = (norm (B *\<^sub>V e))\<^sup>2\<close> for e
    by (metis Re_complex_of_real)

  have \<open>has_sum (\<lambda>e. cmod ((abs_op A *\<^sub>V e) \<bullet>\<^sub>C e)) E t \<longleftrightarrow> has_sum (\<lambda>e. (norm (B *\<^sub>V e))\<^sup>2) E t\<close>
    by (simp add: *)
  also have \<open>\<dots> = has_sum (\<lambda>f. (norm (B* *\<^sub>V f))\<^sup>2) F t\<close>
    apply (subst TODO_name2[where F=F])
    by (simp_all add: assms)
  also have \<open>\<dots> = has_sum (\<lambda>f. (norm (B *\<^sub>V f))\<^sup>2) F t\<close>
    using TODO_name2 assms(2) by blast
  also have \<open>\<dots> = has_sum (\<lambda>e. cmod ((abs_op A *\<^sub>V e) \<bullet>\<^sub>C e)) F t\<close>
    by (simp add: *)
  finally show ?thesis
    by simp
qed

definition trace_class :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_inner) \<Rightarrow> bool\<close> 
  where \<open>trace_class A \<longleftrightarrow> (\<exists>E. is_onb E \<and> (\<lambda>e. cmod ((abs_op A *\<^sub>V e) \<bullet>\<^sub>C e)) abs_summable_on E)\<close>

lemma trace_classI:
  assumes \<open>is_onb E\<close> and \<open>(\<lambda>e. cmod ((abs_op A *\<^sub>V e) \<bullet>\<^sub>C e)) abs_summable_on E\<close>
  shows \<open>trace_class A\<close>
  using assms(1) assms(2) trace_class_def by blast

lemma trace_class_iff_summable:
  assumes \<open>is_onb E\<close>
  shows \<open>trace_class A \<longleftrightarrow> (\<lambda>e. cmod ((abs_op A *\<^sub>V e) \<bullet>\<^sub>C e)) abs_summable_on E\<close>
  apply (auto intro!: trace_classI assms simp: trace_class_def)
  using assms summable_on_def trace_norm_basis_invariance by blast

lemma trace_class_0[simp]: \<open>trace_class 0\<close>
  unfolding trace_class_def
  by (auto intro!: exI[of _ some_chilbert_basis] simp: is_onb_def is_normal_some_chilbert_basis)

lemma trace_class_adj: \<open>trace_class a \<Longrightarrow> trace_class (a*)\<close>
  sorry

lemma trace_class_plus[simp]: \<open>trace_class t \<Longrightarrow> trace_class u \<Longrightarrow> trace_class (t + u)\<close>
  sorry

lemma trace_class_uminus[simp]: \<open>trace_class t \<Longrightarrow> trace_class (-t)\<close>
  by (auto simp add: trace_class_def)

lemma trace_class_minus[simp]: \<open>trace_class t \<Longrightarrow> trace_class u \<Longrightarrow> trace_class (t - u)\<close>
  by (metis trace_class_plus trace_class_uminus uminus_add_conv_diff)

definition trace_norm where \<open>trace_norm A = (if trace_class A then (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. cmod ((abs_op A *\<^sub>V e) \<bullet>\<^sub>C e)) else 0)\<close>

definition trace where \<open>trace A = (if trace_class A then (\<Sum>\<^sub>\<infinity>e\<in>some_chilbert_basis. e \<bullet>\<^sub>C (A *\<^sub>V e)) else 0)\<close>
(* TODO: switch sides of \<bullet>\<^sub>C !!!! *)

lemma trace_0[simp]: \<open>trace 0 = 0\<close>
  unfolding trace_def by simp

lemma trace_abs_op[simp]: \<open>trace (abs_op A) = trace_norm A\<close>
  sorry

lemma trace_class_butterfly[simp]: \<open>trace_class (butterfly x y)\<close>
  sorry

lemma trace_butterfly_comp: \<open>trace (butterfly x y o\<^sub>C\<^sub>L a) = y \<bullet>\<^sub>C (a *\<^sub>V x)\<close>
  sorry

lemma trace_butterfly: \<open>trace (butterfly x y) = y \<bullet>\<^sub>C x\<close>
  using trace_butterfly_comp[where a=id_cblinfun] by auto

lemma circularity_of_trace:
  assumes \<open>trace_class a\<close>
  shows \<open>trace (a o\<^sub>C\<^sub>L b) = trace (b o\<^sub>C\<^sub>L a)\<close>
  sorry

(* (* The conditions are all necessary, see https://mathoverflow.net/questions/76386/trab-trba *)
(* See https://mathoverflow.net/a/76389/101775 for a proof *)
lemma circularity_of_trace':
  assumes \<open>trace_class (a o\<^sub>C\<^sub>L b)\<close> \<open>trace_class (b o\<^sub>C\<^sub>L a)\<close>
  shows \<open>trace (a o\<^sub>C\<^sub>L b) = trace (b o\<^sub>C\<^sub>L a)\<close>
  sorry *)

lemma trace_class_comp_left: \<open>trace_class a \<Longrightarrow> trace_class (a o\<^sub>C\<^sub>L b)\<close>
  sorry

lemma trace_class_comp_right: \<open>trace_class b \<Longrightarrow> trace_class (a o\<^sub>C\<^sub>L b)\<close>
  sorry

lemma trace_norm_comp_left: \<open>trace_class a \<Longrightarrow> trace_norm (a o\<^sub>C\<^sub>L b) \<le> trace_norm a * norm b\<close>
  sorry

lemma trace_norm_comp_right: \<open>trace_class b \<Longrightarrow> trace_norm (a o\<^sub>C\<^sub>L b) \<le> norm a * trace_norm b\<close>
  sorry

lemma trace_plus: \<open>trace (a + b) = trace a + trace b\<close> if \<open>trace_class a\<close> \<open>trace_class b\<close>
  sorry

lemmas (in bounded_cbilinear) scaleR_right = bounded_bilinear.scaleR_right[OF bounded_bilinear]
lemmas (in bounded_cbilinear) scaleR_left = bounded_bilinear.scaleR_left[OF bounded_bilinear]
lemmas (in bounded_sesquilinear) scaleR_right = bounded_bilinear.scaleR_right[OF bounded_bilinear]
lemmas (in bounded_sesquilinear) scaleR_left = bounded_bilinear.scaleR_left[OF bounded_bilinear]

(* Better: add "interpretation cinner: bounded_sesquilinear cinner", but needs fixing local bounded_sesquilinear first *)
lemma cinner_scaleR_left [simp]: "cinner (scaleR r x) y = of_real r * (cinner x y)"
  by (simp add: scaleR_scaleC)

lemma cinner_scaleR_right [simp]: "cinner x (scaleR r y) = of_real r * (cinner x y)"
  by (simp add: scaleR_scaleC)

lemma trace_class_alt_def:
  assumes \<open>is_onb B\<close>
  shows \<open>trace_class A \<longleftrightarrow> (\<exists>E. is_onb E \<and> (\<lambda>e. cmod ((abs_op A *\<^sub>V e) \<bullet>\<^sub>C e)) abs_summable_on E)\<close>
  sorry

lemma trace_norm_alt_def:
  assumes \<open>is_onb B\<close>
  shows \<open>trace_norm A = (if trace_class A then (\<Sum>\<^sub>\<infinity>e\<in>B. cmod ((abs_op A *\<^sub>V e) \<bullet>\<^sub>C e)) else 0)\<close>
  sorry

lemma abs_op_nondegenerate: \<open>a = 0\<close> if \<open>abs_op a = 0\<close>
  sorry

lemma trace_norm_nondegenerate: \<open>a = 0\<close> if \<open>trace_class a\<close> and \<open>trace_norm a = 0\<close>
proof (rule ccontr)
  assume \<open>a \<noteq> 0\<close>
  then have \<open>abs_op a \<noteq> 0\<close>
    using abs_op_nondegenerate by blast
  then obtain x where xax: \<open>x \<bullet>\<^sub>C (abs_op a *\<^sub>V x) \<noteq> 0\<close>
    by (metis cblinfun.zero_left cblinfun_cinner_eqI cinner_zero_right)
  then have \<open>norm x \<noteq> 0\<close>
    by auto
  then have xax': \<open>sgn x \<bullet>\<^sub>C (abs_op a *\<^sub>V sgn x) \<noteq> 0\<close> and [simp]: \<open>norm (sgn x) = 1\<close>
    unfolding sgn_div_norm using xax by (auto simp: cblinfun.scaleR_right)
  obtain B where sgnx_B: \<open>{sgn x} \<subseteq> B\<close> and \<open>is_onb B\<close>
    apply atomize_elim apply (rule orthonormal_basis_exists)
    using \<open>norm x \<noteq> 0\<close> by (auto simp: is_ortho_set_def sgn_div_norm)

  from \<open>is_onb B\<close> that
  have summable: \<open>(\<lambda>e. (abs_op a *\<^sub>V e) \<bullet>\<^sub>C e) abs_summable_on B\<close>
    using trace_class_iff_summable by fastforce

  from that have \<open>0 = trace_norm a\<close>
    by simp
  also from \<open>is_onb B\<close> have \<open>trace_norm a = (\<Sum>\<^sub>\<infinity>e\<in>B. cmod ((abs_op a *\<^sub>V e) \<bullet>\<^sub>C e))\<close>
    by (smt (verit, ccfv_SIG) abs_norm_cancel infsum_cong infsum_not_exists real_norm_def trace_class_def trace_norm_alt_def)
  also have \<open>\<dots> \<ge> (\<Sum>\<^sub>\<infinity>e\<in>{sgn x}. cmod ((abs_op a *\<^sub>V e) \<bullet>\<^sub>C e))\<close> (is \<open>_ \<ge> \<dots>\<close>)
    apply (rule infsum_mono2)
    using summable sgnx_B by auto
  also from xax' have \<open>\<dots> > 0\<close>
    by (simp add: is_orthogonal_sym xax')
  finally show False
    by simp
qed

lemma
  assumes \<open>\<And>i. i\<in>I \<Longrightarrow> trace_class (a i)\<close>
  shows trace_sum: \<open>trace (\<Sum>i\<in>I. a i) = (\<Sum>i\<in>I. trace (a i))\<close>
    and trace_class_sum: \<open>trace_class (\<Sum>i\<in>I. a i)\<close>
  using assms apply (induction I rule:infinite_finite_induct)
  by (auto simp: trace_plus)

lemma bounded_clinear_trace_duality: \<open>trace_class t \<Longrightarrow> bounded_clinear (\<lambda>a. trace (t o\<^sub>C\<^sub>L a))\<close>
  sorry

typedef (overloaded) 'a::chilbert_space trace_class = \<open>Collect trace_class :: ('a \<Rightarrow>\<^sub>C\<^sub>L 'a) set\<close>
  by (auto intro!: exI[of _ 0])
setup_lifting type_definition_trace_class

instantiation trace_class :: (chilbert_space) "{complex_vector}" begin
(* Lifted definitions *)
lift_definition zero_trace_class :: \<open>'a trace_class\<close> is 0 by auto
lift_definition minus_trace_class :: \<open>'a trace_class \<Rightarrow> 'a trace_class \<Rightarrow> 'a trace_class\<close> is minus by auto
lift_definition uminus_trace_class :: \<open>'a trace_class \<Rightarrow> 'a trace_class\<close> is uminus by auto
lift_definition plus_trace_class :: \<open>'a trace_class \<Rightarrow> 'a trace_class \<Rightarrow> 'a trace_class\<close> is plus by auto
lift_definition scaleC_trace_class :: \<open>complex \<Rightarrow> 'a trace_class \<Rightarrow> 'a trace_class\<close> is scaleC
  by (metis (no_types, opaque_lifting) cblinfun_compose_id_right cblinfun_compose_scaleC_right mem_Collect_eq trace_class_comp_left)
lift_definition scaleR_trace_class :: \<open>real \<Rightarrow> 'a trace_class \<Rightarrow> 'a trace_class\<close> is scaleR
  by (metis (no_types, opaque_lifting) cblinfun_compose_id_right cblinfun_compose_scaleC_right mem_Collect_eq scaleR_scaleC trace_class_comp_left)
instance
proof standard
  fix a b c :: \<open>'a trace_class\<close>
  show \<open>a + b + c = a + (b + c)\<close>
    apply transfer by auto
  show \<open>a + b = b + a\<close>
    apply transfer by auto
  show \<open>0 + a = a\<close>
    apply transfer by auto
  show \<open>- a + a = 0\<close>
    apply transfer by auto
  show \<open>a - b = a + - b\<close>
    apply transfer by auto
  show \<open>(*\<^sub>R) r = ((*\<^sub>C) (complex_of_real r) :: _ \<Rightarrow> 'a trace_class)\<close> for r :: real
    by (metis (mono_tags, opaque_lifting) Trace_Class.scaleC_trace_class_def Trace_Class.scaleR_trace_class_def id_apply map_fun_def o_def scaleR_scaleC)
  show \<open>r *\<^sub>C (a + b) = r *\<^sub>C a + r *\<^sub>C b\<close> for r :: complex
    apply transfer
    by (metis (no_types, lifting) scaleC_add_right)
  show \<open>(r + r') *\<^sub>C a = r *\<^sub>C a + r' *\<^sub>C a\<close> for r r' :: complex
    apply transfer
    by (metis (no_types, lifting) scaleC_add_left)
  show \<open>r *\<^sub>C r' *\<^sub>C a = (r * r') *\<^sub>C a\<close> for r r' :: complex
    apply transfer by auto
  show \<open>1 *\<^sub>C a = a\<close>
    apply transfer by auto
qed
end

instantiation trace_class :: (chilbert_space) "{complex_normed_vector}" begin
(* Definitions related to the trace norm *)
lift_definition norm_trace_class :: \<open>'a trace_class \<Rightarrow> real\<close> is trace_norm .
definition sgn_trace_class :: \<open>'a trace_class \<Rightarrow> 'a trace_class\<close> where \<open>sgn_trace_class a = a /\<^sub>R norm a\<close>
definition dist_trace_class :: \<open>'a trace_class \<Rightarrow> _ \<Rightarrow> _\<close> where \<open>dist_trace_class a b = norm (a - b)\<close>
definition [code del]: "uniformity_trace_class = (INF e\<in>{0<..}. principal {(x::'a trace_class, y). dist x y < e})"
definition [code del]: "open_trace_class U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in INF e\<in>{0<..}. principal {(x, y). dist x y < e}. x' = x \<longrightarrow> y \<in> U)" for U :: "'a trace_class set"
instance
proof standard
  fix a b :: \<open>'a trace_class\<close>
  show \<open>dist a b = norm (a - b)\<close>
    by (metis (no_types, lifting) Trace_Class.dist_trace_class_def)
  show \<open>uniformity = (INF e\<in>{0<..}. principal {(x :: 'a trace_class, y). dist x y < e})\<close>
    by (simp add: uniformity_trace_class_def)
  show \<open>open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U)\<close> for U :: \<open>'a trace_class set\<close>
    by (smt (verit, del_insts) case_prod_beta' eventually_mono open_trace_class_def uniformity_trace_class_def)
  show \<open>(norm a = 0) = (a = 0)\<close>
    apply transfer
    sorry
  show \<open>norm (a + b) \<le> norm a + norm b\<close>
    apply transfer
    sorry
  show \<open>norm (r *\<^sub>C a) = cmod r * norm a\<close> for r
    apply transfer
    sorry
  then show \<open>norm (r *\<^sub>R a) = \<bar>r\<bar> * norm a\<close> for r
    by (metis norm_of_real scaleR_scaleC)
  show \<open>sgn a = a /\<^sub>R norm a\<close>
    by (simp add: sgn_trace_class_def)
qed
end

definition hilbert_schmidt where \<open>hilbert_schmidt a \<longleftrightarrow> trace_class (a* o\<^sub>C\<^sub>L a)\<close>

definition hilbert_schmidt_norm where \<open>hilbert_schmidt_norm a = sqrt (trace_norm (a* o\<^sub>C\<^sub>L a))\<close>

lemma hilbert_schmidt_0[simp]: \<open>hilbert_schmidt 0\<close>
  unfolding hilbert_schmidt_def by simp

typedef (overloaded) ('a::chilbert_space,'b::complex_inner) hilbert_schmidt = \<open>Collect hilbert_schmidt :: ('a \<Rightarrow>\<^sub>C\<^sub>L 'b) set\<close>
  by (auto intro!: exI[of _ 0])
setup_lifting type_definition_hilbert_schmidt

instantiation hilbert_schmidt :: (chilbert_space, complex_inner) "{zero,norm}" begin
lift_definition zero_hilbert_schmidt :: \<open>('a,'b) hilbert_schmidt\<close> is 0 by auto
lift_definition norm_hilbert_schmidt :: \<open>('a,'b) hilbert_schmidt \<Rightarrow> real\<close> is hilbert_schmidt_norm .
instance..
end

end
