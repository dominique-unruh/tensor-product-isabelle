theory Hilbert_Space_Tensor_Product
  imports Complex_Bounded_Operators.Complex_L2 Registers.Misc Misc_Tensor_Product
begin

unbundle cblinfun_notation
no_notation m_inv ("inv\<index> _" [81] 80)
no_notation eq_closure_of ("closure'_of\<index>")

subsection \<open>Tensor product on \<^typ>\<open>_ ell2\<close>\<close>

lift_definition tensor_ell2 :: \<open>'a ell2 \<Rightarrow> 'b ell2 \<Rightarrow> ('a\<times>'b) ell2\<close> (infixr "\<otimes>\<^sub>s" 70) is
  \<open>\<lambda>\<psi> \<phi> (i,j). \<psi> i * \<phi> j\<close>
proof -
  fix \<psi> :: \<open>'a \<Rightarrow> complex\<close> and \<phi> :: \<open>'b \<Rightarrow> complex\<close>
  assume \<open>has_ell2_norm \<psi>\<close> \<open>has_ell2_norm \<phi>\<close>
  from \<open>has_ell2_norm \<phi>\<close> have \<phi>_sum: \<open>(\<lambda>j. (\<psi> i * \<phi> j)\<^sup>2) abs_summable_on UNIV\<close> for i
    by (metis ell2_norm_smult(1) has_ell2_norm_def)
  have double_sum: \<open>(\<lambda>i. \<Sum>\<^sub>\<infinity>j. cmod ((\<psi> i * \<phi> j)\<^sup>2)) abs_summable_on UNIV\<close>
    apply (simp add: norm_mult power_mult_distrib infsum_cmult_right' del: real_norm_def)
    apply (rule summable_on_cmult_left)
    using \<open>has_ell2_norm \<psi>\<close> has_ell2_norm_def by auto
  have \<open>(\<lambda>(i,j). (\<psi> i * \<phi> j)\<^sup>2) abs_summable_on UNIV \<times> UNIV\<close>
    apply (rule abs_summable_on_Sigma_iff[THEN iffD2])
    using \<phi>_sum double_sum by auto
  then show \<open>has_ell2_norm (\<lambda>(i, j). \<psi> i * \<phi> j)\<close>
    by (auto simp add: has_ell2_norm_def case_prod_beta)
qed

lemma tensor_ell2_add1: \<open>tensor_ell2 (a + b) c = tensor_ell2 a c + tensor_ell2 b c\<close>
  apply transfer apply (rule ext) apply (auto simp: case_prod_beta)
  by (simp add: vector_space_over_itself.scale_left_distrib)

lemma tensor_ell2_add2: \<open>tensor_ell2 a (b + c) = tensor_ell2 a b + tensor_ell2 a c\<close>
  apply transfer apply (rule ext) apply (auto simp: case_prod_beta)
  by (meson algebra_simps)

lemma tensor_ell2_scaleC1: \<open>tensor_ell2 (c *\<^sub>C a) b = c *\<^sub>C tensor_ell2 a b\<close>
  apply transfer apply (rule ext) by (auto simp: case_prod_beta)

lemma tensor_ell2_scaleC2: \<open>tensor_ell2 a (c *\<^sub>C b) = c *\<^sub>C tensor_ell2 a b\<close>
  apply transfer apply (rule ext) by (auto simp: case_prod_beta)

lemma tensor_ell2_inner_prod[simp]: \<open>\<langle>tensor_ell2 a b, tensor_ell2 c d\<rangle> = \<langle>a,c\<rangle> * \<langle>b,d\<rangle>\<close>
  apply (rule local_defE[where y=\<open>tensor_ell2 a b\<close>], rename_tac ab)
  apply (rule local_defE[where y=\<open>tensor_ell2 c d\<close>], rename_tac cd)
proof (transfer, hypsubst_thin)
  fix a c :: \<open>'a \<Rightarrow> complex\<close> and b d :: \<open>'b \<Rightarrow> complex\<close>

  assume \<open>has_ell2_norm (\<lambda>(i, j). a i * b j)\<close> and \<open>has_ell2_norm (\<lambda>(i, j). c i * d j)\<close>

  then have *: \<open>(\<lambda>xy. cnj (a (fst xy) * b (snd xy)) * (c (fst xy) * d (snd xy))) abs_summable_on UNIV\<close>
    apply (rule_tac abs_summable_product)
    apply (metis (mono_tags, lifting) complex_mod_cnj complex_mod_mult_cnj has_ell2_norm_def norm_mult norm_power split_def summable_on_cong)
    by (metis (mono_tags, lifting) case_prod_unfold has_ell2_norm_def power2_eq_square summable_on_cong)

  then have *: \<open>(\<lambda>(x, y). cnj (a x * b y) * (c x * d y)) summable_on UNIV \<times> UNIV\<close>
    apply (rule_tac abs_summable_summable)
    by (simp add: case_prod_unfold)

  have \<open>(\<Sum>\<^sub>\<infinity>i. cnj (case i of (i, j) \<Rightarrow> a i * b j) * (case i of (i, j) \<Rightarrow> c i * d j))
     = (\<Sum>\<^sub>\<infinity>(i,j)\<in>UNIV\<times>UNIV. cnj (a i * b j) * (c i * d j))\<close> (is \<open>?lhs = _\<close>)
    by (simp add: case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>i. \<Sum>\<^sub>\<infinity>j. cnj (a i * b j) * (c i * d j))\<close>
    apply (subst infsum_Sigma'_banach[symmetric])
    using * by auto
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>i. cnj (a i) * c i) * (\<Sum>\<^sub>\<infinity>j. cnj (b j) * (d j))\<close> (is \<open>_ = ?rhs\<close>)
    apply (subst infsum_cmult_left'[symmetric])
    by (auto intro!: infsum_cong simp flip: infsum_cmult_right')
  finally show \<open>?lhs = ?rhs\<close>
    by -
qed

lemma tensor_ell2_norm: \<open>norm (a \<otimes>\<^sub>s b) = norm a * norm b\<close>
  by (simp add: norm_eq_sqrt_cinner[where 'a=\<open>(_::type) ell2\<close>] norm_mult real_sqrt_mult)

lemma clinear_tensor_ell21: "clinear (\<lambda>b. a \<otimes>\<^sub>s b)"
  apply (rule clinearI; transfer)
   apply (auto simp: case_prod_beta)
  by (simp add: cond_case_prod_eta algebra_simps)

lemma bounded_clinear_tensor_ell21: "bounded_clinear (\<lambda>b. a \<otimes>\<^sub>s b)"
  apply (auto intro!: bounded_clinear.intro clinear_tensor_ell21
      simp: bounded_clinear_axioms_def tensor_ell2_norm)
  using mult.commute order_eq_refl by blast

lemma clinear_tensor_ell22: "clinear (\<lambda>a. a \<otimes>\<^sub>s b)"
  apply (rule clinearI; transfer)
   apply (auto simp: case_prod_beta)
  by (simp add: case_prod_beta' algebra_simps)

lemma bounded_clinear_tensor_ell22: "bounded_clinear (\<lambda>a. tensor_ell2 a b)"
  by (auto intro!: bounded_clinear.intro clinear_tensor_ell22
      simp: bounded_clinear_axioms_def tensor_ell2_norm)

lemma tensor_ell2_ket[simp]: "tensor_ell2 (ket i) (ket j) = ket (i,j)"
  apply transfer by auto

lemma tensor_ell2_0_left[simp]: \<open>0 \<otimes>\<^sub>s x = 0\<close>
  apply transfer by auto

lemma tensor_ell2_0_right[simp]: \<open>x \<otimes>\<^sub>s 0 = 0\<close>
  apply transfer by auto

lemma tensor_ell2_sum_left: \<open>(\<Sum>x\<in>X. a x) \<otimes>\<^sub>s b = (\<Sum>x\<in>X. a x \<otimes>\<^sub>s b)\<close>
  apply (induction X rule:infinite_finite_induct)
  by (auto simp: tensor_ell2_add1)

lemma tensor_ell2_sum_right: \<open>a \<otimes>\<^sub>s (\<Sum>x\<in>X. b x) = (\<Sum>x\<in>X. a \<otimes>\<^sub>s b x)\<close>
  apply (induction X rule:infinite_finite_induct)
  by (auto simp: tensor_ell2_add2)

lemma norm_tensor_ell2: \<open>norm (a \<otimes>\<^sub>s b) = norm a * norm b\<close>
proof transfer
  fix a :: \<open>'a \<Rightarrow> complex\<close> and b :: \<open>'b \<Rightarrow> complex\<close>
  assume \<open>has_ell2_norm a\<close> \<open>has_ell2_norm b\<close>
  have 1: \<open>(\<lambda>j. (a i * b j)\<^sup>2) abs_summable_on UNIV\<close> for i
    using \<open>has_ell2_norm b\<close>
    by (auto simp add: power_mult_distrib norm_mult has_ell2_norm_def
        intro!: summable_on_cmult_right)
  have 2: \<open>(\<lambda>i. cmod (\<Sum>\<^sub>\<infinity>j. cmod ((a i * b j)\<^sup>2))) summable_on UNIV\<close>
    using \<open>has_ell2_norm a\<close>
    by (auto simp add: power_mult_distrib norm_mult has_ell2_norm_def infsum_cmult_right'
        intro!: summable_on_cmult_left)
  have 3: \<open>(\<lambda>p. (a (fst p) * b (snd p))\<^sup>2) abs_summable_on UNIV \<times> UNIV\<close>
    using 1 2 by (auto intro!: abs_summable_on_Sigma_iff[THEN iffD2] simp flip: UNIV_Times_UNIV)

  have \<open>(ell2_norm (\<lambda>(i, j). a i * b j))\<^sup>2 = (\<Sum>\<^sub>\<infinity>(i,j). (cmod (a i * b j))\<^sup>2)\<close>
    by (simp add: ell2_norm_def case_prod_unfold infsum_nonneg)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(i,j). cmod ((a i * b j)\<^sup>2))\<close>
    by (simp add: norm_power)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>i. \<Sum>\<^sub>\<infinity>j. cmod ((a i * b j)\<^sup>2))\<close>
    using 3 by (simp add: infsum_Sigma'_banach case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>i. \<Sum>\<^sub>\<infinity>j. (cmod (a i))\<^sup>2 * (cmod (b j))\<^sup>2)\<close>
    by (simp add: norm_power power_mult_distrib norm_mult)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>i. (cmod (a i))\<^sup>2 * (\<Sum>\<^sub>\<infinity>j. (cmod (b j))\<^sup>2))\<close>
    by (simp add: infsum_cmult_right')
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>i. (cmod (a i))\<^sup>2) * (\<Sum>\<^sub>\<infinity>j. (cmod (b j))\<^sup>2)\<close>
    by (simp add: infsum_cmult_left')
  also have \<open>\<dots> = (ell2_norm a)\<^sup>2 * (ell2_norm b)\<^sup>2\<close>
    by (metis (mono_tags, lifting) ell2_norm_def ell2_norm_geq0 real_sqrt_ge_0_iff real_sqrt_pow2_iff)
  finally show \<open>ell2_norm (\<lambda>(i, j). a i * b j) = ell2_norm a * ell2_norm b\<close>
    by (metis ell2_norm_geq0 mult_nonneg_nonneg power2_eq_imp_eq power_mult_distrib)
qed

lemma tensor_ell2_dense:
  fixes S :: \<open>'a ell2 set\<close> and T :: \<open>'b ell2 set\<close>
  assumes \<open>closure (cspan S) = UNIV\<close> and \<open>closure (cspan T) = UNIV\<close>
  shows \<open>closure (cspan {a\<otimes>\<^sub>sb | a b. a\<in>S \<and> b\<in>T}) = UNIV\<close>
proof -
  define ST where \<open>ST = {a\<otimes>\<^sub>sb | a b. a\<in>S \<and> b\<in>T}\<close>
  from assms have 1: \<open>bounded_clinear F \<Longrightarrow> bounded_clinear G \<Longrightarrow> (\<forall>x\<in>S. F x = G x) \<Longrightarrow> F = G\<close> for F G :: \<open>'a ell2 \<Rightarrow> complex\<close>
    using dense_span_separating[of S F G] by auto
  from assms have 2: \<open>bounded_clinear F \<Longrightarrow> bounded_clinear G \<Longrightarrow> (\<forall>x\<in>T. F x = G x) \<Longrightarrow> F = G\<close> for F G :: \<open>'b ell2 \<Rightarrow> complex\<close>
    using dense_span_separating[of T F G] by auto
  have \<open>F = G\<close> 
    if [simp]: \<open>bounded_clinear F\<close> \<open>bounded_clinear G\<close> and eq: \<open>\<forall>x\<in>ST. F x = G x\<close>
    for F G :: \<open>('a\<times>'b) ell2 \<Rightarrow> complex\<close>
  proof -
    from eq have eq': \<open>F (s \<otimes>\<^sub>s t) = G (s \<otimes>\<^sub>s t)\<close> if \<open>s \<in> S\<close> and \<open>t \<in> T\<close> for s t
      using ST_def that by blast
    then have \<open>F (s \<otimes>\<^sub>s ket t) = G (s \<otimes>\<^sub>s ket t)\<close> if \<open>s \<in> S\<close> for s t
      apply (rule_tac fun_cong[where x=\<open>ket t\<close>])
      apply (rule 2)
      using that by (auto simp add: bounded_clinear_compose bounded_clinear_tensor_ell21)
    then have \<open>F (ket s \<otimes>\<^sub>s ket t) = G (ket s \<otimes>\<^sub>s ket t)\<close> for s t
      apply (rule_tac fun_cong[where x=\<open>ket s\<close>])
      apply (rule 1)
      apply (auto simp add: bounded_clinear_compose bounded_clinear_tensor_ell21)
      using that bounded_clinear_compose bounded_clinear_tensor_ell22 that by blast+
    then show "F = G"
      apply (rule_tac bounded_clinear_equal_ket)
      by auto
  qed
  then show \<open>closure (cspan ST) = UNIV\<close>
    using separating_dense_span by blast
qed

definition assoc_ell2 :: \<open>(('a\<times>'b)\<times>'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a\<times>('b\<times>'c)) ell2\<close> where
  \<open>assoc_ell2 = classical_operator (Some o (\<lambda>((a,b),c). (a,(b,c))))\<close>

lemma unitary_assoc_ell2[simp]: \<open>unitary assoc_ell2\<close>
  unfolding assoc_ell2_def
  apply (rule unitary_classical_operator)
  apply (rule o_bij[of \<open>(\<lambda>(a,(b,c)). ((a,b),c))\<close>])
  by auto

lemma assoc_ell2_tensor: \<open>assoc_ell2 *\<^sub>V ((a \<otimes>\<^sub>s b) \<otimes>\<^sub>s c) = (a \<otimes>\<^sub>s (b \<otimes>\<^sub>s c))\<close>
proof -
  note [simp] = bounded_clinear_compose[OF bounded_clinear_tensor_ell21]
    bounded_clinear_compose[OF bounded_clinear_tensor_ell22]
    bounded_clinear_cblinfun_apply
  have \<open>assoc_ell2 *\<^sub>V ((ket a \<otimes>\<^sub>s ket b) \<otimes>\<^sub>s ket c) = (ket a \<otimes>\<^sub>s (ket b \<otimes>\<^sub>s ket c))\<close> for a :: 'a and b :: 'b and c :: 'c
    by (simp add: inj_def assoc_ell2_def classical_operator_ket classical_operator_exists_inj)
  then have \<open>assoc_ell2 *\<^sub>V ((ket a \<otimes>\<^sub>s ket b) \<otimes>\<^sub>s c) = (ket a \<otimes>\<^sub>s (ket b \<otimes>\<^sub>s c))\<close> for a :: 'a and b :: 'b
    apply (rule_tac fun_cong[where x=c])
    apply (rule_tac bounded_clinear_equal_ket)
    by auto
  then have \<open>assoc_ell2 *\<^sub>V ((ket a \<otimes>\<^sub>s b) \<otimes>\<^sub>s c) = (ket a \<otimes>\<^sub>s (b \<otimes>\<^sub>s c))\<close> for a :: 'a
    apply (rule_tac fun_cong[where x=b])
    apply (rule_tac bounded_clinear_equal_ket)
    by auto
  then show \<open>assoc_ell2 *\<^sub>V ((a \<otimes>\<^sub>s b) \<otimes>\<^sub>s c) = (a \<otimes>\<^sub>s (b \<otimes>\<^sub>s c))\<close>
    apply (rule_tac fun_cong[where x=a])
    apply (rule_tac bounded_clinear_equal_ket)
    by auto
qed

lemma assoc_ell2'_tensor: \<open>assoc_ell2* *\<^sub>V tensor_ell2 a (tensor_ell2 b c) = tensor_ell2 (tensor_ell2 a b) c\<close>
  by (metis (no_types, opaque_lifting) assoc_ell2_tensor cblinfun_apply_cblinfun_compose id_cblinfun.rep_eq unitaryD1 unitary_assoc_ell2)

definition swap_ell2 :: \<open>('a\<times>'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('b\<times>'a) ell2\<close> where
  \<open>swap_ell2 = classical_operator (Some o prod.swap)\<close>

lemma unitary_swap_ell2[simp]: \<open>unitary swap_ell2\<close>
  unfolding swap_ell2_def
  apply (rule unitary_classical_operator)
  by auto

lemma swap_ell2_tensor[simp]: \<open>swap_ell2 *\<^sub>V (a \<otimes>\<^sub>s b) = b \<otimes>\<^sub>s a\<close> for a :: \<open>'a ell2\<close> and b :: \<open>'b ell2\<close>
proof -
  note [simp] = bounded_clinear_compose[OF bounded_clinear_tensor_ell21]
    bounded_clinear_compose[OF bounded_clinear_tensor_ell22]
    bounded_clinear_cblinfun_apply
  have \<open>swap_ell2 *\<^sub>V (ket a \<otimes>\<^sub>s ket b) = (ket b \<otimes>\<^sub>s ket a)\<close> for a :: 'a and b :: 'b
    by (simp add: inj_def swap_ell2_def classical_operator_ket classical_operator_exists_inj)
  then have \<open>swap_ell2 *\<^sub>V (ket a \<otimes>\<^sub>s b) = (b \<otimes>\<^sub>s ket a)\<close> for a :: 'a
    apply (rule_tac fun_cong[where x=b])
    apply (rule_tac bounded_clinear_equal_ket)
    by auto
  then show \<open>swap_ell2 *\<^sub>V (a \<otimes>\<^sub>s b) = (b \<otimes>\<^sub>s a)\<close>
    apply (rule_tac fun_cong[where x=a])
    apply (rule_tac bounded_clinear_equal_ket)
    by auto
qed

lemma inv_prod_swap[simp]: \<open>inv prod.swap = prod.swap\<close>
  by (simp add: inv_unique_comp)

lemma adjoint_swap_ell2[simp]: \<open>swap_ell2* = swap_ell2\<close>
  by (simp add: swap_ell2_def inv_map_total)

lemma tensor_ell2_extensionality:
  assumes "(\<And>s t. a *\<^sub>V (s \<otimes>\<^sub>s t) = b *\<^sub>V (s \<otimes>\<^sub>s t))"
  shows "a = b"
  apply (rule equal_ket, case_tac x, hypsubst_thin)
  by (simp add: assms flip: tensor_ell2_ket)

lemma tensor_ell2_nonzero: \<open>a \<otimes>\<^sub>s b \<noteq> 0\<close> if \<open>a \<noteq> 0\<close> and \<open>b \<noteq> 0\<close>
  apply (use that in transfer)
  apply auto
  by (metis mult_eq_0_iff old.prod.case)

lemma swap_ell2_selfinv[simp]: \<open>swap_ell2 o\<^sub>C\<^sub>L swap_ell2 = id_cblinfun\<close>
  by (metis adjoint_swap_ell2 unitary_def unitary_swap_ell2)

lemma bounded_cbilinear_tensor_ell2[bounded_cbilinear]: \<open>bounded_cbilinear (\<otimes>\<^sub>s)\<close>
proof standard
  fix a a' :: "'a ell2" and b b' :: "'b ell2" and r :: complex
  show \<open>tensor_ell2 (a + a') b = tensor_ell2 a b + tensor_ell2 a' b\<close>
    by (meson tensor_ell2_add1)
  show \<open>tensor_ell2 a (b + b') = tensor_ell2 a b + tensor_ell2 a b'\<close>
    by (simp add: tensor_ell2_add2)  
  show \<open>tensor_ell2 (r *\<^sub>C a) b = r *\<^sub>C tensor_ell2 a b\<close>
    by (simp add: tensor_ell2_scaleC1)
  show \<open>tensor_ell2 a (r *\<^sub>C b) = r *\<^sub>C tensor_ell2 a b\<close>
    by (simp add: tensor_ell2_scaleC2)
  show \<open>\<exists>K. \<forall>a b. norm (tensor_ell2 a b) \<le> norm a * norm b * K \<close>
    apply (rule exI[of _ 1])
    by (simp add: norm_tensor_ell2)
qed

subsection \<open>Tensor product of operators on \<^typ>\<open>_ ell2\<close>\<close>

definition tensor_op :: \<open>('a ell2, 'b ell2) cblinfun \<Rightarrow> ('c ell2, 'd ell2) cblinfun
      \<Rightarrow> (('a\<times>'c) ell2, ('b\<times>'d) ell2) cblinfun\<close> (infixr "\<otimes>\<^sub>o" 70) where
  \<open>tensor_op M N = cblinfun_extension (range ket) (\<lambda>k. case (inv ket k) of (x,y) \<Rightarrow> tensor_ell2 (M *\<^sub>V ket x) (N *\<^sub>V ket y))\<close>

(* Vaguely following Takesaki, Section IV.1 *) (* TODO bibtex *)
lemma  
  fixes a :: \<open>'a\<close> and b :: \<open>'b\<close> and c :: \<open>'c\<close> and d :: \<open>'d\<close> and M :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close> and N :: \<open>'c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2\<close>
  shows tensor_op_ell2: \<open>(M \<otimes>\<^sub>o N) *\<^sub>V (\<psi> \<otimes>\<^sub>s \<phi>) = (M *\<^sub>V \<psi>) \<otimes>\<^sub>s (N *\<^sub>V \<phi>)\<close>
  and tensor_op_norm: \<open>norm (M \<otimes>\<^sub>o N) = norm M * norm N\<close>
proof -
  define S1 :: \<open>('a\<times>'d) ell2 set\<close> and f1 g1 extg1 
    where \<open>S1 = range ket\<close> 
      and \<open>f1 k = (case (inv ket k) of (x,y) \<Rightarrow> tensor_ell2 (M *\<^sub>V ket x) (ket y))\<close>
      and \<open>g1 = cconstruct S1 f1\<close> and \<open>extg1 = cblinfun_extension (cspan S1) g1\<close>
    for k
  define S2 :: \<open>('a\<times>'c) ell2 set\<close> and f2 g2 extg2
    where \<open>S2 = range ket\<close> 
      and \<open>f2 k = (case (inv ket k) of (x,y) \<Rightarrow> tensor_ell2 (ket x) (N *\<^sub>V ket y))\<close>
      and \<open>g2 = cconstruct S2 f2\<close> and \<open>extg2 = cblinfun_extension (cspan S2) g2\<close>
    for k
  define tensorMN where \<open>tensorMN = extg1 o\<^sub>C\<^sub>L extg2\<close>

  have extg1_ket: \<open>extg1 *\<^sub>V ket (x,y) = (M *\<^sub>V ket x) \<otimes>\<^sub>s ket y\<close>
    and norm_extg1: \<open>norm extg1 \<le> norm M\<close> for x y
  proof -
    have [simp]: \<open>cindependent S1\<close>
      using S1_def cindependent_ket by blast
    have [simp]: \<open>closure (cspan S1) = UNIV\<close>
      by (simp add: S1_def)
    have [simp]: \<open>ket (x, y) \<in> cspan S1\<close> for x y
      by (simp add: S1_def complex_vector.span_base)
    have g1_f1: \<open>g1 (ket (x,y)) = f1 (ket (x,y))\<close> for x y
      by (metis S1_def \<open>cindependent S1\<close> complex_vector.construct_basis g1_def rangeI)
    have [simp]: \<open>clinear g1\<close>
      unfolding g1_def using \<open>cindependent S1\<close> by (rule complex_vector.linear_construct)
    then have g1_add: \<open>g1 (x + y) = g1 x + g1 y\<close> if \<open>x \<in> cspan S1\<close> and \<open>y \<in> cspan S1\<close> for x y
      using clinear_iff by blast
    from \<open>clinear g1\<close> have g1_scale: \<open>g1 (c *\<^sub>C x) = c *\<^sub>C g1 x\<close> if \<open>x \<in> cspan S1\<close> for x c
      by (simp add: complex_vector.linear_scale)

    have g1_bounded: \<open>norm (g1 \<psi>) \<le> norm M * norm \<psi>\<close> if \<open>\<psi> \<in> cspan S1\<close> for \<psi>
    proof -
      from that obtain t r where \<open>finite t\<close> and \<open>t \<subseteq> range ket\<close> and \<psi>_tr: \<open>\<psi> = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
        by (smt (verit) complex_vector.span_explicit mem_Collect_eq S1_def)
      define X Y where \<open>X = fst ` inv ket ` t\<close> and \<open>Y = snd ` inv ket ` t\<close>
      have g1_ket: \<open>g1 (ket (x,y)) = (M *\<^sub>V ket x) \<otimes>\<^sub>s ket y\<close> for x y
        apply (simp add: g1_def S1_def)
        apply (subst complex_vector.construct_basis)
        by (auto simp add: f1_def cindependent_ket)
      define \<xi> where \<open>\<xi> y = (\<Sum>x\<in>X. if (ket (x,y) \<in> t) then r (ket (x,y)) *\<^sub>C ket x else 0)\<close> for y
      have \<psi>\<xi>: \<open>\<psi> = (\<Sum>y\<in>Y. \<xi> y \<otimes>\<^sub>s ket y)\<close>
      proof -
        have \<open>(\<Sum>y\<in>Y. \<xi> y \<otimes>\<^sub>s ket y) = (\<Sum>xy\<in>X \<times> Y. if ket xy \<in> t then r (ket xy) *\<^sub>C ket xy else 0)\<close>
          apply (simp add: \<xi>_def tensor_ell2_sum_left)
          apply (subst sum.swap)
          by (auto simp: sum.cartesian_product tensor_ell2_scaleC1 intro!: sum.cong)
        also have \<open>\<dots> = (\<Sum>xy\<in>ket ` (X \<times> Y). if xy \<in> t then r xy *\<^sub>C xy else 0)\<close>
          apply (subst sum.reindex)
          by (auto simp add: inj_on_def)
        also have \<open>\<dots> = \<psi>\<close>
          unfolding \<psi>_tr
          apply (rule sum.mono_neutral_cong_right)
             apply (auto simp add: X_def Y_def \<open>finite t\<close>)
          by (smt (verit, ccfv_SIG) Sigma_cong Y_def \<open>t \<subseteq> range ket\<close> f_inv_into_f image_eqI subsetD subset_fst_snd)
        finally show ?thesis
          by simp
      qed
      have \<open>(norm (g1 \<psi>))\<^sup>2 = (norm (\<Sum>y\<in>Y. (M *\<^sub>V \<xi> y) \<otimes>\<^sub>s ket y))\<^sup>2\<close>
        by (auto simp: \<psi>\<xi> complex_vector.linear_sum \<xi>_def tensor_ell2_sum_left 
            complex_vector.linear_scale g1_ket tensor_ell2_scaleC1
            complex_vector.linear_0
            intro!: sum.cong arg_cong[where f=norm])
      also have \<open>\<dots> = (\<Sum>y\<in>Y. (norm ((M *\<^sub>V \<xi> y) \<otimes>\<^sub>s ket y))\<^sup>2)\<close>
        apply (rule pythagorean_theorem_sum)
        using Y_def \<open>finite t\<close> by auto
      also have \<open>\<dots> = (\<Sum>y\<in>Y. (norm (M *\<^sub>V \<xi> y))\<^sup>2)\<close>
        by (simp add: norm_tensor_ell2)
      also have \<open>\<dots> \<le> (\<Sum>y\<in>Y. (norm M * norm (\<xi> y))\<^sup>2)\<close>
        by (meson norm_cblinfun norm_ge_zero power_mono sum_mono)
      also have \<open>\<dots> = (norm M)\<^sup>2 * (\<Sum>y\<in>Y. (norm (\<xi> y \<otimes>\<^sub>s ket y))\<^sup>2)\<close>
        by (simp add: power_mult_distrib norm_tensor_ell2 flip: sum_distrib_left)
      also have \<open>\<dots> = (norm M)\<^sup>2 * (norm (\<Sum>y\<in>Y. \<xi> y \<otimes>\<^sub>s ket y))\<^sup>2\<close>
        apply (subst pythagorean_theorem_sum)
        using Y_def \<open>finite t\<close> by auto
      also have \<open>\<dots> = (norm M)\<^sup>2 * (norm \<psi>)\<^sup>2\<close>
        using \<psi>\<xi> by fastforce
      finally show \<open>norm (g1 \<psi>) \<le> norm M * norm \<psi>\<close>
        by (metis mult_nonneg_nonneg norm_ge_zero power2_le_imp_le power_mult_distrib)
    qed

    from g1_add g1_scale g1_bounded
    have extg1_exists: \<open>cblinfun_extension_exists (cspan S1) g1\<close>
      apply (rule_tac cblinfun_extension_exists_bounded_dense[where B=\<open>norm M\<close>])
      by auto

    then show \<open>extg1 *\<^sub>V ket (x,y) = (M *\<^sub>V ket x) \<otimes>\<^sub>s ket y\<close> for x y
      by (simp add: extg1_def cblinfun_extension_apply g1_f1 f1_def)

    from g1_add g1_scale g1_bounded
    show \<open>norm extg1 \<le> norm M\<close>
      by (auto simp: extg1_def intro!: cblinfun_extension_exists_norm)
  qed

  have extg1_apply: \<open>extg1 *\<^sub>V (\<psi> \<otimes>\<^sub>s \<phi>) = (M *\<^sub>V \<psi>) \<otimes>\<^sub>s \<phi>\<close> for \<psi> \<phi>
  proof -
    have 1: \<open>bounded_clinear (\<lambda>a. extg1 *\<^sub>V (a \<otimes>\<^sub>s ket y))\<close> for y
      by (intro bounded_clinear_cblinfun_apply bounded_clinear_tensor_ell22)
    have 2: \<open>bounded_clinear (\<lambda>a. (M *\<^sub>V a) \<otimes>\<^sub>s ket y)\<close> for y :: 'd
      by (auto intro!: bounded_clinear_tensor_ell22[THEN bounded_clinear_compose] bounded_clinear_cblinfun_apply)
    have 3: \<open>bounded_clinear (\<lambda>a. extg1 *\<^sub>V (\<psi> \<otimes>\<^sub>s a))\<close>
      by (intro bounded_clinear_cblinfun_apply bounded_clinear_tensor_ell21)
    have 4: \<open>bounded_clinear ((\<otimes>\<^sub>s) (M *\<^sub>V \<psi>))\<close>
      by (auto intro!: bounded_clinear_tensor_ell21[THEN bounded_clinear_compose] bounded_clinear_cblinfun_apply)

    have eq_ket: \<open>extg1 *\<^sub>V tensor_ell2 \<psi> (ket y) = tensor_ell2 (M *\<^sub>V \<psi>) (ket y)\<close> for y
      apply (rule bounded_clinear_eq_on[where t=\<psi> and G=\<open>range ket\<close>])
      using 1 2 extg1_ket by auto
    show ?thesis 
      apply (rule bounded_clinear_eq_on[where t=\<phi> and G=\<open>range ket\<close>])
      using 3 4 eq_ket by auto
  qed

  have extg2_ket: \<open>extg2 *\<^sub>V ket (x,y) = ket x \<otimes>\<^sub>s (N *\<^sub>V ket y)\<close>
    and norm_extg2: \<open>norm extg2 \<le> norm N\<close> for x y
  proof -
    have [simp]: \<open>cindependent S2\<close>
      using S2_def cindependent_ket by blast
    have [simp]: \<open>closure (cspan S2) = UNIV\<close>
      by (simp add: S2_def)
    have [simp]: \<open>ket (x, y) \<in> cspan S2\<close> for x y
      by (simp add: S2_def complex_vector.span_base)
    have g2_f2: \<open>g2 (ket (x,y)) = f2 (ket (x,y))\<close> for x y
      by (metis S2_def \<open>cindependent S2\<close> complex_vector.construct_basis g2_def rangeI)
    have [simp]: \<open>clinear g2\<close>
      unfolding g2_def using \<open>cindependent S2\<close> by (rule complex_vector.linear_construct)
    then have g2_add: \<open>g2 (x + y) = g2 x + g2 y\<close> if \<open>x \<in> cspan S2\<close> and \<open>y \<in> cspan S2\<close> for x y
      using clinear_iff by blast
    from \<open>clinear g2\<close> have g2_scale: \<open>g2 (c *\<^sub>C x) = c *\<^sub>C g2 x\<close> if \<open>x \<in> cspan S2\<close> for x c
      by (simp add: complex_vector.linear_scale)

    have g2_bounded: \<open>norm (g2 \<psi>) \<le> norm N * norm \<psi>\<close> if \<open>\<psi> \<in> cspan S2\<close> for \<psi>
    proof -
      from that obtain t r where \<open>finite t\<close> and \<open>t \<subseteq> range ket\<close> and \<psi>_tr: \<open>\<psi> = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
        by (smt (verit) complex_vector.span_explicit mem_Collect_eq S2_def)
      define X Y where \<open>X = fst ` inv ket ` t\<close> and \<open>Y = snd ` inv ket ` t\<close>
      have g2_ket: \<open>g2 (ket (x,y)) = ket x \<otimes>\<^sub>s (N *\<^sub>V ket y)\<close> for x y
        apply (simp add: g2_def S2_def)
        apply (subst complex_vector.construct_basis)
        by (auto simp add: f2_def cindependent_ket)
      define \<xi> where \<open>\<xi> x = (\<Sum>y\<in>Y. if (ket (x,y) \<in> t) then r (ket (x,y)) *\<^sub>C ket y else 0)\<close> for x
      have \<psi>\<xi>: \<open>\<psi> = (\<Sum>x\<in>X. ket x \<otimes>\<^sub>s \<xi> x)\<close>
      proof -
        have \<open>(\<Sum>x\<in>X. ket x \<otimes>\<^sub>s \<xi> x) = (\<Sum>xy\<in>X \<times> Y. if ket xy \<in> t then r (ket xy) *\<^sub>C ket xy else 0)\<close>
          apply (simp add: \<xi>_def tensor_ell2_sum_right)
          by (auto simp: sum.cartesian_product tensor_ell2_scaleC2 intro!: sum.cong)
        also have \<open>\<dots> = (\<Sum>xy\<in>ket ` (X \<times> Y). if xy \<in> t then r xy *\<^sub>C xy else 0)\<close>
          apply (subst sum.reindex)
          by (auto simp add: inj_on_def)
        also have \<open>\<dots> = \<psi>\<close>
          unfolding \<psi>_tr
          apply (rule sum.mono_neutral_cong_right)
             apply (auto simp add: X_def Y_def \<open>finite t\<close>)
          by (smt (verit, ccfv_SIG) Sigma_cong Y_def \<open>t \<subseteq> range ket\<close> f_inv_into_f image_eqI subsetD subset_fst_snd)
        finally show ?thesis
          by simp
      qed
      have \<open>(norm (g2 \<psi>))\<^sup>2 = (norm (\<Sum>x\<in>X. ket x \<otimes>\<^sub>s (N *\<^sub>V \<xi> x)))\<^sup>2\<close>
        by (auto simp: \<psi>\<xi> complex_vector.linear_sum \<xi>_def tensor_ell2_sum_right
            complex_vector.linear_scale g2_ket tensor_ell2_scaleC2
            complex_vector.linear_0
            intro!: sum.cong arg_cong[where f=norm])
      also have \<open>\<dots> = (\<Sum>x\<in>X. (norm (ket x \<otimes>\<^sub>s (N *\<^sub>V \<xi> x)))\<^sup>2)\<close>
        apply (rule pythagorean_theorem_sum)
        using X_def \<open>finite t\<close> by auto
      also have \<open>\<dots> = (\<Sum>x\<in>X. (norm (N *\<^sub>V \<xi> x))\<^sup>2)\<close>
        by (simp add: norm_tensor_ell2)
      also have \<open>\<dots> \<le> (\<Sum>x\<in>X. (norm N * norm (\<xi> x))\<^sup>2)\<close>
        by (meson norm_cblinfun norm_ge_zero power_mono sum_mono)
      also have \<open>\<dots> = (norm N)\<^sup>2 * (\<Sum>x\<in>X. (norm (ket x \<otimes>\<^sub>s \<xi> x))\<^sup>2)\<close>
        by (simp add: power_mult_distrib norm_tensor_ell2 flip: sum_distrib_left)
      also have \<open>\<dots> = (norm N)\<^sup>2 * (norm (\<Sum>x\<in>X. ket x \<otimes>\<^sub>s \<xi> x))\<^sup>2\<close>
        apply (subst pythagorean_theorem_sum)
        using X_def \<open>finite t\<close> by auto
      also have \<open>\<dots> = (norm N)\<^sup>2 * (norm \<psi>)\<^sup>2\<close>
        using \<psi>\<xi> by fastforce
      finally show \<open>norm (g2 \<psi>) \<le> norm N * norm \<psi>\<close>
        by (metis mult_nonneg_nonneg norm_ge_zero power2_le_imp_le power_mult_distrib)
    qed

    from g2_add g2_scale g2_bounded
    have extg2_exists: \<open>cblinfun_extension_exists (cspan S2) g2\<close>
      apply (rule_tac cblinfun_extension_exists_bounded_dense[where B=\<open>norm N\<close>])
      by auto

    then show \<open>extg2 *\<^sub>V ket (x,y) = ket x \<otimes>\<^sub>s N *\<^sub>V ket y\<close> for x y
      by (simp add: extg2_def cblinfun_extension_apply g2_f2 f2_def)

    from g2_add g2_scale g2_bounded
    show \<open>norm extg2 \<le> norm N\<close>
      by (auto simp: extg2_def intro!: cblinfun_extension_exists_norm)
  qed

  have extg2_apply: \<open>extg2 *\<^sub>V (\<psi> \<otimes>\<^sub>s \<phi>) = \<psi> \<otimes>\<^sub>s (N *\<^sub>V \<phi>)\<close> for \<psi> \<phi>
  proof -
    have 1: \<open>bounded_clinear (\<lambda>a. extg2 *\<^sub>V (ket x \<otimes>\<^sub>s a))\<close> for x
      by (intro bounded_clinear_cblinfun_apply bounded_clinear_tensor_ell21)
    have 2: \<open>bounded_clinear (\<lambda>a. ket x \<otimes>\<^sub>s (N *\<^sub>V a))\<close> for x :: 'a
      by (auto intro!: bounded_clinear_tensor_ell21[THEN bounded_clinear_compose] bounded_clinear_cblinfun_apply)
    have 3: \<open>bounded_clinear (\<lambda>a. extg2 *\<^sub>V (a \<otimes>\<^sub>s \<phi>))\<close>
      by (intro bounded_clinear_cblinfun_apply bounded_clinear_tensor_ell22)
    have 4: \<open> bounded_clinear (\<lambda>a. a \<otimes>\<^sub>s (N *\<^sub>V \<phi>))\<close>
      by (auto intro!: bounded_clinear_tensor_ell22[THEN bounded_clinear_compose] bounded_clinear_cblinfun_apply)

    have eq_ket: \<open>extg2 *\<^sub>V (ket x \<otimes>\<^sub>s \<phi>) = ket x \<otimes>\<^sub>s (N *\<^sub>V \<phi>)\<close> for x
      apply (rule bounded_clinear_eq_on[where t=\<phi> and G=\<open>range ket\<close>])
      using 1 2 extg2_ket by auto
    show ?thesis 
      apply (rule bounded_clinear_eq_on[where t=\<psi> and G=\<open>range ket\<close>])
      using 3 4 eq_ket by auto
  qed

  have tensorMN_apply: \<open>tensorMN *\<^sub>V (\<psi> \<otimes>\<^sub>s \<phi>) = (M *\<^sub>V \<psi>) \<otimes>\<^sub>s (N *\<^sub>V \<phi>)\<close> for \<psi> \<phi>
    by (simp add: extg1_apply extg2_apply tensorMN_def)

  have \<open>cblinfun_extension_exists (range ket) (\<lambda>k. case inv ket k of (x, y) \<Rightarrow> (M *\<^sub>V ket x) \<otimes>\<^sub>s (N *\<^sub>V ket y))\<close>
    apply (rule cblinfun_extension_existsI[where B=tensorMN])
    using tensorMN_apply[of \<open>ket _\<close> \<open>ket _\<close>] by auto

  then have otimes_ket: \<open>(M \<otimes>\<^sub>o N) *\<^sub>V (ket (a,c)) = (M *\<^sub>V ket a) \<otimes>\<^sub>s (N *\<^sub>V ket c)\<close> for a c
    by (simp add: tensor_op_def cblinfun_extension_apply)

  have tensorMN_otimes: \<open>M \<otimes>\<^sub>o N = tensorMN\<close>
    apply (rule_tac equal_ket) 
    using tensorMN_apply[of \<open>ket _\<close> \<open>ket _\<close>] 
    by (auto simp: otimes_ket)

  show otimes_apply: \<open>(M \<otimes>\<^sub>o N) *\<^sub>V (\<psi> \<otimes>\<^sub>s \<phi>) = (M *\<^sub>V \<psi>) \<otimes>\<^sub>s (N *\<^sub>V \<phi>)\<close> for \<psi> \<phi>
    by (simp add: tensorMN_apply tensorMN_otimes)

  show \<open>norm (M \<otimes>\<^sub>o N) = norm M * norm N\<close>
  proof (rule order.antisym)
    show \<open>norm (M \<otimes>\<^sub>o N) \<le> norm M * norm N\<close>
      apply (simp add: tensorMN_otimes tensorMN_def)
      by (smt (verit, best) mult_mono norm_cblinfun_compose norm_extg1 norm_extg2 norm_ge_zero)
    have \<open>norm (M \<otimes>\<^sub>o N) \<ge> norm M * norm N * \<epsilon>\<close> if \<open>\<epsilon> < 1\<close> and \<open>\<epsilon> > 0\<close> for \<epsilon>
    proof -
      obtain \<psi>a where 1: \<open>norm (M *\<^sub>V \<psi>a) \<ge> norm M * sqrt \<epsilon>\<close> and \<open>norm \<psi>a = 1\<close>
        apply atomize_elim
        apply (rule cblinfun_norm_approx_witness_mult[where \<epsilon>=\<open>sqrt \<epsilon>\<close> and A=M])
        using \<open>\<epsilon> < 1\<close> by auto
      obtain \<psi>b where 2: \<open>norm (N *\<^sub>V \<psi>b) \<ge> norm N * sqrt \<epsilon>\<close> and \<open>norm \<psi>b = 1\<close>
        apply atomize_elim
        apply (rule cblinfun_norm_approx_witness_mult[where \<epsilon>=\<open>sqrt \<epsilon>\<close> and A=N])
        using \<open>\<epsilon> < 1\<close> by auto
      have \<open>norm ((M \<otimes>\<^sub>o N) *\<^sub>V (\<psi>a \<otimes>\<^sub>s \<psi>b)) / norm (\<psi>a \<otimes>\<^sub>s \<psi>b) = norm ((M \<otimes>\<^sub>o N) *\<^sub>V (\<psi>a \<otimes>\<^sub>s \<psi>b))\<close>
        using \<open>norm \<psi>a = 1\<close> \<open>norm \<psi>b = 1\<close>
        by (simp add: norm_tensor_ell2) 
      also have \<open>\<dots> = norm (M *\<^sub>V \<psi>a) * norm (N *\<^sub>V \<psi>b)\<close>
        by (simp add: norm_tensor_ell2 otimes_apply)
      also from 1 2 have \<open>\<dots> \<ge> (norm M * sqrt \<epsilon>) * (norm N * sqrt \<epsilon>)\<close> (is \<open>_ \<ge> \<dots>\<close>)
        apply (rule mult_mono')
        using \<open>\<epsilon> > 0\<close> by auto
      also have \<open>\<dots> = norm M * norm N * \<epsilon>\<close>
        using \<open>\<epsilon> > 0\<close> by force
      finally show ?thesis
        using cblinfun_norm_geqI by blast
    qed
    then show \<open>norm (M \<otimes>\<^sub>o N) \<ge> norm M * norm N\<close>
      by (metis field_le_mult_one_interval mult.commute)
  qed
qed

lemma tensor_op_ket: \<open>tensor_op M N *\<^sub>V (ket (a,c)) = tensor_ell2 (M *\<^sub>V ket a) (N *\<^sub>V ket c)\<close>
  by (metis tensor_ell2_ket tensor_op_ell2)

lemma comp_tensor_op: "(tensor_op a b) o\<^sub>C\<^sub>L (tensor_op c d) = tensor_op (a o\<^sub>C\<^sub>L c) (b o\<^sub>C\<^sub>L d)"
  for a :: "'e ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2" and b :: "'f ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2" and
      c :: "'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'e ell2" and d :: "'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'f ell2"
  apply (rule equal_ket)
  apply (rename_tac ij, case_tac ij, rename_tac i j, hypsubst_thin)
  by (simp flip: tensor_ell2_ket add: tensor_op_ell2)

lemma tensor_op_left_add: \<open>(x + y) \<otimes>\<^sub>o b = x \<otimes>\<^sub>o b + y \<otimes>\<^sub>o b\<close>
  for x y :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2\<close> and b :: \<open>'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2\<close>
  apply (auto intro!: equal_ket simp: tensor_op_ket)
  by (simp add: plus_cblinfun.rep_eq tensor_ell2_add1 tensor_op_ket)

lemma tensor_op_right_add: \<open>b \<otimes>\<^sub>o (x + y) = b \<otimes>\<^sub>o x + b \<otimes>\<^sub>o y\<close>
  for x y :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2\<close> and b :: \<open>'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2\<close>
  apply (auto intro!: equal_ket simp: tensor_op_ket)
  by (simp add: plus_cblinfun.rep_eq tensor_ell2_add2 tensor_op_ket)

lemma tensor_op_scaleC_left: \<open>(c *\<^sub>C x) \<otimes>\<^sub>o b = c *\<^sub>C (x \<otimes>\<^sub>o b)\<close>
  for x :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2\<close> and b :: \<open>'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2\<close>
  by (auto intro!: equal_ket simp: tensor_op_ket tensor_ell2_scaleC1)

lemma tensor_op_scaleC_right: \<open>b \<otimes>\<^sub>o (c *\<^sub>C x) = c *\<^sub>C (b \<otimes>\<^sub>o x)\<close>
  for x :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2\<close> and b :: \<open>'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2\<close>
  by (auto intro!: equal_ket simp: tensor_op_ket tensor_ell2_scaleC2)

lemma tensor_op_bounded_cbilinear[simp]: \<open>bounded_cbilinear tensor_op\<close>
  by (auto intro!: bounded_cbilinear.intro exI[of _ 1]
      simp: tensor_op_left_add tensor_op_right_add tensor_op_scaleC_left tensor_op_scaleC_right tensor_op_norm)

lemma tensor_op_cbilinear[simp]: \<open>cbilinear tensor_op\<close>
  by (simp add: bounded_cbilinear.add_left bounded_cbilinear.add_right cbilinear_def clinearI tensor_op_scaleC_left tensor_op_scaleC_right)

lemma tensor_butter: \<open>butterket i j \<otimes>\<^sub>o butterket k l = butterket (i,k) (j,l)\<close>
  for i :: "_" and j :: "_" and k :: "_" and l :: "_"
  apply (rule equal_ket, rename_tac x, case_tac x)
  apply (auto simp flip: tensor_ell2_ket simp: tensor_op_ell2 butterfly_def)
  by (auto simp: tensor_ell2_scaleC1 tensor_ell2_scaleC2)

lemma cspan_tensor_op_butter: \<open>cspan {tensor_op (butterket i j) (butterket k l)| (i::_::finite) (j::_::finite) (k::_::finite) (l::_::finite). True} = UNIV\<close>
  unfolding tensor_butter
  apply (subst cspan_butterfly_ket[symmetric])
  by (metis surj_pair)

lemma cindependent_tensor_op_butter: \<open>cindependent {tensor_op (butterket i j) (butterket k l)| i j k l. True}\<close>
  unfolding tensor_butter
  using cindependent_butterfly_ket
  by (smt (z3) Collect_mono_iff complex_vector.independent_mono)

lift_definition right_amplification :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2) \<Rightarrow>\<^sub>C\<^sub>L (('a\<times>'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('b\<times>'c) ell2)\<close> is
  \<open>\<lambda>a. a \<otimes>\<^sub>o id_cblinfun\<close>
  by (simp add: bounded_cbilinear.bounded_clinear_left)

lift_definition left_amplification :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2) \<Rightarrow>\<^sub>C\<^sub>L (('c\<times>'a) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('c\<times>'b) ell2)\<close> is
  \<open>\<lambda>a. id_cblinfun \<otimes>\<^sub>o a\<close>
  by (simp add: bounded_cbilinear.bounded_clinear_right)

lift_definition tensor_ell2_left :: \<open>'a ell2 \<Rightarrow> ('b ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a\<times>'b) ell2)\<close> is
  \<open>\<lambda>\<psi> \<phi>. \<psi> \<otimes>\<^sub>s \<phi>\<close>
  by (simp add: bounded_cbilinear.bounded_clinear_right bounded_cbilinear_tensor_ell2)

lift_definition tensor_ell2_right :: \<open>'a ell2 \<Rightarrow> ('b ell2 \<Rightarrow>\<^sub>C\<^sub>L ('b\<times>'a) ell2)\<close> is
  \<open>\<lambda>\<psi> \<phi>. \<phi> \<otimes>\<^sub>s \<psi>\<close>
  by (simp add: bounded_clinear_tensor_ell22)

typedef (overloaded) ('a,'b) cblinfun_sot = \<open>UNIV :: ('a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector) set\<close> ..
setup_lifting type_definition_cblinfun_sot

instantiation cblinfun_sot :: (complex_normed_vector, complex_normed_vector) complex_vector begin
lift_definition scaleC_cblinfun_sot :: \<open>complex \<Rightarrow> ('a, 'b) cblinfun_sot \<Rightarrow> ('a, 'b) cblinfun_sot\<close> 
  is \<open>scaleC\<close> .
lift_definition uminus_cblinfun_sot :: \<open>('a, 'b) cblinfun_sot \<Rightarrow> ('a, 'b) cblinfun_sot\<close> is uminus .
lift_definition zero_cblinfun_sot :: \<open>('a, 'b) cblinfun_sot\<close> is 0 .
lift_definition minus_cblinfun_sot :: \<open>('a, 'b) cblinfun_sot \<Rightarrow> ('a, 'b) cblinfun_sot \<Rightarrow> ('a, 'b) cblinfun_sot\<close> is minus .
lift_definition plus_cblinfun_sot :: \<open>('a, 'b) cblinfun_sot \<Rightarrow> ('a, 'b) cblinfun_sot \<Rightarrow> ('a, 'b) cblinfun_sot\<close> is plus .
lift_definition scaleR_cblinfun_sot :: \<open>real \<Rightarrow> ('a, 'b) cblinfun_sot \<Rightarrow> ('a, 'b) cblinfun_sot\<close> is scaleR .
instance
  apply (intro_classes; transfer)
  by (auto simp add: scaleR_scaleC scaleC_add_right scaleC_add_left)
end

instantiation cblinfun_sot :: (complex_normed_vector, complex_normed_vector) topological_space begin
lift_definition open_cblinfun_sot :: \<open>('a, 'b) cblinfun_sot set \<Rightarrow> bool\<close> is \<open>openin cstrong_operator_topology\<close> .
instance
proof intro_classes
  show \<open>open (UNIV :: ('a,'b) cblinfun_sot set)\<close>
    apply transfer
    by (metis cstrong_operator_topology_topspace openin_topspace)
  show \<open>open S \<Longrightarrow> open T \<Longrightarrow> open (S \<inter> T)\<close> for S T :: \<open>('a,'b) cblinfun_sot set\<close>
    apply transfer by auto
  show \<open>\<forall>S\<in>K. open S \<Longrightarrow> open (\<Union> K)\<close> for K :: \<open>('a,'b) cblinfun_sot set set\<close>
    apply transfer by auto
qed
end

lemma transfer_nhds_cstrong_operator_topology[transfer_rule]:
  includes lifting_syntax
  shows \<open>(cr_cblinfun_sot ===> rel_filter cr_cblinfun_sot) (nhdsin cstrong_operator_topology) nhds\<close>
  unfolding nhds_def nhdsin_def
  apply (simp add: cstrong_operator_topology_topspace)
  by transfer_prover

(* lemma [transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique S\<close>
  shows \<open>(rel_filter S ===> rel_filter S ===> (=)) (\<le>) (\<le>)\<close>
  unfolding le_filter_def
  by transfer_prover *)

(* TODO move *)
lemma limitin_pullback_topology: 
  \<open>limitin (pullback_topology A g T) f l F \<longleftrightarrow> l\<in>A \<and> (\<forall>\<^sub>F x in F. f x \<in> A) \<and> limitin T (g o f) (g l) F\<close>
  apply (simp add: topspace_pullback_topology limitin_def openin_pullback_topology imp_ex flip: ex_simps(1))
  apply rule
   apply simp
   apply safe
  using eventually_mono apply fastforce
   apply (simp add: eventually_conj_iff)
  by (simp add: eventually_conj_iff)

lemma limitin_cstrong_operator_topology: 
  \<open>limitin cstrong_operator_topology f l F \<longleftrightarrow> (((*\<^sub>V) \<circ> f) \<longlongrightarrow> (*\<^sub>V) l) F\<close>
  by (simp add: cstrong_operator_topology_def limitin_pullback_topology)

lemma tendsto_coordinatewise: \<open>(f \<longlongrightarrow> l) F \<longleftrightarrow> (\<forall>x. ((\<lambda>i. f i x) \<longlongrightarrow> l x) F)\<close>
proof (intro iffI allI)
  assume asm: \<open>(f \<longlongrightarrow> l) F\<close>
  then show \<open>((\<lambda>i. f i x) \<longlongrightarrow> l x) F\<close> for x
    apply (rule continuous_on_tendsto_compose[where s=UNIV, rotated])
    by auto
next
  assume asm: \<open>(\<forall>x. ((\<lambda>i. f i x) \<longlongrightarrow> l x) F)\<close>
  show \<open>(f \<longlongrightarrow> l) F\<close>
  proof (unfold tendsto_def, intro allI impI)
    fix S assume \<open>open S\<close> and \<open>l \<in> S\<close>
    from product_topology_open_contains_basis[OF \<open>open S\<close>[unfolded open_fun_def] \<open>l \<in> S\<close>]
    obtain U where lU: \<open>l \<in> Pi UNIV U\<close> and openU: \<open>\<And>x. open (U x)\<close> and finiteD: \<open>finite {x. U x \<noteq> UNIV}\<close> and US: \<open>Pi UNIV U \<subseteq> S\<close>
      by (auto simp add: PiE_UNIV_domain)

    define D where \<open>D = {x. U x \<noteq> UNIV}\<close>
    with finiteD have finiteD: \<open>finite D\<close>
      by simp
    have PiUNIV: \<open>t \<in> Pi UNIV U \<longleftrightarrow> (\<forall>x\<in>D. t x \<in> U x)\<close> for t
      using D_def by blast

    have f_Ui: \<open>\<forall>\<^sub>F i in F. f i x \<in> U x\<close> for x
      using asm[rule_format, of x] openU[of x]
      using lU topological_tendstoD by fastforce

    have \<open>\<forall>\<^sub>F x in F. \<forall>i\<in>D. f x i \<in> U i\<close>
      using finiteD
    proof induction
      case empty
      then show ?case
        by simp
    next
      case (insert x F)
      with f_Ui show ?case
        by (simp add: eventually_conj_iff)
    qed

    then show \<open>\<forall>\<^sub>F x in F. f x \<in> S\<close>
      using US by (simp add: PiUNIV eventually_mono in_mono)
  qed
qed

lemma filterlim_parametric[transfer_rule]: 
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_unique S\<close>
  shows \<open>((R ===> S) ===> rel_filter S ===> rel_filter R ===> (=)) filterlim filterlim\<close>
  using filtermap_parametric[transfer_rule] le_filter_parametric[transfer_rule] apply fail?
  unfolding filterlim_def
  by transfer_prover

lemma transfer_tendsto_cstrong_operator_topology[transfer_rule]: 
  includes lifting_syntax
  shows \<open>((R ===> cr_cblinfun_sot) ===> cr_cblinfun_sot ===> rel_filter R ===> (=)) (limitin cstrong_operator_topology) tendsto\<close>
  apply transfer_prover_start
    apply transfer_step
   apply transfer_step
  oops

lemma filterlim_cstrong_operator_topology: \<open>filterlim f (nhdsin cstrong_operator_topology l) = limitin cstrong_operator_topology f l\<close>
  unfolding limitin_def filterlim_def eventually_filtermap le_filter_def eventually_nhdsin cstrong_operator_topology_topspace
  apply (intro ext)
  apply safe
    apply simp
   apply meson
  by (metis (mono_tags, lifting) eventually_mono)

instance cblinfun_sot :: (complex_normed_vector, complex_normed_vector) t2_space
  apply intro_classes
  apply transfer
  apply auto
  sorry

definition rel_topology :: \<open>('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a topology \<Rightarrow> 'b topology \<Rightarrow> bool)\<close> where
  \<open>rel_topology R S T \<longleftrightarrow> (rel_fun (rel_set R) (=)) (openin S) (openin T)\<close>

lemma transfer_euclidean_cstrong_operator_topology[transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_topology cr_cblinfun_sot) cstrong_operator_topology euclidean\<close>
  apply (auto simp: rel_topology_def cr_cblinfun_sot_def rel_set_def
intro!: rel_funI)
   apply transfer
   apply auto
   apply (meson openin_subopen subsetI)
  apply transfer
  apply auto
  by (meson openin_subopen subsetI)

lemma [transfer_rule]:
  includes lifting_syntax
  (* assumes [transfer_rule]: \<open>bi_unique S\<close> *)
  shows \<open>(rel_topology R ===> rel_set R ===> (=)) openin openin\<close>
  by (auto simp add: rel_fun_def rel_topology_def)

lemma [transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_total R\<close>
  shows \<open>(rel_topology R ===> rel_set R) topspace topspace\<close>
  unfolding topspace_def
  by transfer_prover

lemma [transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: \<open>bi_total S\<close>
  assumes [transfer_rule]: \<open>bi_unique S\<close>
  assumes [transfer_rule]: \<open>bi_total R\<close>
  assumes [transfer_rule]: \<open>bi_unique R\<close>
  shows \<open>(rel_topology R ===> rel_topology S ===> (R ===> S) ===> (=)) continuous_map continuous_map\<close>
  unfolding continuous_map_def
  by transfer_prover

lemma openin_cstrong_operator_topology: \<open>openin cstrong_operator_topology U \<longleftrightarrow> (\<exists>V. open V \<and> U = (*\<^sub>V) -` V)\<close>
  by (simp add: cstrong_operator_topology_def openin_pullback_topology)

lemma aux1: 
  assumes \<open>continuous_on UNIV f\<close>
  shows \<open>filtercomap f (nhds (f x)) \<ge> nhds x\<close>
  apply ( simp add: le_filter_def filter_eq_iff eventually_filtercomap  
eventually_inf_principal eventually_nhds
)
  apply safe
   apply (rule_tac x=\<open>f -` S\<close> in exI)
   apply safe
  using assms open_vimage apply blast
    apply blast
  apply blast
  by -

(* lemma aux2: 
  (* assumes \<open>continuous_on UNIV f\<close> *)
  assumes \<open>inj f\<close>
  shows \<open>filtercomap f (nhds (f x)) \<le> nhds x \<sqinter> principal XXX\<close>
  apply ( simp add: le_filter_def filter_eq_iff eventually_filtercomap  
eventually_inf_principal eventually_nhds
)
  apply safe
  apply (rule_tac x=\<open>P o inv f\<close> in exI)
  apply autox *)


lemma cstrong_operator_topology_plus_cont: \<open>LIM x nhdsin cstrong_operator_topology a \<times>\<^sub>F nhdsin cstrong_operator_topology b.
            fst x + snd x :> nhdsin cstrong_operator_topology (a + b)\<close>
proof -
  have 1: \<open>nhdsin cstrong_operator_topology a = filtercomap cblinfun_apply (nhds (cblinfun_apply a))\<close>
    for a :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
    by (auto simp add: filter_eq_iff eventually_filtercomap eventually_nhds eventually_nhdsin
        cstrong_operator_topology_topspace openin_cstrong_operator_topology)

  have \<open>(((*\<^sub>V) \<circ> (\<lambda>x. fst x + snd x)) \<longlongrightarrow> (*\<^sub>V) (a + b))
     (nhdsin cstrong_operator_topology a \<times>\<^sub>F nhdsin cstrong_operator_topology b)\<close>
  proof (unfold tendsto_def, intro allI impI)
    fix S assume \<open>open S\<close> and \<open>(*\<^sub>V) (a + b) \<in> S\<close>
    obtain U where \<open>(*\<^sub>V) (a + b) \<in> Pi\<^sub>E UNIV U\<close> and openU: \<open>\<forall>i. openin euclidean (U i)\<close>
      and finiteD: \<open>finite {i. U i \<noteq> topspace euclidean}\<close> and US: \<open>Pi\<^sub>E UNIV U \<subseteq> S\<close>
      using product_topology_open_contains_basis[OF \<open>open S\<close>[unfolded open_fun_def] \<open>(*\<^sub>V) (a + b) \<in> S\<close>]
      by auto

    define D where \<open>D = {i. U i \<noteq> UNIV}\<close>
    with finiteD have \<open>finite D\<close>
      by auto

    from openU have openU: \<open>open (U i)\<close> for i
      by auto

    have \<open>a *\<^sub>V i + b *\<^sub>V i \<in> U i\<close> for i
      by (metis PiE_mem \<open>(*\<^sub>V) (a + b) \<in> Pi\<^sub>E UNIV U\<close> iso_tuple_UNIV_I plus_cblinfun.rep_eq)

    then have \<open>\<forall>\<^sub>F x in nhds (a *\<^sub>V i) \<times>\<^sub>F nhds (b *\<^sub>V i).
            (fst x + snd x) \<in> U i\<close> for i
      using openU tendsto_add_Pair tendsto_def by fastforce

(*     then obtain Ua Ub where \<open>open (Ua i)\<close> \<open>open (Ub i)\<close> \<open>a *\<^sub>V i \<in> Ua i\<close> \<open>a *\<^sub>V i \<in> Ub i\<close>
      and \<open>(\<forall>x y. x\<in>Ua i \<longrightarrow> y\<in>Ub i \<longrightarrow> fst (x, y) + snd (x, y) \<in> U i)\<close> for i
      unfolding eventually_prod_filter
      apply atomize_elim
      apply (simp flip: all_conj_distrib add: choice_iff)
      apply (subst choice_iff[symmetric])
      apply (subst choice_iff[symmetric])
      apply auto
      by metis *)

    then obtain Pa Pb where \<open>eventually (Pa i) (nhds (a *\<^sub>V i))\<close> and \<open>eventually (Pb i) (nhds (b *\<^sub>V i))\<close>
      and PaPb_plus: \<open>(\<forall>x y. Pa i x \<longrightarrow> Pb i y \<longrightarrow> fst (x, y) + snd (x, y) \<in> U i)\<close> 
    for i
      unfolding eventually_prod_filter
      by metis

    from \<open>\<And>i. eventually (Pa i) (nhds (a *\<^sub>V i))\<close>
    obtain Ua where \<open>open (Ua i)\<close> and a_Ua: \<open>a *\<^sub>V i \<in> Ua i\<close> and Ua_Pa: \<open>Ua i \<subseteq> Collect (Pa i)\<close> for i
      unfolding eventually_nhds
      apply atomize_elim
      by (metis mem_Collect_eq subsetI)
    from \<open>\<And>i. eventually (Pb i) (nhds (b *\<^sub>V i))\<close>
    obtain Ub where \<open>open (Ub i)\<close> and b_Ub: \<open>b *\<^sub>V i \<in> Ub i\<close> and Ub_Pb: \<open>Ub i \<subseteq> Collect (Pb i)\<close> for i
      unfolding eventually_nhds
      apply atomize_elim
      by (metis mem_Collect_eq subsetI)
    have UaUb_plus: \<open>x \<in> Ua i \<Longrightarrow> y \<in> Ub i \<Longrightarrow> x + y \<in> U i\<close> for i x y
      by (metis PaPb_plus Ua_Pa Ub_Pb fst_eqD mem_Collect_eq snd_conv subsetD)

    define Ua' where \<open>Ua' i = (if i\<in>D then Ua i else UNIV)\<close> for i
    define Ub' where \<open>Ub' i = (if i\<in>D then Ub i else UNIV)\<close> for i

    have Ua'_UNIV: \<open>U i = UNIV \<Longrightarrow> Ua' i = UNIV\<close> for i
      by (simp add: D_def Ua'_def)
    have Ub'_UNIV: \<open>U i = UNIV \<Longrightarrow> Ub' i = UNIV\<close> for i
      by (simp add: D_def Ub'_def)
    have [simp]: \<open>open (Ua' i)\<close> for i
      by (simp add: Ua'_def \<open>open (Ua _)\<close>)
    have [simp]: \<open>open (Ub' i)\<close> for i
      by (simp add: Ub'_def \<open>open (Ub _)\<close>)
    have a_Ua': \<open>a *\<^sub>V i \<in> Ua' i\<close> for i
      by (simp add: Ua'_def a_Ua)
    have b_Ub': \<open>b *\<^sub>V i \<in> Ub' i\<close> for i
      by (simp add: Ub'_def b_Ub)
    have UaUb'_plus: \<open>a \<in> Ua' i \<Longrightarrow> b \<in> Ub' i \<Longrightarrow> a + b \<in> U i\<close> for i a b
      apply (cases \<open>i \<in> D\<close>)
      using UaUb_plus by (auto simp add: Ua'_def  Ub'_def D_def)

    define Ua'' where \<open>Ua'' = Pi UNIV Ua'\<close>
    define Ub'' where \<open>Ub'' = Pi UNIV Ub'\<close>

    have \<open>open Ua''\<close>
      using finiteD Ua'_UNIV
      apply (auto simp add: openin_cstrong_operator_topology open_fun_def Ua''_def PiE_UNIV_domain
          openin_product_topology_alt D_def intro!: exI[where x=\<open>Ua'\<close>])
      by (meson Collect_mono rev_finite_subset)
    have \<open>open Ub''\<close>
      using finiteD Ub'_UNIV
      apply (auto simp add: openin_cstrong_operator_topology open_fun_def Ub''_def PiE_UNIV_domain
          openin_product_topology_alt D_def intro!: exI[where x=\<open>Ub'\<close>])
      by (meson Collect_mono rev_finite_subset)
    have a_Ua'': \<open>cblinfun_apply a \<in> Ua''\<close>
      by (simp add: Ua''_def a_Ua')
    have b_Ub'': \<open>cblinfun_apply b \<in> Ub''\<close>
      by (simp add: Ub''_def b_Ub')
    have UaUb''_plus: \<open>a \<in> Ua'' \<Longrightarrow> b \<in> Ub'' \<Longrightarrow> a i + b i \<in> U i\<close> for i a b
      using UaUb'_plus apply (auto simp add: Ua''_def  Ub''_def)
      by blast

    define Ua''' where \<open>Ua''' = cblinfun_apply -` Ua''\<close>
    define Ub''' where \<open>Ub''' = cblinfun_apply -` Ub''\<close>
    have \<open>openin cstrong_operator_topology Ua'''\<close>
      using \<open>open Ua''\<close> by (auto simp: openin_cstrong_operator_topology Ua'''_def)
    have \<open>openin cstrong_operator_topology Ub'''\<close>
      using \<open>open Ub''\<close> by (auto simp: openin_cstrong_operator_topology Ub'''_def)
    have a_Ua'': \<open>a \<in> Ua'''\<close>
      by (simp add: Ua'''_def a_Ua'')
    have b_Ub'': \<open>b \<in> Ub'''\<close>
      by (simp add: Ub'''_def b_Ub'')
    have UaUb'''_plus: \<open>a \<in> Ua''' \<Longrightarrow> b \<in> Ub''' \<Longrightarrow> a *\<^sub>V i + b *\<^sub>V i \<in> U i\<close> for i a b
      by (simp add: Ua'''_def UaUb''_plus Ub'''_def)

    define Pa' where \<open>Pa' a \<longleftrightarrow> a \<in> Ua'''\<close> for a
    define Pb' where \<open>Pb' b \<longleftrightarrow> b \<in> Ub'''\<close> for b

    have Pa'_nhd: \<open>eventually Pa' (nhdsin cstrong_operator_topology a)\<close>
      using \<open>openin cstrong_operator_topology Ua'''\<close>
      by (auto simp add: Pa'_def eventually_nhdsin intro!: exI[of _ \<open>Ua'''\<close>] a_Ua'')
    have Pb'_nhd: \<open>eventually Pb' (nhdsin cstrong_operator_topology b)\<close>
      using \<open>openin cstrong_operator_topology Ub'''\<close>
      by (auto simp add: Pb'_def eventually_nhdsin intro!: exI[of _ \<open>Ub'''\<close>] b_Ub'')
    have Pa'Pb'_plus: \<open>((*\<^sub>V) \<circ> (\<lambda>x. fst x + snd x)) (a, b) \<in> S\<close> if \<open>Pa' a\<close> \<open>Pb' b\<close> for a b
      using that UaUb'''_plus US
      by (auto simp add: Pa'_def Pb'_def PiE_UNIV_domain Pi_iff cblinfun.add_left[THEN ext])

    show \<open>\<forall>\<^sub>F x in nhdsin cstrong_operator_topology a \<times>\<^sub>F nhdsin cstrong_operator_topology b.
            ((*\<^sub>V) \<circ> (\<lambda>x. fst x + snd x)) x \<in> S\<close>
      using Pa'_nhd Pb'_nhd Pa'Pb'_plus
      unfolding eventually_prod_filter
      apply (rule_tac exI[of _ Pa'])
      apply (rule_tac exI[of _ Pb'])
      by simp
  qed
  then show ?thesis
    unfolding 1 filterlim_filtercomap_iff by -
qed

instance cblinfun_sot :: (complex_normed_vector, complex_normed_vector) topological_group_add
proof intro_classes
  show \<open>((\<lambda>x. fst x + snd x) \<longlongrightarrow> a + b) (nhds a \<times>\<^sub>F nhds b)\<close> for a b :: \<open>('a,'b) cblinfun_sot\<close>
    apply transfer
    by (rule cstrong_operator_topology_plus_cont)

  have *: \<open>continuous_map cstrong_operator_topology cstrong_operator_topology uminus\<close>
    apply (subst continuous_on_cstrong_operator_topo_iff_coordinatewise)
    apply (rewrite at \<open>(\<lambda>y. - y *\<^sub>V x)\<close> in \<open>\<forall>x. \<hole>\<close> to \<open>(\<lambda>y. y *\<^sub>V - x)\<close> DEADID.rel_mono_strong)
    by (auto simp: cstrong_operator_topology_continuous_evaluation cblinfun.minus_left cblinfun.minus_right)
  show \<open>(uminus \<longlongrightarrow> - a) (nhds a)\<close> for a :: \<open>('a,'b) cblinfun_sot\<close>
    apply (subst tendsto_at_iff_tendsto_nhds[symmetric])
    apply (subst isCont_def[symmetric])
    apply (rule continuous_on_interior[where s=UNIV])
     apply (subst continuous_map_iff_continuous2[symmetric])
     apply transfer
    using * by auto
qed

lemma limitin_closure_of:
  assumes \<open>limitin T f c F\<close>
  assumes \<open>range f \<subseteq> S\<close>
  assumes \<open>\<not> trivial_limit F\<close>
  shows \<open>c \<in> T closure_of S\<close>
  by (smt (verit, ccfv_SIG) assms(1) assms(2) assms(3) eventually_happens' in_closure_of limitin_def rangeI subsetD)

lemma limitin_closedin:
  assumes \<open>limitin T f c F\<close>
  assumes \<open>range f \<subseteq> S\<close>
  assumes \<open>closedin T S\<close>
  assumes \<open>\<not> trivial_limit F\<close>
  shows \<open>c \<in> S\<close>
  by (metis assms(1) assms(2) assms(3) assms(4) closure_of_eq limitin_closure_of)


lemma infsum_bounded_clinear:
  assumes \<open>bounded_clinear f\<close>
  assumes \<open>g summable_on S\<close>
  shows \<open>infsum (f \<circ> g) S = f (infsum g S)\<close>
  apply (rule infsum_comm_additive)
  using assms cblinfun_apply_induct cblinfun.additive_right
  by (auto simp: clinear_continuous_within)

lemma has_sum_bounded_clinear: 
  assumes \<open>bounded_clinear f\<close>
  assumes \<open>has_sum g S x\<close>
  shows \<open>has_sum (f o g) S (f x)\<close>
  apply (rule has_sum_comm_additive)
  using assms cblinfun_apply_induct cblinfun.additive_right apply auto
  using clinear_continuous_within isCont_def by fastforce

lemma abs_summable_on_bounded_clinear: 
  assumes \<open>bounded_clinear f\<close>
  assumes \<open>g abs_summable_on S\<close>
  shows \<open>(f o g) abs_summable_on S\<close>
  sorry

lemma infsum_cblinfun_apply:
  assumes \<open>g summable_on S\<close>
  shows \<open>infsum (\<lambda>x. A *\<^sub>V g x) S = A *\<^sub>V (infsum g S)\<close>
  apply (rule infsum_bounded_clinear[unfolded o_def, of \<open>cblinfun_apply A\<close>])
  using assms by (auto simp add: bounded_cbilinear.bounded_clinear_right bounded_cbilinear_cblinfun_apply)

lemma has_sum_cblinfun_apply:
  assumes \<open>has_sum g S x\<close>
  shows \<open>has_sum (\<lambda>x. A *\<^sub>V g x) S (A *\<^sub>V x)\<close>
  apply (rule has_sum_bounded_clinear[unfolded o_def, of \<open>cblinfun_apply A\<close>])
  using assms by (auto simp add: bounded_cbilinear.bounded_clinear_right bounded_cbilinear_cblinfun_apply)

lemma abs_summable_on_cblinfun_apply:
  assumes \<open>g abs_summable_on S\<close>
  shows \<open>(\<lambda>x. A *\<^sub>V g x) abs_summable_on S\<close>
  sorry

lemma has_sum_id_tensor_butterfly_ket: \<open>has_sum (\<lambda>i. (id_cblinfun \<otimes>\<^sub>o selfbutterket i) *\<^sub>V \<psi>) UNIV \<psi>\<close>
  sorry

(* TODO useful? TODO iff? *)
lemma aux2: \<open>nhds a \<sqinter> principal A \<noteq> \<bottom>\<close> if \<open>a \<in> closure A\<close>
  apply (cases \<open>a \<in> A\<close>)
   apply (auto simp:  filter_eq_iff eventually_inf eventually_principal eventually_nhds) apply blast
  apply (subgoal_tac \<open>a islimpt A\<close>)
   apply ( simp add:  filter_eq_iff eventually_inf eventually_principal eventually_nhds islimpt_def)
   apply meson
  by (simp add: islimpt_in_closure that)

lemma limit_in_closure:
  assumes lim: \<open>(f \<longlongrightarrow> x) F\<close>
  assumes nt: \<open>F \<noteq> \<bottom>\<close>
  assumes inA: \<open>\<forall>\<^sub>F x in F. f x \<in> A\<close>
  shows \<open>x \<in> closure A\<close>
  apply (cases \<open>x \<in> A\<close>)
   apply (meson closure_subset in_mono)
  apply (auto simp: closure_def filterlim_def islimpt_def le_filter_def eventually_filtermap
      eventually_nhds image_def)
  by (smt (verit, ccfv_threshold) assms(1) assms(3) eventually_elim2 nt tendsto_def trivial_limit_eq)

lemma sot_closure_is_csubspace[simp]:
  fixes A::"('a::complex_normed_vector, 'b::complex_normed_vector) cblinfun_sot set"
  assumes \<open>csubspace A\<close>
  shows \<open>csubspace (closure A)\<close>
proof (rule complex_vector.subspaceI)
  show \<open>0 \<in> closure A\<close>
    by (simp add: assms closure_def complex_vector.subspace_0)
  show \<open>x + y \<in> closure A\<close> if \<open>x \<in> closure A\<close> \<open>y \<in> closure A\<close> for x y
  proof -
    define FF where \<open>FF = ((nhds x \<sqinter> principal A) \<times>\<^sub>F (nhds y \<sqinter> principal A))\<close>
    have nt: \<open>FF \<noteq> bot\<close>
      by (simp add: aux2 prod_filter_eq_bot that(1) that(2) FF_def)
    have \<open>\<forall>\<^sub>F x in FF. fst x \<in> A\<close>
      unfolding FF_def
      by (smt (verit, ccfv_SIG) eventually_prod_filter fst_conv inf_sup_ord(2) le_principal)
    moreover have \<open>\<forall>\<^sub>F x in FF. snd x \<in> A\<close>
      unfolding FF_def
      by (smt (verit, ccfv_SIG) eventually_prod_filter snd_conv inf_sup_ord(2) le_principal)
    ultimately have FF_plus: \<open>\<forall>\<^sub>F x in FF. fst x + snd x \<in> A\<close>
      by (smt (verit, best) assms complex_vector.subspace_add eventually_elim2)

    have \<open>(fst \<longlongrightarrow> x) ((nhds x \<sqinter> principal A) \<times>\<^sub>F (nhds y \<sqinter> principal A))\<close>
      apply (simp add: filterlim_def)
      using filtermap_fst_prod_filter
      using le_inf_iff by blast
    moreover have \<open>(snd \<longlongrightarrow> y) ((nhds x \<sqinter> principal A) \<times>\<^sub>F (nhds y \<sqinter> principal A))\<close>
      apply (simp add: filterlim_def)
      using filtermap_snd_prod_filter
      using le_inf_iff by blast
    ultimately have \<open>(id \<longlongrightarrow> (x,y)) FF\<close>
      by (simp add: filterlim_def nhds_prod prod_filter_mono FF_def)

    moreover note tendsto_add_Pair[of x y]
    ultimately have \<open>(((\<lambda>x. fst x + snd x) o id) \<longlongrightarrow> (\<lambda>x. fst x + snd x) (x,y)) FF\<close>
      unfolding filterlim_def nhds_prod
      by (smt (verit, best) filterlim_compose filterlim_def filterlim_filtermap fst_conv snd_conv tendsto_compose_filtermap)

    then have \<open>((\<lambda>x. fst x + snd x) \<longlongrightarrow> (x+y)) FF\<close>
      by simp
    then show \<open>x + y \<in> closure A\<close>
      using nt FF_plus by (rule limit_in_closure)
  qed
  show \<open>c *\<^sub>C x \<in> closure A\<close> if \<open>x \<in> closure A\<close> for x c
    by -
qed

lemma [transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_set cr_cblinfun_sot ===> (=)) csubspace csubspace\<close>
  unfolding complex_vector.subspace_def
  by transfer_prover

lemma [transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_set cr_cblinfun_sot ===> (=)) (closedin cstrong_operator_topology) closed\<close>
  apply (simp add: closed_def[abs_def] closedin_def[abs_def] cstrong_operator_topology_topspace Compl_eq_Diff_UNIV)
  by transfer_prover

lemma [transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_set cr_cblinfun_sot ===> rel_set cr_cblinfun_sot) (Abstract_Topology.closure_of cstrong_operator_topology) closure\<close>
  apply (subst closure_of_hull[where X=cstrong_operator_topology, unfolded cstrong_operator_topology_topspace, simplified, abs_def])
  apply (subst closure_hull[abs_def])
  unfolding hull_def
  by transfer_prover

lemma sot_closure_is_csubspace'[simp]:
  fixes A::"('a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector) set"
  assumes \<open>csubspace A\<close>
  shows \<open>csubspace (cstrong_operator_topology closure_of A)\<close>
  using sot_closure_is_csubspace[of \<open>Abs_cblinfun_sot ` A\<close>] assms
  apply (transfer fixing: A)
  by simp

lemma has_sum_closed_cstrong_operator_topology:
  assumes aA: \<open>\<And>i. a i \<in> A\<close>
  assumes closed: \<open>closedin cstrong_operator_topology A\<close>
  assumes subspace: \<open>csubspace A\<close>
  assumes has_sum: \<open>\<And>\<psi>. has_sum (\<lambda>i. a i *\<^sub>V \<psi>) I (b *\<^sub>V \<psi>)\<close>
  shows \<open>b \<in> A\<close>
proof -
  have 1: \<open>range (sum a) \<subseteq> A\<close>
  proof -
    have \<open>sum a X \<in> A\<close> for X
      apply (induction X rule:infinite_finite_induct)
      by (auto simp add: subspace complex_vector.subspace_0 aA complex_vector.subspace_add)
    then show ?thesis
      by auto
  qed

  from has_sum
  have \<open>((\<lambda>F. \<Sum>i\<in>F. a i *\<^sub>V \<psi>) \<longlongrightarrow> b *\<^sub>V \<psi>) (finite_subsets_at_top I)\<close> for \<psi>
    using has_sum_def by blast
  then have \<open>limitin cstrong_operator_topology (\<lambda>F. \<Sum>i\<in>F. a i) b (finite_subsets_at_top I)\<close>
    by (auto simp add: limitin_cstrong_operator_topology tendsto_coordinatewise cblinfun.sum_left)
  then show \<open>b \<in> A\<close>
    using 1 closed apply (rule limitin_closedin)
    by simp
qed

(* TODO infinite version. Needs different proof because the butterflies only span the compact operators (I think). 
  Takesaki, p.185, (10) basically is this, I think.
*)
lemma tensor_op_dense: \<open>cstrong_operator_topology closure_of (cspan {a \<otimes>\<^sub>o b | a b. True}) = UNIV\<close>
proof (intro order.antisym subset_UNIV subsetI)
  fix c :: \<open>('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('c \<times> 'd) ell2\<close>
  define c' where \<open>c' i j = (tensor_ell2_right (ket i))* o\<^sub>C\<^sub>L c o\<^sub>C\<^sub>L tensor_ell2_right (ket j)\<close> for i j
  define AB :: \<open>(('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('c \<times> 'd) ell2) set\<close> where
    \<open>AB = cstrong_operator_topology closure_of (cspan {a \<otimes>\<^sub>o b | a b. True})\<close>

  have [simp]: \<open>closedin cstrong_operator_topology AB\<close>
    by (simp add: AB_def)
  have [simp]: \<open>csubspace AB\<close>
    using AB_def sot_closure_is_csubspace' by blast

  have *: \<open>c' i j \<otimes>\<^sub>o butterket i j = (id_cblinfun \<otimes>\<^sub>o selfbutterket i) o\<^sub>C\<^sub>L c o\<^sub>C\<^sub>L (id_cblinfun \<otimes>\<^sub>o selfbutterket j)\<close> for i j
    by -

  have \<open>c' i j \<otimes>\<^sub>o butterket i j \<in> AB\<close> for i j
  proof -
    have \<open>c' i j \<otimes>\<^sub>o butterket i j \<in> {a \<otimes>\<^sub>o b | a b. True}\<close>
      by auto
    also have \<open>\<dots> \<subseteq> cspan \<dots>\<close>
      by (simp add: complex_vector.span_superset)
    also have \<open>\<dots> \<subseteq> cstrong_operator_topology closure_of \<dots>\<close>
      apply (rule closure_of_subset)
      by (simp add: cstrong_operator_topology_topspace)
    also have \<open>\<dots> = AB\<close>
      by (simp add: AB_def)
    finally show ?thesis
      by simp
  qed
  with * have AB1: \<open>(id_cblinfun \<otimes>\<^sub>o selfbutterket i) o\<^sub>C\<^sub>L c o\<^sub>C\<^sub>L (id_cblinfun \<otimes>\<^sub>o selfbutterket j) \<in> AB\<close> for i j
    by simp
  have \<open>has_sum (\<lambda>i. ((id_cblinfun \<otimes>\<^sub>o selfbutterket i) o\<^sub>C\<^sub>L c o\<^sub>C\<^sub>L (id_cblinfun \<otimes>\<^sub>o selfbutterket j)) *\<^sub>V \<psi>)
            UNIV ((c o\<^sub>C\<^sub>L (id_cblinfun \<otimes>\<^sub>o selfbutterket j)) *\<^sub>V \<psi>)\<close> for j \<psi>
    apply simp by (rule has_sum_id_tensor_butterfly_ket)
  then have AB2: \<open>(c o\<^sub>C\<^sub>L (id_cblinfun \<otimes>\<^sub>o selfbutterket j)) \<in> AB\<close> for j
    apply (rule has_sum_closed_cstrong_operator_topology[rotated -1])
    using AB1 by auto

  have \<open>has_sum (\<lambda>j. (c o\<^sub>C\<^sub>L (id_cblinfun \<otimes>\<^sub>o selfbutterket j)) *\<^sub>V \<psi>) UNIV (c *\<^sub>V \<psi>)\<close> for \<psi>
    apply simp
    apply (rule has_sum_cblinfun_apply)
    by (rule has_sum_id_tensor_butterfly_ket)
  then show AB3: \<open>c \<in> AB\<close>
    apply (rule has_sum_closed_cstrong_operator_topology[rotated -1])
    using AB2 by auto
qed

(* TODO this one, too? *)
(* lemma tensor_op_dense:
  fixes S :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2) set\<close> and T :: \<open>('b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2) set\<close>
  assumes \<open>cstrong_operator_topology closure_of (cspan S) = UNIV\<close> and \<open>cstrong_operator_topology closure_of (cspan T) = UNIV\<close>
  shows \<open>cstrong_operator_topology closure_of (cspan {a \<otimes>\<^sub>o b | a b. a\<in>S \<and> b\<in>T}) = UNIV\<close> *)




lemma tensor_extensionality_finite:
  fixes F G :: \<open>((('a::finite \<times> 'b::finite) ell2) \<Rightarrow>\<^sub>C\<^sub>L (('c::finite \<times> 'd::finite) ell2)) \<Rightarrow> 'e::complex_vector\<close>
  assumes [simp]: "clinear F" "clinear G"
  assumes tensor_eq: "(\<And>a b. F (tensor_op a b) = G (tensor_op a b))"
  shows "F = G"
proof (rule ext, rule complex_vector.linear_eq_on_span[where f=F and g=G])
  show \<open>clinear F\<close> and \<open>clinear G\<close>
    using assms by (simp_all add: cbilinear_def)
  show \<open>x \<in> cspan  {tensor_op (butterket i j) (butterket k l)| i j k l. True}\<close> 
    for x :: \<open>('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('c \<times> 'd) ell2\<close>
    using cspan_tensor_op_butter by auto
  show \<open>F x = G x\<close> if \<open>x \<in> {tensor_op (butterket i j) (butterket k l) |i j k l. True}\<close> for x
    using that by (auto simp: tensor_eq)
qed

lemma tensor_id[simp]: \<open>tensor_op id_cblinfun id_cblinfun = id_cblinfun\<close>
  apply (rule equal_ket, rename_tac x, case_tac x)
  by (simp flip: tensor_ell2_ket add: tensor_op_ell2)

lemma tensor_op_adjoint: \<open>(tensor_op a b)* = tensor_op (a*) (b*)\<close>
  apply (rule cinner_ket_adjointI[symmetric])
  apply (auto simp flip: tensor_ell2_ket simp: tensor_op_ell2)
  by (simp add: cinner_adj_left)

lemma tensor_butterfly[simp]: "tensor_op (butterfly \<psi> \<psi>') (butterfly \<phi> \<phi>') = butterfly (tensor_ell2 \<psi> \<phi>) (tensor_ell2 \<psi>' \<phi>')"
  apply (rule equal_ket, rename_tac x, case_tac x)
  by (simp flip: tensor_ell2_ket add: tensor_op_ell2 butterfly_def
      cblinfun_apply_cblinfun_compose tensor_ell2_scaleC1 tensor_ell2_scaleC2)

definition tensor_lift :: \<open>(('a1::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a2::finite ell2) \<Rightarrow> ('b1::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b2::finite ell2) \<Rightarrow> 'c)
                        \<Rightarrow> ((('a1\<times>'b1) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a2\<times>'b2) ell2) \<Rightarrow> 'c::complex_normed_vector)\<close> where
  "tensor_lift F2 = (SOME G. clinear G \<and> (\<forall>a b. G (tensor_op a b) = F2 a b))"
(* TODO use cblinfun_extension? *)
(* TODO the same for tensor_ell2 *)

lemma 
  fixes F2 :: "'a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::finite ell2
            \<Rightarrow> 'c::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd::finite ell2
            \<Rightarrow> 'e::complex_normed_vector"
  assumes "cbilinear F2"
  shows tensor_lift_clinear: "clinear (tensor_lift F2)"
    and tensor_lift_correct:  \<open>(\<lambda>a b. tensor_lift F2 (a \<otimes>\<^sub>o b)) = F2\<close>
proof -
  define F2' t4 \<phi> where
    \<open>F2' = tensor_lift F2\<close> and
    \<open>t4 = (\<lambda>(i,j,k,l). tensor_op (butterket i j) (butterket k l))\<close> and
    \<open>\<phi> m = (let (i,j,k,l) = inv t4 m in F2 (butterket i j) (butterket k l))\<close> for m
  have t4inj: "x = y" if "t4 x = t4 y" for x y
  proof (rule ccontr)
    obtain i  j  k  l  where x: "x = (i,j,k,l)" by (meson prod_cases4) 
    obtain i' j' k' l' where y: "y = (i',j',k',l')" by (meson prod_cases4) 
    have 1: "bra (i,k) *\<^sub>V t4 x *\<^sub>V ket (j,l) = 1"
      by (auto simp: t4_def x tensor_op_ell2 butterfly_def cinner_ket simp flip: tensor_ell2_ket)
    assume \<open>x \<noteq> y\<close>
    then have 2: "bra (i,k) *\<^sub>V t4 y *\<^sub>V ket (j,l) = 0"
      by (auto simp: t4_def x y tensor_op_ell2 butterfly_def cblinfun_apply_cblinfun_compose cinner_ket
               simp flip: tensor_ell2_ket)
    from 1 2 that
    show False
      by auto
  qed
  have \<open>\<phi> (tensor_op (butterket i j) (butterket k l)) = F2 (butterket i j) (butterket k l)\<close> for i j k l
    apply (subst asm_rl[of \<open>tensor_op (butterket i j) (butterket k l) = t4 (i,j,k,l)\<close>])
     apply (simp add: t4_def)
    by (auto simp add: injI t4inj inv_f_f \<phi>_def)

  have *: \<open>range t4 = {tensor_op (butterket i j) (butterket k l) |i j k l. True}\<close>
    apply (auto simp: case_prod_beta t4_def)
    using image_iff by fastforce

  have "cblinfun_extension_exists (range t4) \<phi>"
    thm cblinfun_extension_exists_finite_dim[where \<phi>=\<phi>]
    apply (rule cblinfun_extension_exists_finite_dim)
     apply auto unfolding * 
    using cindependent_tensor_op_butter cspan_tensor_op_butter by auto

  then obtain G where G: \<open>G *\<^sub>V (t4 (i,j,k,l)) = F2 (butterket i j) (butterket k l)\<close> for i j k l
    apply atomize_elim
    unfolding cblinfun_extension_exists_def
    apply auto
    by (metis (no_types, lifting) t4inj \<phi>_def f_inv_into_f rangeI split_conv)

  have *: \<open>G *\<^sub>V tensor_op (butterket i j) (butterket k l) = F2 (butterket i j) (butterket k l)\<close> for i j k l
    using G by (auto simp: t4_def)
  have *: \<open>G *\<^sub>V tensor_op a (butterket k l) = F2 a (butterket k l)\<close> for a k l
    apply (rule complex_vector.linear_eq_on_span[where g=\<open>\<lambda>a. F2 a _\<close> and B=\<open>{butterket k l|k l. True}\<close>])
    unfolding cspan_butterfly_ket
    using * apply (auto intro!: clinear_compose[unfolded o_def, where f=\<open>\<lambda>a. tensor_op a _\<close> and g=\<open>(*\<^sub>V) G\<close>])
     apply (metis cbilinear_def tensor_op_cbilinear)
    using assms unfolding cbilinear_def by blast
  have G_F2: \<open>G *\<^sub>V tensor_op a b = F2 a b\<close> for a b
    apply (rule complex_vector.linear_eq_on_span[where g=\<open>F2 a\<close> and B=\<open>{butterket k l|k l. True}\<close>])
    unfolding cspan_butterfly_ket
    using * apply (auto simp: cblinfun.add_right clinearI
                        intro!: clinear_compose[unfolded o_def, where f=\<open>tensor_op a\<close> and g=\<open>(*\<^sub>V) G\<close>])
    apply (meson cbilinear_def tensor_op_cbilinear)
    using assms unfolding cbilinear_def by blast

  have \<open>clinear F2' \<and> (\<forall>a b. F2' (tensor_op a b) = F2 a b)\<close>
    unfolding F2'_def tensor_lift_def 
    apply (rule someI[where x=\<open>(*\<^sub>V) G\<close> and P=\<open>\<lambda>G. clinear G \<and> (\<forall>a b. G (tensor_op a b) = F2 a b)\<close>])
    using G_F2 by (simp add: cblinfun.add_right clinearI)

  then show \<open>clinear F2'\<close> and \<open>(\<lambda>a b. tensor_lift F2 (tensor_op a b)) = F2\<close>
    unfolding F2'_def by auto
qed


lemma tensor_op_nonzero:
  fixes a :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2\<close> and b :: \<open>'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2\<close>
  assumes \<open>a \<noteq> 0\<close> and \<open>b \<noteq> 0\<close>
  shows \<open>a \<otimes>\<^sub>o b \<noteq> 0\<close>
proof -
  from \<open>a \<noteq> 0\<close> obtain i where i: \<open>a *\<^sub>V ket i \<noteq> 0\<close>
    by (metis cblinfun.zero_left equal_ket)
  from \<open>b \<noteq> 0\<close> obtain j where j: \<open>b *\<^sub>V ket j \<noteq> 0\<close>
    by (metis cblinfun.zero_left equal_ket)
  from i j have ijneq0: \<open>(a *\<^sub>V ket i) \<otimes>\<^sub>s (b *\<^sub>V ket j) \<noteq> 0\<close>
    by (simp add: tensor_ell2_nonzero)
  have \<open>(a *\<^sub>V ket i) \<otimes>\<^sub>s (b *\<^sub>V ket j) = (a \<otimes>\<^sub>o b) *\<^sub>V ket (i,j)\<close>
    by (simp add: tensor_op_ket)
  with ijneq0 show \<open>a \<otimes>\<^sub>o b \<noteq> 0\<close>
    by force
qed

lemma inj_tensor_ell2_left: \<open>inj (\<lambda>a::'a ell2. a \<otimes>\<^sub>s b)\<close> if \<open>b \<noteq> 0\<close> for b :: \<open>'b ell2\<close>
proof (rule injI, rule ccontr)
  fix x y :: \<open>'a ell2\<close>
  assume eq: \<open>x \<otimes>\<^sub>s b = y \<otimes>\<^sub>s b\<close>
  assume neq: \<open>x \<noteq> y\<close>
  define a where \<open>a = x - y\<close>
  from neq a_def have neq0: \<open>a \<noteq> 0\<close>
    by auto
  with \<open>b \<noteq> 0\<close> have \<open>a \<otimes>\<^sub>s b \<noteq> 0\<close>
    by (simp add: tensor_ell2_nonzero)
  then have \<open>x \<otimes>\<^sub>s b \<noteq> y \<otimes>\<^sub>s b\<close>
    unfolding a_def
    by (metis add_cancel_left_left diff_add_cancel tensor_ell2_add1)
  with eq show False
    by auto
qed

lemma inj_tensor_ell2_right: \<open>inj (\<lambda>b::'b ell2. a \<otimes>\<^sub>s b)\<close> if \<open>a \<noteq> 0\<close> for a :: \<open>'a ell2\<close>
proof (rule injI, rule ccontr)
  fix x y :: \<open>'b ell2\<close>
  assume eq: \<open>a \<otimes>\<^sub>s x = a \<otimes>\<^sub>s y\<close>
  assume neq: \<open>x \<noteq> y\<close>
  define b where \<open>b = x - y\<close>
  from neq b_def have neq0: \<open>b \<noteq> 0\<close>
    by auto
  with \<open>a \<noteq> 0\<close> have \<open>a \<otimes>\<^sub>s b \<noteq> 0\<close>
    by (simp add: tensor_ell2_nonzero)
  then have \<open>a \<otimes>\<^sub>s x \<noteq> a \<otimes>\<^sub>s y\<close>
    unfolding b_def
    by (metis add_cancel_left_left diff_add_cancel tensor_ell2_add2)
  with eq show False
    by auto
qed

lemma inj_tensor_left: \<open>inj (\<lambda>a::'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2. a \<otimes>\<^sub>o b)\<close> if \<open>b \<noteq> 0\<close> for b :: \<open>'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2\<close>
proof (rule injI, rule ccontr)
  fix x y :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2\<close>
  assume eq: \<open>x \<otimes>\<^sub>o b = y \<otimes>\<^sub>o b\<close>
  assume neq: \<open>x \<noteq> y\<close>
  define a where \<open>a = x - y\<close>
  from neq a_def have neq0: \<open>a \<noteq> 0\<close>
    by auto
  with \<open>b \<noteq> 0\<close> have \<open>a \<otimes>\<^sub>o b \<noteq> 0\<close>
    by (simp add: tensor_op_nonzero)
  then have \<open>x \<otimes>\<^sub>o b \<noteq> y \<otimes>\<^sub>o b\<close>
    unfolding a_def
    by (metis add_cancel_left_left diff_add_cancel tensor_op_left_add) 
  with eq show False
    by auto
qed

lemma inj_tensor_right: \<open>inj (\<lambda>b::'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2. a \<otimes>\<^sub>o b)\<close> if \<open>a \<noteq> 0\<close> for a :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2\<close>
proof (rule injI, rule ccontr)
  fix x y :: \<open>'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2\<close>
  assume eq: \<open>a \<otimes>\<^sub>o x = a \<otimes>\<^sub>o y\<close>
  assume neq: \<open>x \<noteq> y\<close>
  define b where \<open>b = x - y\<close>
  from neq b_def have neq0: \<open>b \<noteq> 0\<close>
    by auto
  with \<open>a \<noteq> 0\<close> have \<open>a \<otimes>\<^sub>o b \<noteq> 0\<close>
    by (simp add: tensor_op_nonzero)
  then have \<open>a \<otimes>\<^sub>o x \<noteq> a \<otimes>\<^sub>o y\<close>
    unfolding b_def
    by (metis add_cancel_left_left diff_add_cancel tensor_op_right_add) 
  with eq show False
    by auto
qed

lemma tensor_ell2_almost_injective:
  assumes \<open>tensor_ell2 a b = tensor_ell2 c d\<close>
  assumes \<open>a \<noteq> 0\<close>
  shows \<open>\<exists>\<gamma>. b = \<gamma> *\<^sub>C d\<close>
proof -
  from \<open>a \<noteq> 0\<close> obtain i where i: \<open>cinner (ket i) a \<noteq> 0\<close>
    by (metis cinner_eq_zero_iff cinner_ket_left ell2_pointwise_ortho)
  have \<open>cinner (ket i \<otimes>\<^sub>s ket j) (a \<otimes>\<^sub>s b) = cinner (ket i \<otimes>\<^sub>s ket j) (c \<otimes>\<^sub>s d)\<close> for j
    using assms by simp
  then have eq2: \<open>(cinner (ket i) a) * (cinner (ket j) b) = (cinner (ket i) c) * (cinner (ket j) d)\<close> for j
    by (metis tensor_ell2_inner_prod)
  then obtain \<gamma> where \<open>cinner (ket i) c = \<gamma> * cinner (ket i) a\<close>
    by (metis i eq_divide_eq)
  with eq2 have \<open>(cinner (ket i) a) * (cinner (ket j) b) = (cinner (ket i) a) * (\<gamma> * cinner (ket j) d)\<close> for j
    by simp
  then have \<open>cinner (ket j) b = cinner (ket j) (\<gamma> *\<^sub>C d)\<close> for j
    using i by force
  then have \<open>b = \<gamma> *\<^sub>C d\<close>
    by (simp add: cinner_ket_eqI)
  then show ?thesis
    by auto
qed


lemma tensor_op_almost_injective:
  fixes a c :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
    and b d :: \<open>'c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2\<close>
  assumes \<open>tensor_op a b = tensor_op c d\<close>
  assumes \<open>a \<noteq> 0\<close>
  shows \<open>\<exists>\<gamma>. b = \<gamma> *\<^sub>C d\<close>
proof (cases \<open>d = 0\<close>)
  case False
  from \<open>a \<noteq> 0\<close> obtain \<psi> where \<psi>: \<open>a *\<^sub>V \<psi> \<noteq> 0\<close>
    by (metis cblinfun.zero_left cblinfun_eqI)
  have \<open>(a \<otimes>\<^sub>o b) (\<psi> \<otimes>\<^sub>s \<phi>) = (c \<otimes>\<^sub>o d) (\<psi> \<otimes>\<^sub>s \<phi>)\<close> for \<phi>
    using assms by simp
  then have eq2: \<open>(a \<psi>) \<otimes>\<^sub>s (b \<phi>) = (c \<psi>) \<otimes>\<^sub>s (d \<phi>)\<close> for \<phi>
    by (simp add: tensor_op_ell2)
  then have eq2': \<open>(d \<phi>) \<otimes>\<^sub>s (c \<psi>) = (b \<phi>) \<otimes>\<^sub>s (a \<psi>)\<close> for \<phi>
    by (metis swap_ell2_tensor)
  from False obtain \<phi>0 where \<phi>0: \<open>d \<phi>0 \<noteq> 0\<close>
    by (metis cblinfun.zero_left cblinfun_eqI)
  obtain \<gamma> where \<open>c \<psi> = \<gamma> *\<^sub>C a \<psi>\<close>
    apply atomize_elim
    using eq2' \<phi>0 by (rule tensor_ell2_almost_injective)
  with eq2 have \<open>(a \<psi>) \<otimes>\<^sub>s (b \<phi>) = (a \<psi>) \<otimes>\<^sub>s (\<gamma> *\<^sub>C d \<phi>)\<close> for \<phi>
    by (simp add: tensor_ell2_scaleC1 tensor_ell2_scaleC2)
  then have \<open>b \<phi> = \<gamma> *\<^sub>C d \<phi>\<close> for \<phi>
    by (smt (verit, best) \<psi> complex_vector.scale_cancel_right tensor_ell2_almost_injective tensor_ell2_nonzero tensor_ell2_scaleC2)
  then have \<open>b = \<gamma> *\<^sub>C d\<close>
    by (simp add: cblinfun_eqI)
  then show ?thesis
    by auto
next
  case True
  then have \<open>c \<otimes>\<^sub>o d = 0\<close>
    by (metis add_cancel_right_left tensor_op_right_add)
  then have \<open>a \<otimes>\<^sub>o b = 0\<close>
    using assms(1) by presburger
  with \<open>a \<noteq> 0\<close> have \<open>b = 0\<close>
    by (meson tensor_op_nonzero)
  then show ?thesis
    by auto
qed

lemma clinear_tensor_left[simp]: \<open>clinear (\<lambda>a. a \<otimes>\<^sub>o b :: _ ell2 \<Rightarrow>\<^sub>C\<^sub>L _ ell2)\<close>
  apply (rule clinearI)
   apply (rule tensor_op_left_add)
  by (rule tensor_op_scaleC_left)

lemma clinear_tensor_right[simp]: \<open>clinear (\<lambda>b. a \<otimes>\<^sub>o b :: _ ell2 \<Rightarrow>\<^sub>C\<^sub>L _ ell2)\<close>
  apply (rule clinearI)
   apply (rule tensor_op_right_add)
  by (rule tensor_op_scaleC_right)

lemma tensor_op_0_left[simp]: \<open>tensor_op 0 x = (0 :: ('a*'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('c*'d) ell2)\<close>
  apply (rule equal_ket)
  by (auto simp flip: tensor_ell2_ket simp: tensor_op_ell2)

lemma tensor_op_0_right[simp]: \<open>tensor_op x 0 = (0 :: ('a*'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('c*'d) ell2)\<close>
  apply (rule equal_ket)
  by (auto simp flip: tensor_ell2_ket simp: tensor_op_ell2)

lemma bij_tensor_ell2_one_dim_left:
  assumes \<open>\<psi> \<noteq> 0\<close>
  shows \<open>bij (\<lambda>x::'b ell2. (\<psi> :: 'a::CARD_1 ell2) \<otimes>\<^sub>s x)\<close>
proof (rule bijI)
  show \<open>inj (\<lambda>x::'b ell2. (\<psi> :: 'a::CARD_1 ell2) \<otimes>\<^sub>s x)\<close>
    using assms by (rule inj_tensor_ell2_right)
  have \<open>\<exists>x. \<psi> \<otimes>\<^sub>s x = \<phi>\<close> for \<phi> :: \<open>('a*'b) ell2\<close>
  proof (use assms in transfer)
    fix \<psi> :: \<open>'a \<Rightarrow> complex\<close> and \<phi> :: \<open>'a*'b \<Rightarrow> complex\<close>
    assume \<open>has_ell2_norm \<phi>\<close> and \<open>\<psi> \<noteq> (\<lambda>_. 0)\<close>
    define c where \<open>c = \<psi> undefined\<close>
    then have \<open>\<psi> a = c\<close> for a 
      apply (subst everything_the_same[of _ undefined])
      by simp
    with \<open>\<psi> \<noteq> (\<lambda>_. 0)\<close> have \<open>c \<noteq> 0\<close>
      by auto

    define x where \<open>x j = \<phi> (undefined, j) / c\<close> for j
    have \<open>(\<lambda>(i, j). \<psi> i * x j) = \<phi>\<close>
      apply (auto intro!: ext simp: x_def \<open>\<psi> _ = c\<close> \<open>c \<noteq> 0\<close>)
      apply (subst (2) everything_the_same[of _ undefined])
      by simp
    moreover have \<open>has_ell2_norm x\<close>
    proof -
      have \<open>(\<lambda>(i,j). (\<phi> (i,j))\<^sup>2) abs_summable_on UNIV\<close>
        using \<open>has_ell2_norm \<phi>\<close> has_ell2_norm_def by auto
      then have \<open>(\<lambda>(i,j). (\<phi> (i,j))\<^sup>2) abs_summable_on Pair undefined ` UNIV\<close>
        using summable_on_subset_banach by blast
      then have \<open>(\<lambda>j. (\<phi> (undefined,j))\<^sup>2) abs_summable_on UNIV\<close>
        apply (subst (asm) summable_on_reindex)
        by (auto simp: o_def inj_def)
      then have \<open>(\<lambda>j. (\<phi> (undefined,j) / c)\<^sup>2) abs_summable_on UNIV\<close>
        by (simp add: divide_inverse power_mult_distrib norm_mult summable_on_cmult_left)
      then have \<open>(\<lambda>j. (x j)\<^sup>2) abs_summable_on UNIV\<close>
        by (simp add: x_def)
      then show ?thesis
        using has_ell2_norm_def by blast
    qed
    ultimately show \<open>\<exists>x\<in>Collect has_ell2_norm. (\<lambda>(i, j). \<psi> i * x j) = \<phi>\<close>
      apply (rule_tac bexI[where x=x])
      by auto
  qed

  then show \<open>surj (\<lambda>x::'b ell2. (\<psi> :: 'a::CARD_1 ell2) \<otimes>\<^sub>s x)\<close>
    by (metis surj_def)
qed

lemma ket_CARD_1_is_1: \<open>ket x = 1\<close> for x :: \<open>'a::CARD_1\<close>
  apply transfer by simp

lemma bij_tensor_op_one_dim_left:
  fixes a :: \<open>'a::{CARD_1,enum} ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::{CARD_1,enum} ell2\<close>
  assumes \<open>a \<noteq> 0\<close>
  shows \<open>bij (\<lambda>x::'c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2. a \<otimes>\<^sub>o x)\<close>
proof -
  have [simp]: \<open>bij (Pair (undefined::'a))\<close>
    apply (rule o_bij[of snd]) by auto
  have [simp]: \<open>bij (Pair (undefined::'b))\<close>
    apply (rule o_bij[of snd]) by auto
  define t where \<open>t x = a \<otimes>\<^sub>o x\<close> for x :: \<open>'c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2\<close>
  define u :: \<open>'c ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a\<times>'c) ell2\<close> where \<open>u = classical_operator (Some o Pair undefined)\<close>
  define v :: \<open>'d ell2 \<Rightarrow>\<^sub>C\<^sub>L ('b\<times>'d) ell2\<close> where \<open>v = classical_operator (Some o Pair undefined)\<close>
  have [simp]: \<open>unitary u\<close> \<open>unitary v\<close>
    by (simp_all add: u_def v_def)
  have u_ket[simp]: \<open>u *\<^sub>V ket x = ket (undefined, x)\<close> for x
    by (simp add: u_def classical_operator_ket classical_operator_exists_inj inj_def)
  have uadj_ket[simp]: \<open>u* *\<^sub>V ket (z, x) = ket x\<close> for x z
    apply (subst everything_the_same[of _ undefined])
    by (metis (no_types, opaque_lifting) u_ket cinner_adj_right cinner_ket_eqI cinner_ket_same orthogonal_ket prod.inject)
  have v_ket[simp]: \<open>v *\<^sub>V ket x = ket (undefined, x)\<close> for x
    by (simp add: v_def classical_operator_ket classical_operator_exists_inj inj_def)
  then have [simp]: \<open>v *\<^sub>V x = ket undefined \<otimes>\<^sub>s x\<close> for x
    apply (rule_tac fun_cong[where x=x])
    apply (rule bounded_clinear_equal_ket)
    by (auto simp add: bounded_clinear_tensor_ell21 cblinfun.bounded_clinear_right)
  define a' :: complex where \<open>a' = one_dim_iso a\<close>
  from assms have \<open>a' \<noteq> 0\<close>
    using a'_def one_dim_iso_of_zero' by auto
  have a_a': \<open>a = of_complex a'\<close>
    by (simp add: a'_def) 
  have \<open>t x *\<^sub>V ket (i,j) = (a' *\<^sub>C v o\<^sub>C\<^sub>L x o\<^sub>C\<^sub>L u*) *\<^sub>V ket (i,j)\<close> for x i j
    apply (simp add: t_def)
    apply (simp add: ket_CARD_1_is_1 tensor_op_ell2 flip: tensor_ell2_ket)
    by (metis a'_def one_cblinfun_apply_one one_dim_scaleC_1 scaleC_cblinfun.rep_eq tensor_ell2_scaleC1) 
  then have t: \<open>t x = (a' *\<^sub>C v o\<^sub>C\<^sub>L x o\<^sub>C\<^sub>L u*)\<close> for x
    apply (rule_tac equal_ket)
    by auto
  define s where \<open>s y = (inverse a' *\<^sub>C (v)* o\<^sub>C\<^sub>L y o\<^sub>C\<^sub>L u)\<close> for y
  have \<open>s (t x) = (a' * inverse a') *\<^sub>C (((v)* o\<^sub>C\<^sub>L v) o\<^sub>C\<^sub>L x o\<^sub>C\<^sub>L (u* o\<^sub>C\<^sub>L u))\<close> for x
    apply (simp add: s_def t cblinfun_compose_assoc)
    by (simp flip: cblinfun_compose_assoc)
  also have \<open>\<dots> x = x\<close> for x
    using \<open>a' \<noteq> 0\<close> by simp
  finally have \<open>s o t = id\<close>
    by auto
  have \<open>t (s y) = (a' * inverse a') *\<^sub>C ((v o\<^sub>C\<^sub>L (v)*) o\<^sub>C\<^sub>L y o\<^sub>C\<^sub>L (u o\<^sub>C\<^sub>L u*))\<close> for y
    apply (simp add: s_def t cblinfun_compose_assoc)
    by (simp flip: cblinfun_compose_assoc)
  also have \<open>\<dots> y = y\<close> for y
    using \<open>a' \<noteq> 0\<close> by simp
  finally have \<open>t o s = id\<close>
    by auto
  from \<open>s o t = id\<close> \<open>t o s = id\<close>
  show \<open>bij t\<close>
    using o_bij by blast
qed

lemma bij_tensor_op_one_dim_right:
  assumes \<open>b \<noteq> 0\<close>
  shows \<open>bij (\<lambda>x::'c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2. x \<otimes>\<^sub>o (b :: 'a::{CARD_1,enum} ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::{CARD_1,enum} ell2))\<close>
    (is \<open>bij ?f\<close>)
proof -
  let ?sf = \<open>(\<lambda>x. swap_ell2 o\<^sub>C\<^sub>L (?f x) o\<^sub>C\<^sub>L swap_ell2)\<close>
  let ?s = \<open>(\<lambda>x. swap_ell2 o\<^sub>C\<^sub>L x o\<^sub>C\<^sub>L swap_ell2)\<close>
  let ?g = \<open>(\<lambda>x::'c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2. (b :: 'a::{CARD_1,enum} ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::{CARD_1,enum} ell2) \<otimes>\<^sub>o x)\<close>
  have \<open>?sf = ?g\<close>
    by (auto intro!: ext tensor_ell2_extensionality simp add: swap_ell2_tensor tensor_op_ell2)
  have \<open>bij ?g\<close>
    using assms by (rule bij_tensor_op_one_dim_left)
  have \<open>?s o ?sf = ?f\<close>
    apply (auto intro!: ext simp: cblinfun_assoc_left)
    by (auto simp: cblinfun_assoc_right)
  also have \<open>bij ?s\<close>
    apply (rule o_bij[where g=\<open>(\<lambda>x. swap_ell2 o\<^sub>C\<^sub>L x o\<^sub>C\<^sub>L swap_ell2)\<close>])
     apply (auto intro!: ext simp: cblinfun_assoc_left)
    by (auto simp: cblinfun_assoc_right)
  show \<open>bij ?f\<close>
    apply (subst \<open>?s o ?sf = ?f\<close>[symmetric], subst \<open>?sf = ?g\<close>)
    using \<open>bij ?g\<close> \<open>bij ?s\<close> by (rule bij_comp)
qed

lemma overlapping_tensor:
  fixes a23 :: \<open>('a2*'a3) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('b2*'b3) ell2\<close>
    and b12 :: \<open>('a1*'a2) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('b1*'b2) ell2\<close>
  assumes eq: \<open>butterfly \<psi> \<psi>' \<otimes>\<^sub>o a23 = assoc_ell2 o\<^sub>C\<^sub>L (b12 \<otimes>\<^sub>o butterfly \<phi> \<phi>') o\<^sub>C\<^sub>L assoc_ell2*\<close>
  assumes \<open>\<psi> \<noteq> 0\<close> \<open>\<psi>' \<noteq> 0\<close> \<open>\<phi> \<noteq> 0\<close> \<open>\<phi>' \<noteq> 0\<close>
  shows \<open>\<exists>c. butterfly \<psi> \<psi>' \<otimes>\<^sub>o a23 = butterfly \<psi> \<psi>' \<otimes>\<^sub>o c \<otimes>\<^sub>o butterfly \<phi> \<phi>'\<close>
proof -
  let ?id1 = \<open>id_cblinfun :: unit ell2 \<Rightarrow>\<^sub>C\<^sub>L unit ell2\<close>
  note id_cblinfun_eq_1[simp del]
  define d where \<open>d = butterfly \<psi> \<psi>' \<otimes>\<^sub>o a23\<close>

  define \<psi>\<^sub>n \<psi>\<^sub>n' a23\<^sub>n where \<open>\<psi>\<^sub>n = \<psi> /\<^sub>C norm \<psi>\<close> and \<open>\<psi>\<^sub>n' = \<psi>' /\<^sub>C norm \<psi>'\<close> and \<open>a23\<^sub>n = norm \<psi> *\<^sub>C norm \<psi>' *\<^sub>C a23\<close>
  have [simp]: \<open>norm \<psi>\<^sub>n = 1\<close> \<open>norm \<psi>\<^sub>n' = 1\<close>
    using \<open>\<psi> \<noteq> 0\<close> \<open>\<psi>' \<noteq> 0\<close> by (auto simp: \<psi>\<^sub>n_def \<psi>\<^sub>n'_def norm_inverse)
  have n1: \<open>butterfly \<psi>\<^sub>n \<psi>\<^sub>n' \<otimes>\<^sub>o a23\<^sub>n = butterfly \<psi> \<psi>' \<otimes>\<^sub>o a23\<close>
    apply (auto simp: \<psi>\<^sub>n_def \<psi>\<^sub>n'_def a23\<^sub>n_def tensor_op_scaleC_left tensor_op_scaleC_right)
    by (metis (no_types, lifting) assms(2) assms(3) inverse_mult_distrib mult.commute no_zero_divisors norm_eq_zero of_real_eq_0_iff right_inverse scaleC_one)

  define \<phi>\<^sub>n \<phi>\<^sub>n' b12\<^sub>n where \<open>\<phi>\<^sub>n = \<phi> /\<^sub>C norm \<phi>\<close> and \<open>\<phi>\<^sub>n' = \<phi>' /\<^sub>C norm \<phi>'\<close> and \<open>b12\<^sub>n = norm \<phi> *\<^sub>C norm \<phi>' *\<^sub>C b12\<close>
  have [simp]: \<open>norm \<phi>\<^sub>n = 1\<close> \<open>norm \<phi>\<^sub>n' = 1\<close>
    using \<open>\<phi> \<noteq> 0\<close> \<open>\<phi>' \<noteq> 0\<close> by (auto simp: \<phi>\<^sub>n_def \<phi>\<^sub>n'_def norm_inverse)
  have n2: \<open>b12\<^sub>n \<otimes>\<^sub>o butterfly \<phi>\<^sub>n \<phi>\<^sub>n' = b12 \<otimes>\<^sub>o butterfly \<phi> \<phi>'\<close>
    apply (auto simp: \<phi>\<^sub>n_def \<phi>\<^sub>n'_def b12\<^sub>n_def tensor_op_scaleC_left tensor_op_scaleC_right)
    by (metis (no_types, lifting) assms(4) assms(5) field_class.field_inverse inverse_mult_distrib mult.commute no_zero_divisors norm_eq_zero of_real_hom.hom_0 scaleC_one)

  define c' :: \<open>(unit*'a2*unit) ell2 \<Rightarrow>\<^sub>C\<^sub>L (unit*'b2*unit) ell2\<close> 
    where \<open>c' = (vector_to_cblinfun \<psi>\<^sub>n \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o vector_to_cblinfun \<phi>\<^sub>n)* o\<^sub>C\<^sub>L d
            o\<^sub>C\<^sub>L (vector_to_cblinfun \<psi>\<^sub>n' \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o vector_to_cblinfun \<phi>\<^sub>n')\<close>

  define c'' :: \<open>'a2 ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b2 ell2\<close>
    where \<open>c'' = inv (\<lambda>c''. id_cblinfun \<otimes>\<^sub>o c'' \<otimes>\<^sub>o id_cblinfun) c'\<close>

  have *: \<open>bij (\<lambda>c''::'a2 ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b2 ell2. ?id1 \<otimes>\<^sub>o c'' \<otimes>\<^sub>o ?id1)\<close>
    apply (subst asm_rl[of \<open>_ = (\<lambda>x. id_cblinfun \<otimes>\<^sub>o x) o (\<lambda>c''. c'' \<otimes>\<^sub>o id_cblinfun)\<close>])
    using [[show_consts]]
    by (auto intro!: bij_comp bij_tensor_op_one_dim_left bij_tensor_op_one_dim_right)

  have c'_c'': \<open>c' = ?id1 \<otimes>\<^sub>o c'' \<otimes>\<^sub>o ?id1\<close>
    unfolding c''_def 
    apply (rule surj_f_inv_f[where y=c', symmetric])
    using * by (rule bij_is_surj)

  define c :: \<open>'a2 ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b2 ell2\<close>
    where \<open>c = c'' /\<^sub>C norm \<psi> /\<^sub>C norm \<psi>' /\<^sub>C norm \<phi> /\<^sub>C norm \<phi>'\<close>

  have aux: \<open>assoc_ell2* o\<^sub>C\<^sub>L (assoc_ell2 o\<^sub>C\<^sub>L x o\<^sub>C\<^sub>L assoc_ell2*) o\<^sub>C\<^sub>L assoc_ell2 = x\<close> for x
    apply (simp add: cblinfun_assoc_left)
    by (simp add: cblinfun_assoc_right)
  have aux2: \<open>(assoc_ell2 o\<^sub>C\<^sub>L ((x \<otimes>\<^sub>o y) \<otimes>\<^sub>o z) o\<^sub>C\<^sub>L assoc_ell2*) = x \<otimes>\<^sub>o (y \<otimes>\<^sub>o z)\<close> for x y z
    apply (rule equal_ket, rename_tac xyz)
    apply (case_tac xyz, hypsubst_thin)
    by (simp flip: tensor_ell2_ket add: assoc_ell2'_tensor assoc_ell2_tensor tensor_op_ell2)

  have \<open>d = (butterfly \<psi>\<^sub>n \<psi>\<^sub>n \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L d o\<^sub>C\<^sub>L (butterfly \<psi>\<^sub>n' \<psi>\<^sub>n' \<otimes>\<^sub>o id_cblinfun)\<close>
    by (auto simp: d_def n1[symmetric] comp_tensor_op cnorm_eq_1[THEN iffD1])
  also have \<open>\<dots> = (butterfly \<psi>\<^sub>n \<psi>\<^sub>n \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L assoc_ell2 o\<^sub>C\<^sub>L (b12\<^sub>n \<otimes>\<^sub>o butterfly \<phi>\<^sub>n \<phi>\<^sub>n')
                  o\<^sub>C\<^sub>L assoc_ell2* o\<^sub>C\<^sub>L (butterfly \<psi>\<^sub>n' \<psi>\<^sub>n' \<otimes>\<^sub>o id_cblinfun)\<close>
    by (auto simp: d_def eq n2 cblinfun_assoc_left)
  also have \<open>\<dots> = (butterfly \<psi>\<^sub>n \<psi>\<^sub>n \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L assoc_ell2 o\<^sub>C\<^sub>L 
               ((id_cblinfun \<otimes>\<^sub>o butterfly \<phi>\<^sub>n \<phi>\<^sub>n) o\<^sub>C\<^sub>L (b12\<^sub>n \<otimes>\<^sub>o butterfly \<phi>\<^sub>n \<phi>\<^sub>n') o\<^sub>C\<^sub>L (id_cblinfun \<otimes>\<^sub>o butterfly \<phi>\<^sub>n' \<phi>\<^sub>n'))
               o\<^sub>C\<^sub>L assoc_ell2* o\<^sub>C\<^sub>L (butterfly \<psi>\<^sub>n' \<psi>\<^sub>n' \<otimes>\<^sub>o id_cblinfun)\<close>
    by (auto simp: comp_tensor_op cnorm_eq_1[THEN iffD1])
  also have \<open>\<dots> = (butterfly \<psi>\<^sub>n \<psi>\<^sub>n \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L assoc_ell2 o\<^sub>C\<^sub>L 
               ((id_cblinfun \<otimes>\<^sub>o butterfly \<phi>\<^sub>n \<phi>\<^sub>n) o\<^sub>C\<^sub>L (assoc_ell2* o\<^sub>C\<^sub>L d o\<^sub>C\<^sub>L assoc_ell2) o\<^sub>C\<^sub>L (id_cblinfun \<otimes>\<^sub>o butterfly \<phi>\<^sub>n' \<phi>\<^sub>n'))
               o\<^sub>C\<^sub>L assoc_ell2* o\<^sub>C\<^sub>L (butterfly \<psi>\<^sub>n' \<psi>\<^sub>n' \<otimes>\<^sub>o id_cblinfun)\<close>
    by (auto simp: d_def n2 eq aux)
  also have \<open>\<dots> = ((butterfly \<psi>\<^sub>n \<psi>\<^sub>n \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L (assoc_ell2 o\<^sub>C\<^sub>L (id_cblinfun \<otimes>\<^sub>o butterfly \<phi>\<^sub>n \<phi>\<^sub>n) o\<^sub>C\<^sub>L assoc_ell2*))
               o\<^sub>C\<^sub>L d o\<^sub>C\<^sub>L ((assoc_ell2 o\<^sub>C\<^sub>L (id_cblinfun \<otimes>\<^sub>o butterfly \<phi>\<^sub>n' \<phi>\<^sub>n') o\<^sub>C\<^sub>L assoc_ell2*) o\<^sub>C\<^sub>L (butterfly \<psi>\<^sub>n' \<psi>\<^sub>n' \<otimes>\<^sub>o id_cblinfun))\<close>
    by (auto simp: sandwich_def cblinfun_assoc_left)
  also have \<open>\<dots> = (butterfly \<psi>\<^sub>n \<psi>\<^sub>n \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o butterfly \<phi>\<^sub>n \<phi>\<^sub>n)
               o\<^sub>C\<^sub>L d o\<^sub>C\<^sub>L (butterfly \<psi>\<^sub>n' \<psi>\<^sub>n' \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o butterfly \<phi>\<^sub>n' \<phi>\<^sub>n')\<close>
    apply (simp only: tensor_id[symmetric] comp_tensor_op aux2)
    by (simp add: cnorm_eq_1[THEN iffD1])
  also have \<open>\<dots> = (vector_to_cblinfun \<psi>\<^sub>n \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o vector_to_cblinfun \<phi>\<^sub>n)
               o\<^sub>C\<^sub>L c' o\<^sub>C\<^sub>L (vector_to_cblinfun \<psi>\<^sub>n' \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o vector_to_cblinfun \<phi>\<^sub>n')*\<close>
    apply (simp add: c'_def butterfly_def_one_dim[where 'c="unit ell2"] cblinfun_assoc_left comp_tensor_op
                      tensor_op_adjoint cnorm_eq_1[THEN iffD1])
    by (simp add: cblinfun_assoc_right comp_tensor_op)
  also have \<open>\<dots> = butterfly \<psi>\<^sub>n \<psi>\<^sub>n' \<otimes>\<^sub>o c'' \<otimes>\<^sub>o butterfly \<phi>\<^sub>n \<phi>\<^sub>n'\<close>
    by (simp add: c'_c'' comp_tensor_op tensor_op_adjoint butterfly_def_one_dim[symmetric])
  also have \<open>\<dots> = butterfly \<psi> \<psi>' \<otimes>\<^sub>o c \<otimes>\<^sub>o butterfly \<phi> \<phi>'\<close>
    by (simp add: \<psi>\<^sub>n_def \<psi>\<^sub>n'_def \<phi>\<^sub>n_def \<phi>\<^sub>n'_def c_def tensor_op_scaleC_left tensor_op_scaleC_right)
  finally have d_c: \<open>d = butterfly \<psi> \<psi>' \<otimes>\<^sub>o c \<otimes>\<^sub>o butterfly \<phi> \<phi>'\<close>
    by -
  then show ?thesis
    by (auto simp: d_def)
qed


end
