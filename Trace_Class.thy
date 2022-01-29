theory Trace_Class
  imports Complex_Bounded_Operators.Complex_L2 Misc_Tensor_Product HS2Ell2
begin

unbundle cblinfun_notation

lemma 
  assumes \<open>is_onb E\<close>
  shows parseval_infsum: \<open>(\<Sum>\<^sub>\<infinity>e\<in>E. (cmod (h \<bullet>\<^sub>C e))\<^sup>2) = (norm h)\<^sup>2\<close>
    and parseval_abs_summable: \<open>(\<lambda>e. (cmod (h \<bullet>\<^sub>C e))\<^sup>2) abs_summable_on E\<close>
  sorry

(* TODO: conway, op, 18.1 Proposition (part) *)
lemma TODO_name1:
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
  shows sqrt_op_pos[simp]: \<open>sqrt_op a \<ge>0\<close> and sqrt_op_square[simp]: \<open>(sqrt_op a)* o\<^sub>C\<^sub>L sqrt_op a = a\<close>
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

definition trace_class :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a) \<Rightarrow> bool\<close> 
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

definition trace_norm where \<open>trace_norm A = (if trace_class A then (\<Sum>e\<in>some_chilbert_basis. cmod ((abs_op A *\<^sub>V e) \<bullet>\<^sub>C e)) else 0)\<close>

typedef (overloaded) 'a::chilbert_space trace_class = \<open>Collect trace_class :: ('a \<Rightarrow>\<^sub>C\<^sub>L 'a) set\<close>
  by (auto intro!: exI[of _ 0])
setup_lifting type_definition_trace_class

instantiation trace_class :: (chilbert_space) "{zero,norm}" begin
lift_definition zero_trace_class :: \<open>'a trace_class\<close> is 0 by auto
lift_definition norm_trace_class :: \<open>'a trace_class \<Rightarrow> real\<close> is trace_norm .
(* lift_definition minus_trace_class :: \<open>'a trace_class \<Rightarrow> 'a trace_class \<Rightarrow> 'a trace_class\<close> is minus  *)
(* definition dist_trace_class :: \<open>'a trace_class \<Rightarrow> _ \<Rightarrow> _\<close> where \<open>dist_trace_class a b = norm (a - b)\<close> *)
instance..
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
