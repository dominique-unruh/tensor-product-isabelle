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

unbundle no_cblinfun_notation

end
