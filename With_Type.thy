theory With_Type
  imports "HOL-Types_To_Sets.Types_To_Sets"
begin

term "type_definition"

definition \<open>with_type S P \<longleftrightarrow> S\<noteq>{} \<and> (\<forall>Rep Abs. type_definition Rep Abs S \<longrightarrow> P Rep Abs S)\<close>

term \<open>TYPE(_)\<close>
term \<open>CARD[x]\<close>

syntax "_with_type" :: "type \<Rightarrow> 'a => 'b" ("(1WITH_TYPE/(1'(_')))")

lemma with_type_mp: \<open>with_type S P \<Longrightarrow> (\<And>Rep Abs. type_definition Rep Abs S \<Longrightarrow> P Rep Abs S \<Longrightarrow> Q Rep Abs S) \<Longrightarrow> with_type S Q\<close>
  by (simp add: with_type_def)

end
