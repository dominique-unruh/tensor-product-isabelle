theory With_Type
  imports "HOL-Types_To_Sets.Types_To_Sets"
begin

definition \<open>with_type S P \<longleftrightarrow> S\<noteq>{} \<and> (\<forall>Rep Abs. type_definition Rep Abs S \<longrightarrow> P Rep Abs)\<close>

syntax "_with_type" :: "type \<Rightarrow> 'a => 'b \<Rightarrow> 'c" ("\<forall>\<^sub>\<tau> _=_. _" [0,0,10] 10)
parse_translation \<open>[
  (\<^syntax_const>\<open>_with_type\<close>, fn ctxt => fn [typ_term, carrier, prop] => let
  val typname = case typ_term of 
    Const ("_ofsort", _) $ Free (n, _) $ _ => 
      if n = "" then raise TERM ("parse_transtation _with_type: empty type variable name", [typ_term])
      else if not (String.isPrefix "'" n) then raise TERM ("parse_transtation _with_type: type variable name does not start with '", [typ_term])
      else String.extract (n,1,NONE)
    | _ => (tracing (\<^make_string> typ_term);
         raise TERM ("parse_transtation _with_type: first argument must be a type variable", [typ_term]))
  val typ = TFree("'" ^ typname, dummyS)
  val rep = Free("rep_" ^ typname, dummyT)
  val abs = Free("abs_" ^ typname, dummyT)
  val prop = Syntax_Trans.abs_tr [rep, Syntax_Trans.abs_tr [abs, prop]]
  val propT = (typ --> dummyT) --> (dummyT --> typ) --> HOLogic.boolT
  val prop = Const(\<^syntax_const>\<open>_constrain\<close>, dummyT) $ prop $ Syntax_Phases.term_of_typ ctxt propT
  in Const(\<^const_name>\<open>with_type\<close>, dummyT) $ carrier $ prop end)
]\<close>
term \<open>\<forall>\<^sub>\<tau>'t = N. (rep_t = rep_t)\<close>


lemma with_type_mp: \<open>with_type S P \<Longrightarrow> (\<And>Rep Abs. type_definition Rep Abs S \<Longrightarrow> P Rep Abs \<Longrightarrow> Q Rep Abs) \<Longrightarrow> with_type S Q\<close>
  by (simp add: with_type_def)

lemma with_typeI:
  assumes \<open>S \<noteq> {}\<close>
  assumes \<open>\<And>Rep Abs. type_definition Rep Abs S \<Longrightarrow> P Rep Abs\<close>
  shows \<open>with_type S P\<close>
  using assms by (simp add: with_type_def)

lemma with_type_nonempty: \<open>with_type S P \<Longrightarrow> S \<noteq> {}\<close>
  by (simp add: with_type_def)

lemma with_type_prepare_cancel:
  assumes \<open>with_type S (\<lambda>(_::'a\<Rightarrow>'b) _. P)\<close>
  shows \<open>(\<exists>(Rep::'a\<Rightarrow>'b) Abs. type_definition Rep Abs S) \<Longrightarrow> P\<close>
  using assms by (auto simp add: with_type_def)

end
