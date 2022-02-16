theory With_Type
  imports "HOL-Types_To_Sets.Types_To_Sets"
"HOL-Library.Cardinality"
begin

definition \<open>with_type S P \<longleftrightarrow> S\<noteq>{} \<and> (\<forall>Rep Abs. type_definition Rep Abs S \<longrightarrow> P Rep Abs)\<close>

typedef bla = \<open>{True} :: bool set\<close> by auto
setup_lifting type_definition_bla
print_theorems

term "class.semigroup_add"
definition \<open>with_type2 S C_rep rep_params P \<longleftrightarrow> S\<noteq>{} \<and> C_rep rep_params
    \<and> (\<forall>Rep Abs. type_definition Rep Abs S \<longrightarrow> P (\<lambda>x y. x = Rep y))\<close>
  for S :: \<open>'rep set\<close> and C :: \<open>'abs_params \<Rightarrow> bool\<close> and P :: \<open>('rep \<Rightarrow> 'abs \<Rightarrow> bool) \<Rightarrow> bool\<close>
  and R :: \<open>('rep \<Rightarrow> 'abs \<Rightarrow> bool) \<Rightarrow> ('rep_params \<Rightarrow> 'abs_params \<Rightarrow> bool)\<close>
  and params :: 'abs_params and C_rep :: \<open>'rep_params \<Rightarrow> bool\<close>

term \<open>rel_fun R (\<longleftrightarrow>)\<close>

(* term \<open>with_type2 (UNIV::bool set) (\<lambda>_. True) (\<lambda>rep abs x. True)\<close> *)

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

lemma with_type2I:
  fixes S :: \<open>'a set\<close> and x :: \<open>'c\<close>
  assumes \<open>S \<noteq> {}\<close>
  assumes \<open>C_rep rep_params\<close>
  assumes \<open>\<And>Rep Abs. type_definition Rep Abs S \<Longrightarrow> P (\<lambda>x y. x = Rep y)\<close>
  (* assumes \<open>\<And>(Rep :: 'b\<Rightarrow>'a) Abs (x::'c). type_definition Rep Abs S \<Longrightarrow> C x \<Longrightarrow> P Rep Abs x\<close> *)
  shows \<open>with_type2 S C_rep rep_params P\<close>
  using assms
  by (auto simp add: with_type2_def)

lemma with_type_nonempty: \<open>with_type S P \<Longrightarrow> S \<noteq> {}\<close>
  by (simp add: with_type_def)

lemma with_type2_nonempty: \<open>with_type2 S C p P \<Longrightarrow> S \<noteq> {}\<close>
  by (simp add: with_type2_def)

lemma with_type_prepare_cancel:
  assumes \<open>with_type S (\<lambda>(_::'a\<Rightarrow>'b) _. P)\<close>
  shows \<open>(\<exists>(Rep::'a\<Rightarrow>'b) Abs. type_definition Rep Abs S) \<Longrightarrow> P\<close>
  using assms by (auto simp add: with_type_def)


lemma with_type2_prepare_cancel:
  fixes S :: \<open>'rep set\<close>
  assumes \<open>with_type2 S C p (\<lambda>(_::'rep\<Rightarrow>'abs\<Rightarrow>bool). P)\<close>
  shows \<open>(\<exists>(Rep::'abs\<Rightarrow>'rep) Abs. type_definition Rep Abs S) \<Longrightarrow> P\<close>
  using assms 
  unfolding  with_type2_def
  by auto

(* definition with_type_semigroup_add :: \<open>('abs\<Rightarrow>'abs\<Rightarrow>'abs) \<Rightarrow> bool\<close>
  where \<open>with_type_semigroup_add plus = (\<forall>x\<in>range rep. \<forall>y\<in>range rep. \<forall>z\<in>range rep. plus (plus x y) z = plus x (plus y z))\<close>
  for rep abs plus *)

unbundle lifting_syntax

axiomatization semigroup_on :: \<open>'a set \<Rightarrow> ('a\<Rightarrow>'a\<Rightarrow>'a) \<Rightarrow> bool\<close>

axiomatization 
  carrier :: \<open>int set\<close> and 
  carrier_plus :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close> and 
  rel :: \<open>int \<Rightarrow> 'a::semigroup_add \<Rightarrow> bool\<close> 
  where
  carrier_nonempty: \<open>carrier \<noteq> {}\<close> and
  carrier_semigroup: \<open>(rel ===> rel ===> rel) carrier_plus abs_plus \<Longrightarrow> class.semigroup_add abs_plus\<close>

declare[[show_sorts, show_consts]]
lemma test:
  includes lifting_syntax
  (* assumes \<open>undefined (4::nat)\<close> *)
  shows \<open>with_type2 carrier (semigroup_on carrier) carrier_plus
      (\<lambda>x::int \<Rightarrow> 'abs::semigroup_add \<Rightarrow> bool. undefined (3::nat))\<close>
  apply (rule with_type2I)
  sorry
(* proof (rule with_type2I)
  show \<open>carrier \<noteq> {}\<close>
    by (simp add: carrier_nonempty)
  show \<open>\<forall>x y :: 'c. (x+y)+x = x+(y+x)\<close>
    by (simp add: add.assoc)
  show \<open>\<forall>x y. True\<close>
    by simp
  show a for a sorry
qed *)

lemma with_type2_semigroup_add:
  fixes Rep :: \<open>'abs \<Rightarrow> int\<close>
  assumes \<open>with_type2 S (semigroup_on S) carrier_plus P\<close>
  assumes \<open>\<exists>(Rep :: 'abs\<Rightarrow>int) Abs. type_definition Rep Abs S\<close>
  shows \<open>\<exists>x::'abs \<Rightarrow> 'abs \<Rightarrow> 'abs. class.semigroup_add x\<close>
  by -

lemma T: \<open>(plus :: 'a::plus\<Rightarrow>'a\<Rightarrow>'a) = undefined CARD('a)\<close>
  sorry
lemmas T' = T[internalize_sort "'a::plus"]

setup \<open>
Sign.add_const_constraint (\<^const_name>\<open>plus\<close>, NONE)
\<close>


lemma
  fixes x
  assumes \<open>undefined (4::nat)\<close>
  shows True
proof -
  note * = test
  note ** = test[THEN with_type2_semigroup_add, THEN someI_ex]
  note * = *[unoverload_type 'abs]
  note * = *[OF **]
  note * = *[THEN with_type2_prepare_cancel]
  then have *: \<open>\<exists>(Rep::'abs::type \<Rightarrow> int) Abs::int \<Rightarrow> 'abs::type. type_definition Rep Abs carrier \<Longrightarrow>
  undefined (3::nat)\<close>
    by metis
  note * = *[rotated, cancel_type_definition]
  note ** = test[THEN with_type2_nonempty]
  note * = *[OF **]
  show True by simp
qed

(* TODO: need to get rid of the semigroup_add first, before cancel (otherwise 'abs occurs).

COncept:
- imagine you know S has a semigroup structure with operation pl
- you can show "typedef Rep Abs S \<Longrightarrow> P" with typeclass abs::semigroup
- by removing the type class, you get "semigroup (+)::abs  \<Longrightarrow> typedef Rep Abs S \<Longrightarrow> P" 
     w/o typeclass and for any (+) (matching the type of Rep/Abs)
- we rotate:  "typedef Rep Abs S \<Longrightarrow> semigroup (+)::abs  \<Longrightarrow> P"
- If Rep is an embedding, then "semigroup-structure of pl" implies "semigroup Rep-pl" (where Rep-pl is pl transferred via Rep).
- So we get "typedef Rep Abs S  \<Longrightarrow> P"
- Here we can cancel the typedef
Done.
 *)
lemmas test3a = test3[OF carrier_semigroup]


lemmas test4 = test3[cancel_type_definition]
lemmas test5 = test4[OF with_type2_nonempty[OF test]]
lemmas test6 = test5[OF semigroup_add_axioms, simplified]

thm test[internalize_sort \<open>'c::default\<close>, THEN with_type_prepare_cancel]


end
