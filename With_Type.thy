theory With_Type
  imports "HOL-Types_To_Sets.Types_To_Sets"
begin

section \<open>General stuff\<close>

definition \<open>with_type S P \<longleftrightarrow> S\<noteq>{} \<and> (\<forall>Rep Abs. type_definition Rep Abs S \<longrightarrow> P Rep Abs)\<close>

definition nice_rel where \<open>nice_rel C S R \<longleftrightarrow> (\<forall>r rp. bi_unique r \<longrightarrow> right_total r \<longrightarrow> S = Collect (Domainp r) \<longrightarrow> C S rp \<longrightarrow> (Domainp (R r) rp))\<close>

text \<open>
\<^term>\<open>S\<close> -- the carrier set of the representation of the type

\<^term>\<open>rep_ops\<close> -- operations of the representation type (i.e., operations like addition on the set or similar)

\<^term>\<open>R\<close> -- transfers a relation \<^term>\<open>r\<close> between representation and abstract type to a relation between representation operations and abstract operations
(\<^term>\<open>r\<close> is always bi-unique and right-total)

\<^term>\<open>P\<close> -- the predicate that we claim holds.
It can work on the type \<^typ>\<open>'abs\<close> (which is type-classed) but it also gets the relation \<^term>\<open>r\<close>
so that it can transfer things back and forth.
(We could also give \<^term>\<open>P\<close> just \<^term>\<open>Rep\<close> instead of the relation. Maybe simpler?)

If \<^term>\<open>P\<close> does not contain \<^typ>\<open>'abs\<close>, we can erase the \<^term>\<open>with_type2\<close> using the \<open>Types_To_Sets\<close> mechanism.
See lemma \<open>erasure_example\<close> below.
\<close>
definition \<open>with_type2 S R C rep_ops P \<longleftrightarrow> S\<noteq>{} \<and> C S rep_ops \<and> nice_rel C S R
    \<and> (\<forall>Rep Abs abs_ops. type_definition Rep Abs S \<longrightarrow> (R (\<lambda>x y. x = Rep y) rep_ops abs_ops) \<longrightarrow> 
            P Rep Abs)\<close>
  for S :: \<open>'rep set\<close> and P :: \<open>('abs \<Rightarrow> 'rep) \<Rightarrow> ('rep \<Rightarrow> 'abs) \<Rightarrow> bool\<close>
  and R :: \<open>('rep \<Rightarrow> 'abs \<Rightarrow> bool) \<Rightarrow> ('rep_ops \<Rightarrow> 'abs_ops \<Rightarrow> bool)\<close>
  and C :: \<open>'rep set \<Rightarrow> 'rep_ops \<Rightarrow> bool\<close> and rep_ops :: \<open>'rep_ops\<close>
(* P should also get Abs. Abs is kind-of inv Rep, but on the wrong inputs, we do not know what it is.
Those do not matter but it may be convenient to have access to the same Abs as is used by type_definition.

Having rep_ops might also be nice.
 *)

definition with_type_class_type where \<open>with_type_class_type S (x::unit) = True\<close>

(* Demonstration *)
lemma \<open>with_type S P = with_type2 S (\<lambda>_. (=)) with_type_class_type () P\<close>
  by (auto simp: with_type_def with_type2_def with_type_class_type_def nice_rel_def)

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
  assumes \<open>C_rep S rep_ops\<close>
  assumes \<open>nice_rel C_rep S R\<close>
  assumes \<open>\<And>Rep Abs abs_ops. type_definition Rep Abs S \<Longrightarrow> R (\<lambda>x y. x = Rep y) rep_ops abs_ops \<Longrightarrow> P Rep Abs\<close>
  shows \<open>with_type2 S R C_rep rep_ops P\<close>
  using assms
  by (auto simp add: with_type2_def)

lemma with_type_nonempty: \<open>with_type S P \<Longrightarrow> S \<noteq> {}\<close>
  by (simp add: with_type_def)

lemma with_type2_nonempty: \<open>with_type2 S R C p P \<Longrightarrow> S \<noteq> {}\<close>
  by (simp add: with_type2_def)

lemma with_type_prepare_cancel:
  assumes \<open>with_type S (\<lambda>(_::'a\<Rightarrow>'b) _. P)\<close>
  shows \<open>(\<exists>(Rep::'a\<Rightarrow>'b) Abs. type_definition Rep Abs S) \<Longrightarrow> P\<close>
  using assms by (auto simp add: with_type_def)

lemma with_type2_prepare_cancel:
  fixes S :: \<open>'rep set\<close>
  assumes wt: \<open>with_type2 S R C p (\<lambda>_ (_::'rep\<Rightarrow>'abs). P)\<close>
  assumes ex: \<open>(\<exists>(Rep::'abs\<Rightarrow>'rep) Abs. type_definition Rep Abs S)\<close>
  shows \<open>P\<close>
proof -
  from ex obtain Rep :: \<open>'abs\<Rightarrow>'rep\<close> and Abs where td: \<open>type_definition Rep Abs S\<close>
    by auto
  define r where \<open>r = (\<lambda>x y. x = Rep y)\<close>
  have [simp]: \<open>bi_unique r\<close> \<open>right_total r\<close>
    using r_def td typedef_bi_unique apply blast
    by (simp add: r_def right_totalI)
  have Sr: \<open>S = Collect (Domainp r)\<close>
    using type_definition.Rep[OF td] 
    apply (auto simp: r_def intro!: DomainPI)
    apply (subst type_definition.Abs_inverse[OF td])
    by auto
  from wt have nice: \<open>nice_rel C S R\<close> and \<open>C S p\<close>
    by (simp_all add: with_type2_def)
  from nice[unfolded nice_rel_def, rule_format, OF \<open>bi_unique r\<close> \<open>right_total r\<close> Sr \<open>C S p\<close>]
  obtain abs_ops where abs_ops: \<open>R (\<lambda>x y. x = Rep y) p abs_ops\<close>
    apply atomize_elim by (auto simp: r_def)
  from td abs_ops wt
  show P
    unfolding with_type2_def
    by auto
qed

unbundle lifting_syntax

lemma Domainp_rel_fun_iff:
  assumes \<open>left_unique R\<close>
  shows \<open>Domainp (R ===> S) p \<longleftrightarrow> (\<forall>x. Domainp R x \<longrightarrow> Domainp S (p x))\<close>
proof 
  show \<open>Domainp (R ===> S) p \<Longrightarrow> \<forall>x. Domainp R x \<longrightarrow> Domainp S (p x)\<close>
    by (auto simp add: Domainp_iff rel_fun_def)
  assume asm: \<open>\<forall>x. Domainp R x \<longrightarrow> Domainp S (p x)\<close>
  show \<open>Domainp (R ===> S) p\<close>
  proof (intro DomainPI rel_funI)
    fix x y assume \<open>R x y\<close>
    then have \<open>Domainp R x\<close>
      by (simp add: DomainPI)
    then have \<open>Domainp S (p x)\<close>
      by (simp add: asm)
    from \<open>R x y\<close>
    have \<open>R (SOME x. R x y) y\<close>
      by (metis verit_sko_ex')
    with \<open>left_unique R\<close> \<open>R x y\<close>
    have x_some: \<open>x = (SOME x. R x y)\<close>
      by (auto simp: left_unique_def)
    from \<open>Domainp S (p x)\<close>
    have \<open>S (p x) (SOME y. S (p x) y)\<close>
      by (metis DomainpE verit_sko_ex')
    then show \<open>S (p x) (SOME y'. S (p (SOME x. R x y)) y')\<close>
      unfolding x_some by simp
  qed
qed

lemma aux:
  assumes \<open>(R ===> (\<longleftrightarrow>)) A B\<close>
  assumes \<open>\<And>x. Domainp R x \<Longrightarrow> C x\<close>
  shows \<open>(R ===> (\<longleftrightarrow>)) (\<lambda>x. C x \<and> A x) B\<close>
  by (smt (verit) DomainPI assms(1) assms(2) rel_fun_def)

lemma bi_unique_left_unique: \<open>bi_unique R \<Longrightarrow> left_unique R\<close>
  by (simp add: bi_unique_alt_def)

axiomatization 
  carrier :: \<open>int set\<close> and 
  carrier_plus :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close> and 
  rel :: \<open>int \<Rightarrow> 'a::semigroup_add \<Rightarrow> bool\<close> 
  where
  carrier_nonempty: \<open>carrier \<noteq> {}\<close> and
  carrier_semigroup: \<open>semigroup_on carrier carrier_plus\<close>

(* lemma nice_sg: \<open>nice_rel semigroup_on carrier (\<lambda>r. r ===> r ===> r)\<close> (* Essentially the same as semigroup_on_Domainp *)
  by (auto simp: nice_rel_def intro!: semigroup_on_Domainp) *)


lemma with_type2_class_axioms:
  fixes Rep :: \<open>'abs \<Rightarrow> 'rep\<close>
    and R :: \<open>('rep\<Rightarrow>'abs\<Rightarrow>bool) \<Rightarrow> ('rep_ops \<Rightarrow> 'abs_ops \<Rightarrow> bool)\<close>
    and R2 :: \<open>('rep\<Rightarrow>'abs2\<Rightarrow>bool) \<Rightarrow> ('rep_ops \<Rightarrow> 'abs_ops2 \<Rightarrow> bool)\<close>
  assumes trans: \<open>\<And>r :: 'rep \<Rightarrow> 'abs2 \<Rightarrow> bool. bi_unique r \<Longrightarrow> right_total r \<Longrightarrow> (R2 r ===> (\<longleftrightarrow>)) (C (Collect (Domainp r))) axioms\<close>
  assumes nice: \<open>nice_rel C S R2\<close>
  assumes wt: \<open>with_type2 S R C rep_plus P\<close>
  assumes ex: \<open>\<exists>(Rep :: 'abs2\<Rightarrow>'rep) Abs. type_definition Rep Abs S\<close>
  shows \<open>\<exists>x::'abs_ops2. axioms x\<close>
proof -
  (* define R where \<open>R = (\<lambda>r::'rep\<Rightarrow>'abs\<Rightarrow>bool. r ===> r ===> r)\<close> *)
  (* define R2 where \<open>R2 = (\<lambda>r::'rep\<Rightarrow>'abs2\<Rightarrow>bool. r ===> r ===> r)\<close> *)
  from ex obtain Rep :: \<open>'abs2\<Rightarrow>'rep\<close> and Abs where td: \<open>type_definition Rep Abs S\<close>
    by auto
  define r where \<open>r x y = (x = Rep y)\<close> for x y
  have bi_unique_r: \<open>bi_unique r\<close>
    using bi_unique_def td type_definition.Rep_inject r_def by fastforce
  have right_total_r: \<open>right_total r\<close>
    by (simp add: right_totalI r_def)
  have right_total_R[transfer_rule]: \<open>right_total (r ===> r ===> r)\<close>
    by (meson bi_unique_r right_total_r bi_unique_alt_def right_total_fun)
  note trans = trans[OF bi_unique_r, OF right_total_r, transfer_rule]

  from td
  have rS: \<open>Collect (Domainp r) = S\<close>
    apply (auto simp: r_def Domainp_iff type_definition.Rep)
    by (meson type_definition.Rep_cases)

  from wt have (* nice: \<open>nice_rel C S R\<close> and *) sg: \<open>C S rep_plus\<close>
    by (simp_all add: with_type2_def)

  with nice have \<open>Domainp (R2 r) rep_plus\<close>
    by (simp add: bi_unique_r nice_rel_def rS right_total_r)
  
  with sg
  have \<open>\<exists>x :: 'abs_ops2. axioms x\<close>
    apply (transfer' fixing: R2 S rep_plus)
    using apply_rsp' local.trans rS by fastforce
  
  then obtain abs_plus :: 'abs_ops2 
    where abs_plus: \<open>axioms abs_plus\<close>
    apply atomize_elim by auto

  then show ?thesis
    by auto
qed

section \<open>\<open>semigroup_on\<close>\<close>

definition semigroup_on :: \<open>'rep set \<Rightarrow> ('rep\<Rightarrow>'rep\<Rightarrow>'rep) \<Rightarrow> bool\<close> where
  \<open>semigroup_on S p \<longleftrightarrow> (\<forall>x\<in>S. \<forall>y\<in>S. p x y \<in> S) \<and> 
      (\<forall>x\<in>S. \<forall>y\<in>S. \<forall>z\<in>S. p (p x y) z = p x (p y z))\<close>


lemma
    semigroup_on_transfer: \<open>((r ===> r ===> r) ===> (\<longleftrightarrow>)) (semigroup_on (Collect (Domainp r))) class.semigroup_add\<close>
    if [transfer_rule]: \<open>bi_unique r\<close> \<open>right_total r\<close>
    for r :: \<open>'rep \<Rightarrow> 'abs \<Rightarrow> bool\<close>
  unfolding semigroup_on_def class.semigroup_add_def
  apply (rule aux)
   apply transfer_prover
  unfolding Domainp_rel_fun_iff[OF bi_unique_left_unique[OF \<open>bi_unique r\<close>]]
  by auto


lemma nice_rel_semigroup_on: \<open>nice_rel semigroup_on S (\<lambda>r. r ===> r ===> r)\<close>
  by (simp add: Domainp_rel_fun_iff bi_unique_left_unique semigroup_on_def nice_rel_def)

lemma with_type2_semigroup_add:
  fixes Rep :: \<open>'abs \<Rightarrow> int\<close>
  assumes wt: \<open>with_type2 S (\<lambda>r::int\<Rightarrow>'abs\<Rightarrow>bool. r ===> r ===> r) semigroup_on rep_plus P\<close>
  assumes ex: \<open>\<exists>(Rep :: 'abs2\<Rightarrow>int) Abs. type_definition Rep Abs S\<close>
  shows \<open>\<exists>x::'abs2 \<Rightarrow> 'abs2 \<Rightarrow> 'abs2. class.semigroup_add x\<close>
  using semigroup_on_transfer nice_rel_semigroup_on wt ex
  by (rule with_type2_class_axioms)


section \<open>Semigroup example\<close>

lemma example:
  includes lifting_syntax
  shows \<open>with_type2 carrier (\<lambda>r. r ===> r ===> r) semigroup_on carrier_plus
      (\<lambda>Rep (Abs::int \<Rightarrow> 'abs::semigroup_add). undefined (3::nat))\<close>
  apply (rule with_type2I)
     apply (rule carrier_nonempty)
    apply (rule carrier_semigroup)
   apply (rule nice_rel_semigroup_on)
proof -
  fix Rep :: \<open>'abs \<Rightarrow> int\<close> and Abs and pls
  assume \<open>type_definition Rep Abs carrier\<close>
  define r where \<open>r = (\<lambda>x y. x = Rep y)\<close>
  have [transfer_rule]: \<open>bi_unique r\<close>
    using \<open>type_definition Rep Abs carrier\<close> bi_unique_def r_def type_definition.Rep_inject by fastforce
  have [transfer_rule]: \<open>right_total r\<close>
    by (simp add: r_def right_total_def)
  assume [transfer_rule]: \<open>(r ===> r ===> r) carrier_plus pls\<close>
  have \<open>pls x y = pls y x\<close> for x y
    apply transfer
    sorry
  show \<open>undefined 3\<close>
    sorry
qed


lemma erasure_example:
  assumes \<open>undefined (4::nat)\<close>
  shows \<open>undefined (3::nat)\<close>
proof -
  note * = example
  note ** = example[THEN with_type2_semigroup_add, THEN someI_ex]
  note * = *[unoverload_type 'abs]
  note * = *[OF **]
  note * = *[THEN with_type2_prepare_cancel]
  then have *: \<open>\<exists>(Rep::'abs::type \<Rightarrow> int) Abs::int \<Rightarrow> 'abs::type. type_definition Rep Abs carrier \<Longrightarrow>
                undefined (3::nat)\<close>
    by metis
  note * = *[rotated, cancel_type_definition]
  note ** = example[THEN with_type2_nonempty]
  note * = *[OF **]
  then show ?thesis by simp
qed

end
