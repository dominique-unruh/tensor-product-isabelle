theory With_Type
  imports "HOL-Types_To_Sets.Types_To_Sets"
begin

section \<open>General stuff\<close>

ML \<open>
type with_type_info = {
  class: class,
  rep_class_data: string,
  rep_class_data_thm: thm option, (* Of the form \<open>rep_class_axioms = (const,const)\<close> *)
  nice_rel: thm, (* nice_rel (fst rep_class_data) S (snd rep_class_data) *)
  transfer: thm option (* bi_unique r \<Longrightarrow> right_total r \<Longrightarrow> (snd rep_class_data r ===> (\<longleftrightarrow>)) (fst rep_class_data (Collect (Domainp r))) class.class *)
}
\<close>


ML \<open>
structure With_Type_Data = Generic_Data (
  type T = { by_class: with_type_info Symtab.table, by_const: with_type_info Symtab.table }
  val empty = { by_class = Symtab.empty, by_const = Symtab.empty }
  fun merge ({by_class,by_const}, {by_class=by_class',by_const=by_const'}) =
    {by_class = Symtab.merge (K true) (by_class, by_class'),
     by_const = Symtab.merge (K true) (by_const, by_const') }
)
\<close>

ML \<open>
fun check_with_type_info _ _ = ()
fun add_with_type_info_generic data context = (check_with_type_info context data;
  With_Type_Data.map (fn {by_class,by_const} => 
    {by_class = Symtab.update (#class data, data) by_class,
     by_const = Symtab.update (#rep_class_data data, data) by_const}) context
)
val add_with_type_info_global = Context.theory_map o add_with_type_info_generic
fun get_with_type_info_by_const_generic context const = 
  Symtab.lookup (With_Type_Data.get context |> #by_const) const
val get_with_type_info_by_const = get_with_type_info_by_const_generic o Context.Proof
\<close>

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
definition \<open>with_type2 = (\<lambda>(C,R) (S,rep_ops) P. S\<noteq>{} \<and> C S rep_ops \<and> nice_rel C S R
    \<and> (\<forall>Rep Abs abs_ops. type_definition Rep Abs S \<longrightarrow> (R (\<lambda>x y. x = Rep y) rep_ops abs_ops) \<longrightarrow> 
            P Rep Abs))\<close>
  for S :: \<open>'rep set\<close> and P :: \<open>('abs \<Rightarrow> 'rep) \<Rightarrow> ('rep \<Rightarrow> 'abs) \<Rightarrow> bool\<close>
  and R :: \<open>('rep \<Rightarrow> 'abs \<Rightarrow> bool) \<Rightarrow> ('rep_ops \<Rightarrow> 'abs_ops \<Rightarrow> bool)\<close>
  and C :: \<open>'rep set \<Rightarrow> 'rep_ops \<Rightarrow> bool\<close> and rep_ops :: \<open>'rep_ops\<close>
(* P should also get Abs. Abs is kind-of inv Rep, but on the wrong inputs, we do not know what it is.
Those do not matter but it may be convenient to have access to the same Abs as is used by type_definition.

Having rep_ops might also be nice.
 *)

definition with_type_class_type where \<open>with_type_class_type = ((\<lambda>_ (_::unit). True), (\<lambda>_. (=)))\<close>

lemma nice_rel_type': \<open>nice_rel (fst with_type_class_type) S (snd with_type_class_type)\<close>
  by (simp add: with_type_class_type_def nice_rel_def Domainp_iff)


setup \<open>
add_with_type_info_global {
  class = \<^class>\<open>type\<close>,
  rep_class_data = \<^const_name>\<open>with_type_class_type\<close>,
  nice_rel = @{thm nice_rel_type'},
  rep_class_data_thm = NONE,
  transfer = NONE
}
\<close>

definition \<open>with_type S P \<longleftrightarrow> S\<noteq>{} \<and> (\<forall>Rep Abs. type_definition Rep Abs S \<longrightarrow> P Rep Abs)\<close>

(* Demonstration *)
lemma \<open>with_type S P = with_type2 with_type_class_type (S,()) P\<close>
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
  fixes Sp :: \<open>'a set \<times> 'c\<close> and CR
  defines \<open>C \<equiv> fst CR\<close> and \<open>R \<equiv> snd CR\<close> and \<open>S \<equiv> fst Sp\<close> and \<open>p \<equiv> snd Sp\<close>
  assumes \<open>S \<noteq> {}\<close>
  assumes \<open>C S p\<close>
  assumes \<open>nice_rel C S R\<close>
  assumes \<open>\<And>Rep Abs abs_ops. type_definition Rep Abs S \<Longrightarrow> R (\<lambda>x y. x = Rep y) p abs_ops \<Longrightarrow> P Rep Abs\<close>
  shows \<open>with_type2 CR Sp P\<close>
  using assms
  by (auto simp add: with_type2_def case_prod_beta)

lemma with_type_nonempty: \<open>with_type S P \<Longrightarrow> S \<noteq> {}\<close>
  by (simp add: with_type_def)

lemma with_type2_nonempty: \<open>with_type2 CR Sp P \<Longrightarrow> fst Sp \<noteq> {}\<close>
  by (simp add: with_type2_def case_prod_beta)

lemma with_type_prepare_cancel:
  assumes \<open>with_type S (\<lambda>(_::'a\<Rightarrow>'b) _. P)\<close>
  shows \<open>(\<exists>(Rep::'a\<Rightarrow>'b) Abs. type_definition Rep Abs S) \<Longrightarrow> P\<close>
  using assms by (auto simp add: with_type_def)

lemma with_type2_prepare_cancel:
  fixes Sp :: \<open>'rep set \<times> _\<close>
  assumes wt: \<open>with_type2 CR Sp (\<lambda>_ (_::'rep\<Rightarrow>'abs). P)\<close>
  assumes ex: \<open>(\<exists>(Rep::'abs\<Rightarrow>'rep) Abs. type_definition Rep Abs (fst Sp))\<close>
  shows P
proof -
  define S p C R where \<open>S = fst Sp\<close> and \<open>p = snd Sp\<close> and \<open>C = fst CR\<close> and \<open>R = snd CR\<close>
  with ex obtain Rep :: \<open>'abs\<Rightarrow>'rep\<close> and Abs where td: \<open>type_definition Rep Abs S\<close>
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
    by (simp_all add: with_type2_def p_def R_def S_def C_def case_prod_beta)
  from nice[unfolded nice_rel_def, rule_format, OF \<open>bi_unique r\<close> \<open>right_total r\<close> Sr \<open>C S p\<close>]
  obtain abs_ops where abs_ops: \<open>R (\<lambda>x y. x = Rep y) p abs_ops\<close>
    apply atomize_elim by (auto simp: r_def)
  from td abs_ops wt
  show P
    by (auto simp: with_type2_def case_prod_beta S_def p_def R_def)
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

lemma with_type2_class_axioms:
  fixes Rep :: \<open>'abs \<Rightarrow> 'rep\<close>
    and CR :: \<open>_ \<times> (('rep\<Rightarrow>'abs\<Rightarrow>bool) \<Rightarrow> ('rep_ops \<Rightarrow> 'abs_ops \<Rightarrow> bool))\<close>
    and Sp
    and R :: \<open>('rep\<Rightarrow>'abs\<Rightarrow>bool) \<Rightarrow> ('rep_ops \<Rightarrow> 'abs_ops \<Rightarrow> bool)\<close>
    and R2 :: \<open>('rep\<Rightarrow>'abs2\<Rightarrow>bool) \<Rightarrow> ('rep_ops \<Rightarrow> 'abs_ops2 \<Rightarrow> bool)\<close>
  defines \<open>C \<equiv> fst CR\<close> and \<open>R \<equiv> snd CR\<close> and \<open>S \<equiv> fst Sp\<close> and \<open>p \<equiv> snd Sp\<close>
  assumes trans: \<open>\<And>r :: 'rep \<Rightarrow> 'abs2 \<Rightarrow> bool. bi_unique r \<Longrightarrow> right_total r \<Longrightarrow> (R2 r ===> (\<longleftrightarrow>)) (C (Collect (Domainp r))) axioms\<close>
  assumes nice: \<open>nice_rel C S R2\<close>
  assumes wt: \<open>with_type2 CR Sp P\<close>
  assumes ex: \<open>\<exists>(Rep :: 'abs2\<Rightarrow>'rep) Abs. type_definition Rep Abs S\<close>
  shows \<open>\<exists>x::'abs_ops2. axioms x\<close>
proof -
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

  from wt have sg: \<open>C S p\<close>
    by (simp_all add: with_type2_def C_def S_def p_def case_prod_beta)

  with nice have \<open>Domainp (R2 r) p\<close>
    by (simp add: bi_unique_r nice_rel_def rS right_total_r)
  
  with sg
  have \<open>\<exists>x :: 'abs_ops2. axioms x\<close>
    apply (transfer' fixing: R2 S p)
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

definition with_type_class_semigroup_add where
  \<open>with_type_class_semigroup_add = (semigroup_on, \<lambda>r. r ===> r ===> r)\<close>

lemma semigroup_on_transfer: 
  \<open>((r ===> r ===> r) ===> (\<longleftrightarrow>)) (semigroup_on (Collect (Domainp r))) class.semigroup_add\<close>
    if [transfer_rule]: \<open>bi_unique r\<close> \<open>right_total r\<close>
    for r :: \<open>'rep \<Rightarrow> 'abs \<Rightarrow> bool\<close>
  unfolding semigroup_on_def class.semigroup_add_def
  apply (rule aux)
   apply transfer_prover
  unfolding Domainp_rel_fun_iff[OF bi_unique_left_unique[OF \<open>bi_unique r\<close>]]
  by auto

lemma nice_rel_semigroup_on: \<open>nice_rel semigroup_on S (\<lambda>r. r ===> r ===> r)\<close>
  by (simp add: Domainp_rel_fun_iff bi_unique_left_unique semigroup_on_def nice_rel_def)

(* lemma with_type2_semigroup_add:
  fixes Rep :: \<open>'abs \<Rightarrow> int\<close>
  assumes wt: \<open>with_type2 with_type_class_semigroup_add Sp P\<close>
  assumes ex: \<open>\<exists>(Rep :: 'abs2\<Rightarrow>int) Abs. type_definition Rep Abs (fst Sp)\<close>
  shows \<open>\<exists>x::'abs2 \<Rightarrow> 'abs2 \<Rightarrow> 'abs2. class.semigroup_add x\<close>
  using _ _ wt ex
  apply (rule with_type2_class_axioms)
   apply (auto simp add: with_type_class_semigroup_add_def intro!: semigroup_on_transfer)
  by (simp add: nice_rel_semigroup_on) *)

lemma semigroup_on_transfer': 
  \<open>bi_unique r \<Longrightarrow> right_total r \<Longrightarrow> (snd with_type_class_semigroup_add r ===> (\<longleftrightarrow>)) (fst with_type_class_semigroup_add (Collect (Domainp r))) class.semigroup_add\<close>
  by (auto simp add: with_type_class_semigroup_add_def intro!: semigroup_on_transfer)

lemma nice_rel_semigroup_on': \<open>nice_rel (fst with_type_class_semigroup_add) S (snd with_type_class_semigroup_add)\<close>
  by (simp add: nice_rel_semigroup_on with_type_class_semigroup_add_def)

(* lemmas with_type2_semigroup_add' = with_type2_class_axioms[OF semigroup_on_transfer' nice_rel_semigroup_on'] *)

section \<open>Ring\<close>

type_synonym 'a ring_ops = \<open>('a \<Rightarrow> 'a \<Rightarrow> 'a) \<times> 'a \<times> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<times> ('a \<Rightarrow> 'a) \<times> ('a \<Rightarrow> 'a \<Rightarrow> 'a)\<close>

axiomatization with_type_class_ring :: 
  "('a set \<Rightarrow> 'a ring_ops \<Rightarrow> bool) \<times> (('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> 'b ring_ops \<Rightarrow> 'c ring_ops \<Rightarrow> bool)"

lemma ring_transfer'[unfolded case_prod_unfold]: 
  \<open>bi_unique r \<Longrightarrow> right_total r \<Longrightarrow> 
    (snd with_type_class_ring r ===> (\<longleftrightarrow>)) (fst with_type_class_ring (Collect (Domainp r))) (\<lambda>(a,b,c,d,e). class.ring a b c d e)\<close>
  sorry

lemma nice_rel_ring': \<open>nice_rel (fst with_type_class_ring) S (snd with_type_class_ring)\<close>
  sorry


section \<open>Finite\<close>

definition with_type_class_finite :: \<open>('a set \<Rightarrow> unit \<Rightarrow> bool) \<times> (('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> (unit \<Rightarrow> unit \<Rightarrow> bool))\<close>
  where \<open>with_type_class_finite = (\<lambda>F _. finite F, \<lambda>_. (=))\<close>

lemma finite_transfer'[unfolded case_prod_unfold]:
  fixes r :: \<open>'rep\<Rightarrow>'abs\<Rightarrow>bool\<close>
  assumes [transfer_rule]: \<open>bi_unique r\<close> \<open>right_total r\<close>
  shows \<open>(snd with_type_class_finite r ===> (\<longleftrightarrow>)) (fst with_type_class_finite (Collect (Domainp r))) (\<lambda>_::unit. class.finite TYPE('abs))\<close>
  unfolding class.finite_def with_type_class_finite_def fst_conv
  by transfer_prover

lemma nice_rel_finite': \<open>nice_rel (fst with_type_class_finite) S (snd with_type_class_finite)\<close>
  by (auto simp: with_type_class_finite_def nice_rel_def)

setup \<open>
add_with_type_info_global {
  class = \<^class>\<open>finite\<close>,
  rep_class_data = \<^const_name>\<open>with_type_class_finite\<close>,
  nice_rel = @{thm nice_rel_finite'},
  rep_class_data_thm = NONE,
  transfer = SOME @{thm finite_transfer'}
}
\<close>

setup \<open>
add_with_type_info_global {
  class = \<^class>\<open>semigroup_add\<close>,
  rep_class_data = \<^const_name>\<open>with_type_class_semigroup_add\<close>,
  nice_rel = @{thm nice_rel_semigroup_on'},
  rep_class_data_thm = NONE,
  transfer = SOME @{thm semigroup_on_transfer'}
}
\<close>

setup \<open>
add_with_type_info_global {
  class = \<^class>\<open>ring\<close>,
  rep_class_data = \<^const_name>\<open>with_type_class_ring\<close>,
  nice_rel = @{thm nice_rel_ring'},
  rep_class_data_thm = NONE,
  transfer = SOME @{thm ring_transfer'}
}
\<close>


section \<open>Semigroup example\<close>

axiomatization 
  carrier :: \<open>int set\<close> and 
  carrier_plus :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close> and 
  rel :: \<open>int \<Rightarrow> 'a::semigroup_add \<Rightarrow> bool\<close> 
  where
  carrier_nonempty: \<open>carrier \<noteq> {}\<close> and
  carrier_semigroup: \<open>semigroup_on carrier carrier_plus\<close>

definition "carrier_both = (carrier,carrier_plus)"

lemma example_semigroup:
  includes lifting_syntax
  shows \<open>with_type2 with_type_class_semigroup_add carrier_both
      (\<lambda>Rep (Abs::int \<Rightarrow> 'abs::semigroup_add). undefined (3::nat))\<close>
  apply (rule with_type2I)
  apply (simp_all add: with_type_class_semigroup_add_def carrier_both_def)
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

lemma example_type:
  includes lifting_syntax
  shows \<open>with_type2 with_type_class_type undefined
      (\<lambda>Rep (Abs::int \<Rightarrow> 'abs). undefined (3::nat))\<close>
  sorry

lemma example_ring:
  includes lifting_syntax
  shows \<open>with_type2 with_type_class_ring undefined
      (\<lambda>Rep (Abs::int \<Rightarrow> 'abs::ring). undefined (3::nat))\<close>
  sorry


lemma example_finite:
  includes lifting_syntax
  shows \<open>with_type2 with_type_class_finite undefined
      (\<lambda>Rep (Abs::int \<Rightarrow> 'abs::finite). undefined (3::nat))\<close>
  sorry


ML \<open>
Unoverload_Type.unoverload_type (Context.Proof \<^context>) [("'a",0)]
@{lemma \<open>undefined::'a::{field,finite} == undefined\<close> by simp}
\<close>

term with_type2

ML \<open>
fun with_type_cancel ctxt thm = let

val (const, abs_type) = case Thm.prop_of thm of
    \<^Const_>\<open>Trueprop\<close> $ (\<^Const_>\<open>with_type2 _ _ abs _\<close> $ Const(const,_) $ _ $ _) => (const,abs)
  | t => raise TERM ("with_type_cancel: theorem must be of the form (with_type2 constant ...)", [t])

val abs_type_name = case abs_type of
  TVar (n,_) => n
  | _ => raise TYPE ("with_type_cancel: abstract type must be a type variable (?'something)", [abs_type], [Thm.prop_of thm])

val info = get_with_type_info_by_const ctxt const |> the

(* "with_type2 CR ?Sp ?P \<Longrightarrow>
    \<exists>Rep Abs. type_definition Rep Abs (fst ?Sp) \<Longrightarrow> \<exists>x. class.name x" *)
(* May be NONE *)
val with_type2_class_axioms = case #transfer info of SOME transfer => 
      (@{thm with_type2_class_axioms} OF [transfer, #nice_rel info])
      |> (Tactic.assume_tac ctxt 1  THEN  Tactic.assume_tac ctxt 1) |> Seq.hd |> SOME
  | NONE => NONE

(* class.name (\<dots> using ?'abs) \<Longrightarrow> with_type2 CR Sp (\<lambda>_ _. P) *)
(* class.name part may be absent for some type classes *)
val unoverloaded = Unoverload_Type.unoverload_type (Context.Proof ctxt) [abs_type_name] thm

(* \<exists>(Rep::?'abs2\<Rightarrow>_) Abs. type_definition Rep Abs (fst Sp) \<Longrightarrow> \<exists>x::?'abs_params2. class.name x *)
(* May be NONE *)
val ex_class = Option.map (fn th => th OF [thm]) with_type2_class_axioms

(* \<exists>(Rep::?'abs2\<Rightarrow>_) Abs. type_definition Rep Abs (fst Sp) \<Longrightarrow> class.name (SOME \<dots>) *)
(* May be NONE *)
val class_some = Option.map (fn thm => @{thm someI_ex} OF [thm]) ex_class

(* \<exists>(Rep::?'abs\<Rightarrow>_) Abs. type_definition Rep Abs (fst Sp) \<Longrightarrow> with_type2 CR Sp (\<lambda>_ _. P) *)
val unoverloaded' = case class_some of SOME thm => unoverloaded OF [thm] | NONE => unoverloaded

(* \<exists>(Rep::?'abs\<Rightarrow>_) Abs. type_definition Rep Abs (fst Sp) [TWICE!] \<Longrightarrow> P *)
val no_with_type2 = @{thm with_type2_prepare_cancel} OF [unoverloaded']

(* \<exists>(Rep::?'abs\<Rightarrow>_) Abs. type_definition Rep Abs (fst Sp) \<Longrightarrow> P *)
val no_repetition = Tactic.distinct_subgoals_tac no_with_type2 |> Seq.hd

(* fst Sp \<noteq> {} \<Longrightarrow> P *)
val removed_abs_type = Local_Typedef.cancel_type_definition no_repetition

(* fst Sp \<noteq> {} *)
val non_empty = @{thm with_type2_nonempty} OF [thm]
val final_thm = removed_abs_type OF [non_empty]
in
final_thm
end
\<close>

ML \<open>
with_type_cancel \<^context> @{thm example_type}
\<close>


(* 
lemma erasure_example:
  assumes \<open>undefined (4::nat)\<close>
  shows \<open>undefined (3::nat)\<close>
proof -
  note * = example_semigroup
  note ** = example_semigroup[THEN with_type2_semigroup_add, THEN someI_ex]
  note * = *[unoverload_type 'abs] (* unoverloaded *)
  note * = *[OF **] (* unoverloaded' *)
  note * = *[THEN with_type2_prepare_cancel] (* no_with_type2 *)
  then have *: \<open>\<exists>(Rep::'abs::type \<Rightarrow> int) Abs::int \<Rightarrow> 'abs::type. type_definition Rep Abs (fst carrier_both) \<Longrightarrow>
                undefined (3::nat)\<close>
    by metis  (* no_repetition *)
  note * = *[cancel_type_definition] (* removed_abs_type *)
  note ** = example_semigroup[THEN with_type2_nonempty] 
  note * = *[OF **]
  then show ?thesis by simp
qed *)

end
