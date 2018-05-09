theory Generalised
  imports Main "~~/src/HOL/Lattice/CompleteLattice"
begin

datatype 'a branch = Positive 'a | Negative 'a

type_synonym 'a pc = "'a branch set"

fun view :: "('a::lattice) pc \<Rightarrow> 'a set" where
"view pc = {l. (\<forall>k. Positive k \<in> pc \<longrightarrow> k \<sqsubseteq> l) \<and> (\<forall> k. Negative k \<in> pc \<longrightarrow> \<not> (k \<sqsubseteq> l)) }"

fun candidate :: "('a::complete_lattice) pc \<Rightarrow> 'a" where
"candidate pc = \<Squnion>{k. Positive k \<in> pc}"

lemma positive: "Positive k \<in> pc \<longrightarrow> k \<sqsubseteq> candidate pc"
  apply (simp add: Join_lower)
  done

lemma decision_left: "(\<forall>k. Negative k \<in> pc \<longrightarrow> \<not> (k \<sqsubseteq> candidate pc)) \<Longrightarrow> view pc \<noteq> {}"
  apply simp
  apply (rule_tac x = "candidate pc" in exI)
  apply (rule conjI)
   apply (insert positive)
  apply auto
  done

lemma decision_right: "view pc \<noteq> {} \<Longrightarrow> (\<forall> k. Negative k \<in> pc \<longrightarrow> \<not> (k \<sqsubseteq> candidate pc))"
  apply auto
  apply (subgoal_tac "\<Squnion>{k. Positive k \<in> pc} \<sqsubseteq> x")
   apply (insert leq_trans)
   apply blast
  apply (insert JoinI)
proof -
fix x :: 'a and k :: 'a
  assume a1: "\<forall>k. Positive k \<in> pc \<longrightarrow> k \<sqsubseteq> x"
  obtain aa :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a" where
    "\<forall>x0 x1. (\<exists>v2. v2 \<in> x1 \<and> \<not> v2 \<sqsubseteq> x0) = (aa x0 x1 \<in> x1 \<and> \<not> aa x0 x1 \<sqsubseteq> x0)"
    by moura
  then have "\<forall>A a. aa a A \<in> A \<and> \<not> aa a A \<sqsubseteq> a \<or> \<Squnion>A \<sqsubseteq> a"
    by (meson Join_least)
  then show "\<Squnion>{a. Positive a \<in> pc} \<sqsubseteq> x"
    using a1 by (metis mem_Collect_eq)
qed

theorem decision: "(\<forall>k. Negative k \<in> pc \<longrightarrow> \<not> (k \<sqsubseteq> candidate pc)) \<longleftrightarrow> view pc \<noteq> {}"
  apply (rule iffI)
   apply (rule decision_left)
   apply simp
  apply (rule decision_right)
  apply simp
  done