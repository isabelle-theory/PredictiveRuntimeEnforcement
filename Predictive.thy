theory Predictive imports Main begin
  section{*Languages as predicates on lists*}

  text{*In this formalization we use lists of some type variable "'a" to model
    words over "'a"*}

  text{*Syntax for the lattice operations:*}

  notation
    bot ("\<bottom>") and
    top ("\<top>") and
    inf (infixl "\<sqinter>" 70) and
    sup (infixl "\<squnion>" 65)

  text{*We introduce the prefix relation on lists as an instantiation of
    a partial order relation. The fact that $x$ is a prefix of a list $y$
    is denoted by $x \le y$. We prove that the prefix relation is a partial
    order, and we also prove some additional properties*}

  instantiation "list" :: (type) order begin
    primrec less_eq_list where
      "([] \<le> x) = True" |
      "((a # x) \<le> y) = (case y of [] \<Rightarrow> False | b # z \<Rightarrow> a = b \<and> (x \<le> z))"

    definition less_list_def: "((x::'a list) < y) = (x \<le> y \<and> \<not> y \<le> x)"

    lemma [simp]: "(x::'a list) \<le> x"
      by (induction x, simp_all)

    lemma prefix_antisym: "\<And>y . (x::'a list) \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
      apply (induction x)
        apply (case_tac y, simp_all)
        by (case_tac y, simp_all)

    lemma prefix_trans: "\<And>y z . (x::'a list) \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
      apply (induction x, simp_all)
        apply (case_tac y, simp_all)
        by (case_tac z, simp_all, auto)

    lemma [simp]: "(y \<le> []) = (y = [])"
      by (unfold less_eq_list_def, case_tac y, auto)

    lemma [simp]: "[] \<le> ax"
      by (simp add: less_eq_list_def)

    lemma prefix_concat: "\<And> x . x \<le> y = (\<exists> z . y = x @ z)"
      by (induction y, simp_all, case_tac x, auto)

    lemma [simp]: "(butlast x) \<le> x"
      by (induction x, simp_all)

    lemma prefix_butlast: "\<And> y . (x \<le> y) = (x = y \<or> x \<le> (butlast y))"
      proof (induction x)
        case Nil show ?case by simp
        case (Cons x xs)
          assume A: "\<And> y . (xs \<le> y) = (xs = y \<or> xs \<le> (butlast y))"
          show ?case
            apply simp
            apply (case_tac y, simp_all)
            apply safe
            apply simp_all
            apply (subst (asm) A, simp)
            by (subst A, simp)
      qed

    lemma [simp]: "(x @ y \<le> x) = (y = [])"
      by (induction x, simp_all)

    instance proof
      qed (simp_all add: less_list_def prefix_antisym, rule prefix_trans)
  end

  section{*Finite deterministic automata*}

  text{*A finite deterministic automaton is modeled as a record of a transition 
    function $\delta:'s \to 'a \to 's$ and a set $Final : 's set$ of final states, 
    and an initial state $s_0:'s$. The states of the automaton are from the type 
    variable $'s$, and the letters of the alphabet from $'a$.*}

  record ('s, 'a) automaton = 
       \<delta> :: "'s \<Rightarrow> 'a \<Rightarrow> 's"
       Final :: "'s set"
       s\<^sub>0 :: 's

  text{*The language of an automaton $A$ is a predicate on lists of letters, and
   it is defined by primitive recursion:*}

  primrec lang:: "('s, 'a, 'c) automaton_ext \<Rightarrow> 'a list \<Rightarrow> bool" where
    "lang A [] = ((s\<^sub>0 A) \<in> (Final A))" |
    "lang A (a # x) = lang (A\<lparr>s\<^sub>0 := \<delta> A (s\<^sub>0 A) a\<rparr>) x"

  text{*We extend the transition function $\delta$ from letters to lists of letters,
    also by primitive induction*}

  primrec \<delta>e:: "('s, 'a, 'b) automaton_ext \<Rightarrow> 'a list \<Rightarrow> 's" where
    "\<delta>e A [] = s\<^sub>0 A" |
    "\<delta>e A (a # x) = \<delta>e (A\<lparr>s\<^sub>0:=\<delta> A (s\<^sub>0 A) a\<rparr>) x"

  text{*Next two lemma connect the language definition to the extended transition function.*}

  lemma lang_deltae: "\<And> A . lang A x = ((\<delta>e A x) \<in> Final A)"
    by (induction x, simp_all)

  lemma lang_deltaeb: "\<And> y A . lang A (x @ y) = lang (A\<lparr>s\<^sub>0:= (\<delta>e A x)\<rparr>) y"
    by (induction x, simp_all)

  lemma delta_but_last_aux: "\<And> a s . \<delta>e (A\<lparr>s\<^sub>0:=s\<rparr>) (x @ [a]) = \<delta> A (\<delta>e (A\<lparr>s\<^sub>0:=s\<rparr>) x) a"
    apply (induction x)
    by simp_all
    
  lemma delta_but_last: "\<delta>e A (x @ [a]) = \<delta> A (\<delta>e A x) a"
    apply (cut_tac A = A and s = "s\<^sub>0 A" and x = x and a = a in delta_but_last_aux)
    by simp

  text{*We introduce the standard product construction of two automata. Here we construct the
    product corresponding the intersection of the languages of the two automata.*}

  definition product :: "('s, 'a, 'c) automaton_ext \<Rightarrow> ('t, 'a, 'c) automaton_ext 
        \<Rightarrow> ('s \<times> 't, 'a, 'c) automaton_ext" (infix "**" 60) where
    "A ** B = \<lparr> 
        \<delta> = (\<lambda> (s, t) a . (\<delta> A s a, \<delta> B t a)), 
        Final = Final A \<times> Final B, 
        s\<^sub>0 = (s\<^sub>0 A,  s\<^sub>0 B),
        \<dots> = automaton.more A\<rparr>"

  text{*Next five lemmas are straightforward properties of the product of two automata.*}

  lemma [simp]: "s\<^sub>0 (A ** B) = (s\<^sub>0 A, s\<^sub>0 B)"
    by (simp add: product_def)

  lemma [simp]: "Final (A ** B) = (Final A \<times> Final B)"
    by (simp add: product_def)

  lemma [simp]: "(A ** B)\<lparr>s\<^sub>0 := (s, t) \<rparr> = (A\<lparr>s\<^sub>0 := s\<rparr>) ** (B\<lparr>s\<^sub>0 := t\<rparr> )"
    by (simp add: product_def)

  lemma [simp]: "\<delta> (A ** B) (s, t) a = (\<delta> A s a, \<delta> B t a)"
    by (simp add: product_def)

  lemma [simp]: "\<And> A B . \<delta>e (A ** B) x = (\<delta>e A x, \<delta>e B x)"
    by (induction x, simp_all)


  text{*Next two lemmas show that the language of the product is the intersection of the 
    languages of the automata. Second lemma is the point-free version of the first lemma.*}

  lemma intersection_aux: "\<And> A B . lang (A ** B) x =  (lang A x \<and> lang B x)"
    apply (induction x)
    by (auto simp add:  lang_deltae)

  lemma intersection: "lang (A ** B) =  (lang A \<sqinter> lang B)"
    by (simp add: fun_eq_iff intersection_aux)

  text{*Next declaration introduces the complement of an automaton as a instantiation
   of the Isabelle uminus class. We take this approach because we what to use the 
   unary symbol $-$ for the complement. Otherwise this is just a simple definition
   similar to the product.*}

  instantiation automaton_ext :: (type, type, type) uminus begin
    definition complement_def: "- A = A\<lparr>Final := -Final A\<rparr>"
    instance proof qed
  end

  text{*Next five lemmas give some properties of the complement.*}
  lemma [simp]: "\<delta> (-A) = \<delta> A"
    by (simp add: complement_def)

  lemma [simp]: "s\<^sub>0 (-A) = s\<^sub>0 A"
    by (simp add: complement_def)

  lemma complement_init[simp]: "(-A)\<lparr> s\<^sub>0 := s \<rparr> = -(A\<lparr> s\<^sub>0 := s \<rparr>)"
    by (simp add: complement_def)

  lemma [simp]: "\<And> A . \<delta>e (-A) x = \<delta>e A x"
    by (induction x, simp_all)

  lemma [simp]: "Final (-A) = - Final A"
    by (simp add: complement_def)

  text{*The language of the complement of $A$ is the complement of the 
    language of $A$. Next two lemmas express this property in point-wise
    and point-free manner.*}

  lemma complement_aux: "\<And>A . lang (- A) x = (\<not> (lang A x))"
    by (simp add: lang_deltae)

  lemma complement: "lang (-A) = (- (lang A))"
    by (simp add: fun_eq_iff complement_aux)

  text{*Next definition introduces an automaton $Extension\ A$ based on automaton $A$.
    A list $x$ is in the language of $Extension\ A$ if and only if there is a prefix
    of $x$ in the language of $A$. In the paper this automaton is denoted by 
    $B_\varphi$, where $\varphi = lang\ A$.*}

  definition "Extension A = \<lparr>
    \<delta> = (\<lambda> s a . if s \<in> Final A then s else \<delta> A s a),
    Final = Final A,
    s\<^sub>0 = s\<^sub>0 A, 
    \<dots> = more A\<rparr>"

  lemma [simp]: "s\<^sub>0 (Extension A) = s\<^sub>0 A"
    by (simp add: Extension_def)

  text{*We introduce some properties of $Extension\ A$ in the next six lemmas.*}

  lemma Extension_initial[simp]: "Extension A\<lparr>s\<^sub>0 := s\<rparr> = Extension (A\<lparr>s\<^sub>0 := s\<rparr>)"
    by (auto simp add: Extension_def fun_eq_iff)

  lemma prefix_final[simp]: "s \<in> Final A \<Longrightarrow> lang ((Extension A)\<lparr>s\<^sub>0 := s\<rparr>) x"
    by (induction x, simp_all add: Extension_def)

  lemma [simp]: "s\<^sub>0 A \<in> Final A \<Longrightarrow> lang (Extension A) x"
    by (drule prefix_final, simp)

  lemma [simp]: "s \<in> Final A \<Longrightarrow> \<delta> (Extension A) s a = s"
    by (simp add: Extension_def)

  lemma [simp]: "s \<notin> Final A \<Longrightarrow> \<delta> (Extension A) s a = \<delta> A s a"
    by (simp add: Extension_def)

  lemma "lang ((Extension A)\<lparr>s\<^sub>0 := s\<rparr>) = \<top> \<Longrightarrow> s \<in> Final A"
    apply (simp add: fun_eq_iff Extension_def image_def)
    by (drule_tac x = "[]" in spec, simp)

  text{*The language of $Extension\ A$ in terms of the language of $A$ is given by
    the next lemma.*}

  lemma Extension_lang: "\<And> (A::('s, 'a, 'c) automaton_ext) . lang (Extension A) x = (\<exists> y . lang A y \<and> y \<le> x)"
    proof (induction x)
    case (Nil) show ?case
      by (simp add: Extension_def image_def)
    next
    case (Cons a x)
      assume A: "\<And> (A::('s, 'a, 'c) automaton_ext) .  lang (Extension A) x = (\<exists>y. lang A y \<and> y \<le> x)"
      from A have B: "\<And> (A::('s, 'a, 'c) automaton_ext) y . lang A y \<Longrightarrow> y \<le> x \<Longrightarrow> lang (Extension A) x"
        by blast 
      show ?case
        apply simp
        apply safe
          apply (case_tac "s\<^sub>0 A \<in>  Final A", simp_all)
          apply (rule_tac x = "[]" in exI, simp)
          apply (simp add: A, safe)
          apply (rule_tac x = "a # y" in exI)
        
          apply simp
          apply (case_tac y, simp_all, safe)
          apply (case_tac "s\<^sub>0 A \<in>  Final A", simp_all)
          by (drule B, simp_all)
    qed

  section{*Constraints of the Predictive Enforcement*}

  text{*Next definition introduces $k_{\psi,\varphi}$ function from the paper 
    \cite{predictive}. The automata $A_\psi$ and $A_\varphi$ correspond to the properties 
    $\psi$ and $\varphi$, respectively.*}

  definition "kfunc A\<^sub>\<psi> A\<^sub>\<phi> x = (\<forall> y . lang A\<^sub>\<psi> (x @ y) \<longrightarrow> (\<exists> z .(lang A\<^sub>\<phi> (x @ z)) \<and> z \<le> y))"

  text{*The Urgency constraint is introduced in the next definition, and it has as hypothesis
    the $kfunc$ function. For simplicity we introduce first $kfunc$ and then Urgency. In the
    paper Urgency precedes the definition of $kfunc$.*}

  definition "Urgency A\<^sub>\<psi> A\<^sub>\<phi> Enf = (\<forall> x . kfunc A\<^sub>\<psi> A\<^sub>\<phi> x \<longrightarrow> Enf x = x)"

  definition "Soundness A\<^sub>\<psi> A\<^sub>\<phi> Enf = (\<forall> x . lang A\<^sub>\<psi> x \<and> Enf x \<noteq> [] \<longrightarrow> lang A\<^sub>\<phi> (Enf x))"

  definition "Transparency1 Enf = (\<forall> x . Enf x \<le> x)"

  definition "Transparency2 A\<^sub>\<phi> Enf = (\<forall> x . lang A\<^sub>\<phi> x \<longrightarrow> Enf x = x)"

  definition [simp]: "Monotonicity Enf = mono Enf"

  text{*Next lemma shows that Transparency2 is a consequence of Urgency*}

  lemma "Urgency A\<^sub>\<psi> A\<^sub>\<phi> Enf \<Longrightarrow> Transparency2 A\<^sub>\<phi> Enf"
    by (metis Transparency2_def Urgency_def append_Nil2 kfunc_def less_eq_list.simps(1))

  section{*Independence of Urgency, Transparency1, Monotonicity and Soundness*}

  lemma Urgency_true [simp]: "lang A\<^sub>\<psi> = \<top> \<Longrightarrow> lang  A\<^sub>\<phi> = \<bottom> \<Longrightarrow> Urgency A\<^sub>\<psi> A\<^sub>\<phi> Enf"
    by (simp add: Urgency_def kfunc_def)

  lemma Urgency_phi[simp]: "lang A\<^sub>\<psi> = \<top> \<Longrightarrow> lang A\<^sub>\<phi> = B \<Longrightarrow> Urgency A\<^sub>\<psi> A\<^sub>\<phi> Enf = (\<forall> x . B x \<longrightarrow> Enf x = x)"
    apply (simp add: kfunc_def Urgency_def, auto)
    apply (drule_tac x = x in spec, safe)
    apply (rule_tac x = "[]" in exI, simp)
    apply (drule_tac x = x in spec)
    by (drule_tac x = "[]" in spec, simp)

  lemma Urgency_id [simp]: "lang A\<^sub>\<psi> = \<top> \<Longrightarrow> lang  A\<^sub>\<phi> = \<top> \<Longrightarrow> (Urgency A\<^sub>\<psi> A\<^sub>\<phi> Enf) = (Enf = id)"
    by (simp add: Urgency_def kfunc_def fun_eq_iff, auto)

  lemma Indep1: "lang A\<^sub>\<psi> = \<top> \<Longrightarrow> lang A\<^sub>\<phi> = \<bottom> \<Longrightarrow> (\<forall> x . Enf x = x) \<Longrightarrow> 
     Urgency A\<^sub>\<psi> A\<^sub>\<phi> Enf \<and> Monotonicity Enf \<and> Transparency1 Enf \<and> \<not> Soundness  A\<^sub>\<psi> A\<^sub>\<phi> Enf"
     by (simp add: Soundness_def mono_def Transparency1_def, auto)

  lemma Indep1a: "lang A\<^sub>\<psi> = \<top> \<Longrightarrow> lang A\<^sub>\<phi> = (\<lambda> x . x = [()]) \<Longrightarrow> (\<forall> x . Enf x = x) \<Longrightarrow> 
     Urgency A\<^sub>\<psi> A\<^sub>\<phi> Enf \<and> Monotonicity Enf \<and> Transparency1 Enf \<and> \<not> Soundness  A\<^sub>\<psi> A\<^sub>\<phi> Enf"
     by (simp add: Soundness_def mono_def Transparency1_def, auto)

  lemma Indep2: "lang A\<^sub>\<psi> = \<top> \<Longrightarrow> lang  A\<^sub>\<phi> = (\<lambda> x . x = [()]) \<Longrightarrow> (\<forall> x . Enf x = [()]) \<Longrightarrow> 
     Urgency A\<^sub>\<psi> A\<^sub>\<phi> Enf \<and> Monotonicity Enf \<and> \<not> Transparency1 Enf \<and> Soundness  A\<^sub>\<psi> A\<^sub>\<phi> Enf"
     apply (simp add: Soundness_def mono_def Transparency1_def)
     by (rule_tac x = "[]" in exI, simp)

  lemma Indep3: "lang A\<^sub>\<psi> = \<top> \<Longrightarrow> lang  A\<^sub>\<phi> = (\<lambda> x . x = [()]) \<Longrightarrow> (\<forall> x . Enf x = (if x = [()] then [()] else [])) \<Longrightarrow> 
     Urgency A\<^sub>\<psi> A\<^sub>\<phi> Enf \<and> \<not> Monotonicity Enf \<and> Transparency1 Enf \<and> Soundness  A\<^sub>\<psi> A\<^sub>\<phi> Enf"
     apply (simp add: Soundness_def mono_def Transparency1_def)
     by (rule_tac x = "[(),()]" in exI, simp)

  lemma Indep4: "lang A\<^sub>\<psi> = \<top> \<Longrightarrow> lang  A\<^sub>\<phi> = \<top> \<Longrightarrow> (\<forall> x . Enf x = []) \<Longrightarrow> 
     \<not> Urgency A\<^sub>\<psi> A\<^sub>\<phi> Enf \<and> Monotonicity Enf \<and> Transparency1 Enf \<and> Soundness  A\<^sub>\<psi> A\<^sub>\<phi> Enf"
     apply (simp add: Soundness_def mono_def Transparency1_def)
     by (rule_tac x = "[Eps \<top>]" in exI, simp)

  section{*Alternative Urgency*}

  text{*A weaker version of Urgency is introduced by:*}
  definition "Urgency' A\<^sub>\<psi> A\<^sub>\<phi> Enf = (\<forall> x . (\<forall> y . lang A\<^sub>\<psi> (x @ y) \<longrightarrow> lang A\<^sub>\<phi> x) \<longrightarrow> Enf x = x)"

  lemma Urgency_Urgency'_aux: "(\<forall> y . lang A\<^sub>\<psi> (x @ y) \<longrightarrow> lang A\<^sub>\<phi> x) \<Longrightarrow> kfunc A\<^sub>\<psi> A\<^sub>\<phi> x"
    by (metis kfunc_def append_Nil2 less_eq_list.simps(1))

  text{*Urgency is stronger than Urgency'*}

  lemma Urgency_Urgency': "Urgency A\<^sub>\<psi> A\<^sub>\<phi> Enf \<Longrightarrow> Urgency'  A\<^sub>\<psi> A\<^sub>\<phi> Enf"
    by (metis Urgency'_def Urgency_def kfunc_def append_Nil2 less_eq_list.simps(1))

  section{*Implementation of $kfunc$ as the inclusion of two regular languages*}

  text{*Next definition is a more abstract variant of $kfunc$ as an inclusion of regular
    languages. Here we do not have the existential quantifier.*}
  definition "kfunc_lang A\<^sub>\<psi> A\<^sub>\<phi> x = (lang (A\<^sub>\<psi>\<lparr>s\<^sub>0 := (\<delta>e A\<^sub>\<psi> x)\<rparr>) \<le> lang ((Extension A\<^sub>\<phi>)\<lparr> s\<^sub>0 := \<delta>e A\<^sub>\<phi> x \<rparr>))"

  lemma kfunc_kfunc_lang: "kfunc A\<^sub>\<psi> A\<^sub>\<phi> x = kfunc_lang A\<^sub>\<psi> A\<^sub>\<phi> x"
    by (simp add: kfunc_def kfunc_lang_def lang_deltaeb Predictive.Extension_lang le_fun_def) 

  lemma kfunc_lang_empty: " kfunc_lang A\<^sub>\<psi> A\<^sub>\<phi> x = (lang ((A\<^sub>\<psi> ** - (Extension A\<^sub>\<phi>))\<lparr>s\<^sub>0 := (\<delta>e A\<^sub>\<psi> x, \<delta>e A\<^sub>\<phi> x)\<rparr>) = \<bottom>)"
    by (simp add: intersection Predictive.complement kfunc_lang_def fun_eq_iff le_fun_def)


  text{*Next theorem shows the implementation of $kfunc$ as a test of emptiness of a regular language
    (Theorem 2 in \cite{predictive}).*}

  theorem kfunc_empty: "kfunc A\<^sub>\<psi> A\<^sub>\<phi> x = (lang ((A\<^sub>\<psi> ** - (Extension A\<^sub>\<phi>))\<lparr>s\<^sub>0 := (\<delta>e A\<^sub>\<psi> x, \<delta>e A\<^sub>\<phi> x)\<rparr>) = \<bottom>)"
    by (unfold kfunc_kfunc_lang kfunc_lang_empty, simp)

  section{*Enforcement Function*}

  text{*Next definition introduces the enforcement function. In this formalization we chose
    to define $enforce$ directly while in \cite{predictive} we define it using another function
    called $store$ that returns two sequences. The $enforce$ function is the first component
    of $store$.*}

  fun enforce :: "('s, 'a, 'c) automaton_ext \<Rightarrow> ('t, 'a, 'c) automaton_ext \<Rightarrow> 'a list \<Rightarrow> 'a list" where
    "enforce A\<^sub>\<psi> A\<^sub>\<phi> x = 
      (if x = [] then 
        [] 
      else 
        (if kfunc A\<^sub>\<psi> A\<^sub>\<phi> x then 
          x 
        else 
          enforce A\<^sub>\<psi> A\<^sub>\<phi> (butlast x)))"

(*
  definition  enforce_nat :: "(nat, nat, nat) automaton_ext \<Rightarrow> (nat, nat, nat) automaton_ext \<Rightarrow> nat list \<Rightarrow> nat list" where
    "enforce_nat = enforce"

  export_code enforce_nat in SML
    module_name Example file "example.ML"

  export_code enforce_nat in Scala
    module_name Example file "example.scala"

  export_code enforce_nat in OCaml
    module_name Example file "example.ocaml"
*)

  text{*When the property $\psi$ is true for all sequences, then the Urgency property
    is simplified to the non-predictive case.*}

  lemma no_prediction: "lang A\<^sub>\<psi> = \<top> \<Longrightarrow> Urgency A\<^sub>\<psi> A\<^sub>\<phi> Enf = (\<forall>x. lang A\<^sub>\<phi> x \<longrightarrow> Enf x = x)"
    apply (auto simp add: Urgency_def kfunc_def)
    apply (metis append_Nil2 less_eq_list.simps(1))
    by (metis list.simps(4) neq_Nil_conv less_eq_list.simps(2) self_append_conv)

  text{*When the property $\psi$ is included in $\varphi$, then output of the
    enforcer is always equal to the input.*}

  lemma subset_enforce: "lang A\<^sub>\<psi> \<le> lang A\<^sub>\<phi> \<Longrightarrow> enforce A\<^sub>\<psi> A\<^sub>\<phi> x = x"
    by (metis enforce.simps kfunc_def order_refl predicate1D)

  text{*When the property $\psi$ is true for all sequences, then the kfun
    is simplified to:*}

  lemma no_prediction_kfunc: "lang A\<^sub>\<psi> = \<top> \<Longrightarrow> kfunc A\<^sub>\<psi> A\<^sub>\<phi> x = lang A\<^sub>\<phi> x"
    apply (auto simp add: kfunc_def)
    using less_eq_list.simps(1) prefix_antisym apply fastforce
    by (metis append_Nil2 less_eq_list.simps(1))

  text{*Next three lemmas are used in the proofs of soundness,  transparency, and urgency.*}

  lemma kfunc_enforce: "enforce A\<^sub>\<psi> A\<^sub>\<phi> x \<noteq> [] \<Longrightarrow> kfunc A\<^sub>\<psi> A\<^sub>\<phi> (enforce A\<^sub>\<psi> A\<^sub>\<phi> x)"
    proof (induction x rule: length_induct)
      fix xs::"'a list"
      assume "\<forall>ys. length ys < length xs \<longrightarrow> enforce A\<^sub>\<psi> A\<^sub>\<phi> ys \<noteq> [] \<longrightarrow> kfunc A\<^sub>\<psi> A\<^sub>\<phi> (enforce A\<^sub>\<psi> A\<^sub>\<phi> ys)"
      from this have A: "\<And> ys . length ys < length xs \<Longrightarrow> enforce A\<^sub>\<psi> A\<^sub>\<phi> ys \<noteq> [] \<Longrightarrow> kfunc A\<^sub>\<psi> A\<^sub>\<phi> (enforce A\<^sub>\<psi> A\<^sub>\<phi> ys)"
        by simp
      assume C: "enforce A\<^sub>\<psi> A\<^sub>\<phi> xs \<noteq> []"
      from this have B: "xs \<noteq> []"
        by (case_tac xs, simp_all)
      from B and C have  D: "\<not> kfunc A\<^sub>\<psi> A\<^sub>\<phi> xs \<Longrightarrow> enforce A\<^sub>\<psi> A\<^sub>\<phi> (butlast xs) \<noteq> []"
        apply (subst enforce.simps)
        apply (subst (asm) enforce.simps)
        apply (subst (asm) enforce.simps)
        by (simp del: enforce.simps)
      from B and D show "kfunc A\<^sub>\<psi> A\<^sub>\<phi> (enforce A\<^sub>\<psi> A\<^sub>\<phi> xs)"
        apply (subst enforce.simps)
        apply (simp del: enforce.simps, safe)
        by (cut_tac ys = "butlast xs" in A, simp_all del: enforce.simps)
    qed
        
  lemma kfunc_prefix_enforce: "kfunc A\<^sub>\<psi> A\<^sub>\<phi> y \<Longrightarrow> y \<le> x \<Longrightarrow> y \<le> (enforce A\<^sub>\<psi> A\<^sub>\<phi> x)"
    apply (induction x rule: length_induct)
    apply (subst enforce.simps)
    apply (case_tac "xs = []")
    apply simp
    apply (simp del: enforce.simps, safe)
    apply (drule_tac x = "butlast xs" in spec, safe)
    apply (simp_all del: enforce.simps)
    by (subst (asm) prefix_butlast, simp)

  lemma lang_enf_kfunc: "lang A\<^sub>\<phi> x \<Longrightarrow> kfunc A\<^sub>\<psi> A\<^sub>\<phi> x"
    apply (simp add: kfunc_def, safe)
    by (rule_tac x= "[]" in exI, simp)

  text{*Finally we prove the enforcement function satisfies 
    soundness,  transparency, monotonicity, and urgency properties.*}

  theorem Transparency1: "enforce A\<^sub>\<psi> A\<^sub>\<phi> x \<le> x"
    apply (induction x rule: length_induct)
    apply (subst enforce.simps)
    apply (case_tac "xs = []")
    apply (unfold if_P)
    apply simp
    apply (unfold if_not_P)
    apply (case_tac "kfunc A\<^sub>\<psi> A\<^sub>\<phi> xs")
    apply simp
    apply (unfold if_not_P)
    apply (drule_tac x = "butlast xs" in spec)
    apply safe
    apply simp
    by (rule_tac y = "butlast xs" in prefix_trans, simp_all)

  lemma Monotonicity_aux: "\<And> x y . x \<le> y \<Longrightarrow> n = length y \<Longrightarrow> enforce A\<^sub>\<psi> A\<^sub>\<phi> x \<le> enforce A\<^sub>\<psi> A\<^sub>\<phi> y"
    apply (induction n)
    apply simp
    apply (subst enforce.simps)
    apply (subst (2) enforce.simps)
    apply (simp del: enforce.simps, safe)
    apply (case_tac x, simp_all del: enforce.simps)
    apply (metis kfunc_prefix_enforce prefix_butlast)
    apply (metis Transparency1 enforce.simps prefix_trans)
    by (metis Suc_eq_plus1 add.commute add_diff_cancel_left' enforce.simps length_butlast prefix_butlast)
    
  theorem Monotonicity: "Monotonicity (enforce A\<^sub>\<psi> A\<^sub>\<phi>)"
    apply (simp)
    apply (unfold mono_def)
    apply safe
    by (rule Monotonicity_aux, simp_all)

  theorem Urgency: "kfunc A\<^sub>\<psi> A\<^sub>\<phi> x \<Longrightarrow> enforce A\<^sub>\<psi> A\<^sub>\<phi> x = x"
    by simp

  theorem Soundness: "lang A\<^sub>\<psi> x \<Longrightarrow> enforce A\<^sub>\<psi> A\<^sub>\<phi> x \<noteq> [] \<Longrightarrow> lang A\<^sub>\<phi> (enforce A\<^sub>\<psi> A\<^sub>\<phi> x)"
    proof -
      assume A: "lang A\<^sub>\<psi> x"
      assume B: "enforce A\<^sub>\<psi> A\<^sub>\<phi> x \<noteq> []"
      have "enforce A\<^sub>\<psi> A\<^sub>\<phi> x \<le> x" by (rule Transparency1)
      from this obtain z where D: "x = enforce A\<^sub>\<psi> A\<^sub>\<phi> x @ z" by (simp add: prefix_concat del: enforce.simps, safe, simp)
      from A and this have [simp]: "lang A\<^sub>\<psi> ( enforce A\<^sub>\<psi> A\<^sub>\<phi> x @ z)" by simp
      from B have "kfunc A\<^sub>\<psi> A\<^sub>\<phi> (enforce A\<^sub>\<psi> A\<^sub>\<phi> x)" by (rule kfunc_enforce)
      from this have C: "\<And> y . lang A\<^sub>\<psi> (enforce A\<^sub>\<psi> A\<^sub>\<phi> x @ y) \<Longrightarrow> (\<exists>t . lang A\<^sub>\<phi> (enforce A\<^sub>\<psi> A\<^sub>\<phi> x @ t) \<and> t \<le> y)" by (simp add: kfunc_def)
      have "(\<exists>t . lang  A\<^sub>\<phi>  (enforce A\<^sub>\<psi> A\<^sub>\<phi> x @ t) \<and> (t \<le> z))" by (rule C, simp del: enforce.simps)
      then obtain za where F: "lang A\<^sub>\<phi> (enforce A\<^sub>\<psi> A\<^sub>\<phi> x @ za)" and E: "za \<le> z" by blast
      from this have "kfunc A\<^sub>\<psi> A\<^sub>\<phi> (enforce A\<^sub>\<psi> A\<^sub>\<phi> x @ za)" by (simp add: lang_enf_kfunc del: enforce.simps)
      from this have "enforce A\<^sub>\<psi> A\<^sub>\<phi> x @ za \<le> enforce A\<^sub>\<psi> A\<^sub>\<phi> x" 
        apply (rule kfunc_prefix_enforce)
        by (cut_tac D E, simp add: prefix_concat del: enforce.simps, blast)
      from this have [simp]: "za = []" by simp
      from F show ?thesis by (simp del: enforce.simps)
    qed

  section{*Enforcement Algorithm*}

  text{*Because the enforcement algorithm has a non-terminating loop we cannot represent it as function
  in Isabelle. We introduce here the invariant of the algorithm, and we prove the initialization
  establishes the invariant, and that each step of the algorithm preserves the invariant. The
  invariant expresses the desired properties of the algorithm*}

  text{*$x$ is the input received so far, $y$ is the concatenation of all released words, and 
  $z$ ($\sigma_c$ in the paper) is the pending word.*}

  definition "Invariant A\<^sub>\<psi> A\<^sub>\<phi> C p q x y z = (
    C = A\<^sub>\<psi> ** - (Extension A\<^sub>\<phi>) 
    \<and> p = \<delta>e A\<^sub>\<psi> x 
    \<and> q =  \<delta>e A\<^sub>\<phi> x \<and> x = y @ z 
    \<and> enforce A\<^sub>\<psi> A\<^sub>\<phi> x = y)"

  definition "Init A\<^sub>\<psi> A\<^sub>\<phi> = (let (z, p, q, C) = ([], s\<^sub>0 A\<^sub>\<psi>, s\<^sub>0 A\<^sub>\<phi>, A\<^sub>\<psi> ** - (Extension A\<^sub>\<phi>)) in (z, p, q, C))"
  
  definition "Step A\<^sub>\<psi> A\<^sub>\<phi> C p q z a = (let (p',q') = (\<delta> A\<^sub>\<psi> p a, \<delta> A\<^sub>\<phi> q a) in (p', q', if lang (C\<lparr>s\<^sub>0 := (p',q')\<rparr>) = \<bottom> then (z @ [a], []) else ([], z @ [a])))"

  text{*The initialization establishes the invariant*}

  lemma Init: "(z, p, q, C) = Init A\<^sub>\<psi> A\<^sub>\<phi> \<Longrightarrow> Invariant A\<^sub>\<psi> A\<^sub>\<phi> C p q [] [] z"
    by (simp add: Init_def Invariant_def) 

  text{*The step preserves the invariant*}

  lemma Step: "(p', q', yr, zo) = Step A\<^sub>\<psi> A\<^sub>\<phi> C p q z a \<Longrightarrow> Invariant A\<^sub>\<psi> A\<^sub>\<phi> C p q x y z \<Longrightarrow> Invariant A\<^sub>\<psi> A\<^sub>\<phi> C p' q' (x @ [a]) (y @ yr) zo"
    apply (simp add: Step_def)
    apply (unfold Invariant_def)
    apply (simp del: enforce.simps)
    apply (cut_tac A\<^sub>\<psi>1 = A\<^sub>\<psi> and A\<^sub>\<phi>1 = A\<^sub>\<phi> and x1 = "x @ [a]" in  kfunc_lang_empty [THEN sym])
    apply (simp del: enforce.simps add:  delta_but_last)
    apply (unfold append_assoc [THEN sym])
    apply (simp del: enforce.simps append_assoc add:  delta_but_last)
    apply (unfold kfunc_kfunc_lang [THEN sym])
    apply (case_tac  "kfunc A\<^sub>\<psi> A\<^sub>\<phi> ((y @ z) @ [a])")
    apply (simp_all del: enforce.simps)
    apply (rule Urgency, simp)
    by (metis (no_types, lifting) append_assoc enforce.simps snoc_eq_iff_butlast)


  section{*Example*}

  datatype Sa = "l0" | "l1" | "l2"
  datatype Sig = "a" | "b" | "c"
  datatype Sb = "k0" | "k1" | "k2" | "k3"

  fun
    \<delta>a :: "Sa \<Rightarrow> Sig \<Rightarrow> Sa"
  where
    "\<delta>a l0 a = l0" |
    "\<delta>a l0 b = l1" |
    "\<delta>a l1 c = l0" |
    "\<delta>a _  a = l2" |
    "\<delta>a _  b = l2" |
    "\<delta>a _  c = l2" 

  definition "Fa = {l0}"

  fun
    \<delta>b :: "Sb \<Rightarrow> Sig \<Rightarrow> Sb"
  where
    "\<delta>b k0 a = k0" |
    "\<delta>b k0 b = k1" |
    "\<delta>b k1 a = k0" |
    "\<delta>b k1 c = k2" |
    "\<delta>b k2 a = k0" |
    "\<delta>b _  a = k3" |
    "\<delta>b _  b = k3" |
    "\<delta>b _  c = k3" 

  definition "Fb = {k0, k1, k2}"

  lemma "kfunc_lang \<lparr>\<delta> = \<delta>b, Final = Fb, s\<^sub>0 = k0\<rparr> \<lparr>\<delta> = \<delta>a, Final = Fa, s\<^sub>0 = l0\<rparr> [a,b] = False"
    apply (simp add: kfunc_lang_def le_fun_def)
    apply (rule_tac x = "[]" in exI)
    by (simp add: Fb_def Extension_def Fa_def )

  lemma "kfunc \<lparr>\<delta> = \<delta>b, Final = Fb, s\<^sub>0 = k0\<rparr> \<lparr>\<delta> = \<delta>a, Final = Fa, s\<^sub>0 = l0\<rparr> [a]"
    apply (simp add: kfunc_def Fb_def Fa_def, auto)
    by (rule_tac x = "[]" in exI, simp)
end
