theory Predictive imports Main begin
  section{*Main results*}
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
      apply (induction y, simp_all)
      by (case_tac x, auto)

    lemma [simp]: "(butlast x) \<le> x"
      by (induction x, simp_all)

    lemma prefix_butlast: "\<And> y . (x \<le> y) = (x = y \<or> x \<le> (butlast y))"
      proof (induction x)
        case Nil show ?case by simp
        case (Cons x xs)
          assume A: "\<And> y . (xs \<le> y) = (xs = y \<or> xs \<le> (butlast y))"
          show ?case
            apply simp
            apply (case_tac y, simp)
            apply simp
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

  text{*A finite deterministic automaton is modeled as a record of a transition 
    function $\delta:'s \to 'a \to 's$ and a set $Final : 's set$ of final states, 
    and an initial state $s_0:'s$. The states of the automaton are from the type 
    variable $'s$, and the letters of the alphabet from $'a$.*}

  record ('s, 'a) automaton = 
       \<delta> :: "'s \<Rightarrow> 'a \<Rightarrow> 's"
       Final :: "'s set"
       s\<^sub>0 :: 's

  text{*The language of an automatoon $A$ is a predicate on lists of letters, and
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

  text{*Next definition introduces an automaton $Prefix\ A$ based on automaton $A$.
    A list $x$ is in the language of $Prefix\ A$ if and only if there is a prefix
    of $x$ in the language of $A$. In the paper this automaton is denoted by 
    $B_\varphi$, where $\varphi = lang\ A$.*}

  definition "Prefix A = \<lparr>
    \<delta> = (\<lambda> u a . (case u of None \<Rightarrow> None | Some s \<Rightarrow> if s \<in> Final A then None else Some (\<delta> A s a))),
    Final = Some ` (Final A) \<union> {None},
    s\<^sub>0 = Some (s\<^sub>0 A), 
    \<dots> = more A\<rparr>"

  lemma [simp]: "s\<^sub>0 (Prefix A) = Some (s\<^sub>0 A)"
    by (simp add: Prefix_def)

  text{*We introduce some properties of $Prefix\ A$ in the next six lemmas.*}

  lemma Prefix_initial[simp]: "Prefix A\<lparr>s\<^sub>0 := Some s\<rparr> = Prefix (A\<lparr>s\<^sub>0 := s\<rparr>)"
    apply (auto simp add: Prefix_def fun_eq_iff)
    by (case_tac x, simp_all)

  lemma [simp]: "lang ((Prefix A)\<lparr>s\<^sub>0 := None\<rparr>) x"
    by (induction x, simp_all add: Prefix_def)

  lemma [simp]: "s \<in> Final A \<Longrightarrow> \<delta> (Prefix A) (Some s) a = None"
    by (simp add: Prefix_def)

  lemma [simp]: "s \<notin> Final A \<Longrightarrow> \<delta> (Prefix A) (Some s) a = Some (\<delta> A s a)"
    by (simp add: Prefix_def)

  lemma [simp]: "s \<in> Final A \<Longrightarrow> lang ((Prefix A)\<lparr> s\<^sub>0 := Some s\<rparr>) x"
    by (case_tac x, simp_all, simp add: Prefix_def)

  lemma "lang ((Prefix A)\<lparr>s\<^sub>0 := Some s\<rparr>) = \<top> \<Longrightarrow> s \<in> Final A"
    apply (simp add: fun_eq_iff Prefix_def image_def)
    by (drule_tac x = "[]" in spec, simp)

  text{*The language of $Prefix\ A$ in terms of the language of $A$ is given by
    the next lemma. This is Lemma 5 from the paper \cite{predictive}.*}

  lemma Prefix_lang: "\<And> (A::('s, 'a, 'c) automaton_ext) . lang (Prefix A) x = (\<exists> y . lang A y \<and> y \<le> x)"
    proof (induction x)
    case (Nil) show ?case
      by (simp add: Prefix_def image_def)
    next
    case (Cons a x)
      assume A: "\<And> (A::('s, 'a, 'c) automaton_ext) .  lang (Prefix A) x = (\<exists>y. lang A y \<and> y \<le> x)"
      from A have B: "\<And> (A::('s, 'a, 'c) automaton_ext) y . lang A y \<Longrightarrow> y \<le> x \<Longrightarrow> lang (Prefix A) x"
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

  text{*Next definition introduces $k_{\psi,\varphi}$ function from Definition 2 in the paper 
    \cite{predictive}. The automata $A_\psi$ and $A_\varphi$ correspond to the properties 
    $\psi$ and $\varphi$, respectively.*}

  definition "kfunc A\<^sub>\<psi> A\<^sub>\<phi> x = (\<forall> y . lang A\<^sub>\<psi> (x @ y) \<longrightarrow> (\<exists> z .(lang A\<^sub>\<phi> (x @ z)) \<and> z \<le> y))"

  text{*The Urgency constraint is introduced in the next definition, and it has as hypothesis
    the $kfunc$ function.*}
  definition "Urgency A\<^sub>\<psi> A\<^sub>\<phi> Enf = (\<forall> x . kfunc A\<^sub>\<psi> A\<^sub>\<phi> x \<longrightarrow> Enf x = x)"

  text{*The weaker version of Urgency is introduced by:*}
  definition "Urgency' A\<^sub>\<psi> A\<^sub>\<phi> Enf = (\<forall> x . (\<forall> y . lang A\<^sub>\<psi> (x @ y) \<longrightarrow> lang A\<^sub>\<phi> x) \<longrightarrow> Enf x = x)"

  lemma Urgency_Urgency'_aux: "(\<forall> y . lang A\<^sub>\<psi> (x @ y) \<longrightarrow> lang A\<^sub>\<phi> x) \<Longrightarrow> kfunc A\<^sub>\<psi> A\<^sub>\<phi> x"
    by (metis kfunc_def append_Nil2 less_eq_list.simps(1))

  text{*Urgency is stronger than Urgency' (Lemma 2 in \cite{predictive}):*}

  lemma Urgency_Urgency': "Urgency A\<^sub>\<psi> A\<^sub>\<phi> Enf \<Longrightarrow> Urgency'  A\<^sub>\<psi> A\<^sub>\<phi> Enf"
    by (simp add: Urgency'_def Urgency_def Urgency_Urgency'_aux)

  text{*When the property $\psi$ is true for all sequences, then the Urgency property
    is simplified to the non-predictive case (Lemma 3 in \cite{predictive}).*}
  lemma no_prediction: "lang A\<^sub>\<psi> = \<top> \<Longrightarrow> Urgency A\<^sub>\<psi> A\<^sub>\<phi> Enf = (\<forall>x. lang A\<^sub>\<phi> x \<longrightarrow> Enf x = x)"
    apply (auto simp add: Urgency_def kfunc_def)
    apply (metis append_Nil2 less_eq_list.simps(1))
    by (metis list.simps(4) neq_Nil_conv less_eq_list.simps(2) self_append_conv)

  text{*Next definition is a more abstract variant of $kfunc$ as an inclusion of regular
    languages. Here we do not have the existential quantifier.*}
  definition "kfunc_lang A\<^sub>\<psi> A\<^sub>\<phi> x = (lang (A\<^sub>\<psi>\<lparr>s\<^sub>0 := (\<delta>e A\<^sub>\<psi> x)\<rparr>) \<le> lang ((Prefix A\<^sub>\<phi>)\<lparr> s\<^sub>0 := Some (\<delta>e A\<^sub>\<phi> x) \<rparr>))"

  lemma kfunc_kfunc_lang: "kfunc A\<^sub>\<psi> A\<^sub>\<phi> x = kfunc_lang A\<^sub>\<psi> A\<^sub>\<phi> x"
    by (simp add: kfunc_def kfunc_lang_def lang_deltaeb Predictive.Prefix_lang le_fun_def)

  lemma kfunc_lang_empty: " kfunc_lang A\<^sub>\<psi> A\<^sub>\<phi> x = (lang ((A\<^sub>\<psi> ** - (Prefix A\<^sub>\<phi>))\<lparr>s\<^sub>0 := (\<delta>e A\<^sub>\<psi> x, Some (\<delta>e A\<^sub>\<phi> x))\<rparr>) = \<bottom>)"
    by (simp add: intersection Predictive.complement kfunc_lang_def fun_eq_iff le_fun_def)

  text{*Next theorem shows the implementation of $kfunc$ as a test of emptiness of a regular language
    (Theorem 2 in \cite{predictive}).*}
  theorem kfunc_empty: "kfunc A\<^sub>\<psi> A\<^sub>\<phi> x = (lang ((A\<^sub>\<psi> ** - (Prefix A\<^sub>\<phi>))\<lparr>s\<^sub>0 := (\<delta>e A\<^sub>\<psi> x, Some (\<delta>e A\<^sub>\<phi> x))\<rparr>) = \<bottom>)"
    by (unfold kfunc_kfunc_lang kfunc_lang_empty, simp)

  text{*Next definition introduces the enforcement function. In this formalization we chose
    to define $enforce$ directly while in \cite{predictive} is defined using another function
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

  text{*Next three lemmas are used in the proofs of soundness,  transparency, and urgency.
    These lemmas correspond to Lemma 4 from \cite{predictive}.*} 

  (*lemma 4.1*)
  lemma kfunc_enforce: "enforce A\<^sub>\<psi> A\<^sub>\<phi> x \<noteq> [] \<Longrightarrow> kfunc A\<^sub>\<psi> A\<^sub>\<phi> (enforce A\<^sub>\<psi> A\<^sub>\<phi> x)"
    apply (induction x rule: length_induct)
    apply (subst enforce.simps)
    apply (case_tac "xs = []")
    apply simp
    apply (simp del: enforce.simps, safe)
    apply (drule_tac x = "butlast xs" in spec, safe)
    apply (simp_all del: enforce.simps)
    by simp

  (*lemma 4.2*)
  lemma kfunc_prefix_enforce: "kfunc A\<^sub>\<psi> A\<^sub>\<phi> y \<Longrightarrow> y \<le> x \<Longrightarrow> y \<le> (enforce A\<^sub>\<psi> A\<^sub>\<phi> x)"
    apply (induction x rule: length_induct)
    apply (subst enforce.simps)
    apply (case_tac "xs = []")
    apply simp
    apply (simp del: enforce.simps, safe)
    apply (drule_tac x = "butlast xs" in spec, safe)
    apply (simp_all del: enforce.simps)
    by (subst (asm) prefix_butlast, simp)

  (*lemma 4.3*)
  lemma lang_enf_kfunc: "lang A\<^sub>\<phi> x \<Longrightarrow> kfunc A\<^sub>\<psi> A\<^sub>\<phi> x"
    apply (simp add: kfunc_def, safe)
    by (rule_tac x= "[]" in exI, simp)

  text{*Finally we prove the enforcement function satisfies 
    soundness,  transparency, and urgency properties.*}

  theorem Transparency1: " enforce A\<^sub>\<psi> A\<^sub>\<phi> x \<le> x"
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

  theorem Transparency2: "lang A\<^sub>\<phi> x \<Longrightarrow> enforce A\<^sub>\<psi> A\<^sub>\<phi> x = x"
    by (simp add: lang_enf_kfunc)

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
      from this have "enforce A\<^sub>\<psi> A\<^sub>\<phi> x @ za \<le> enforce A\<^sub>\<psi> A\<^sub>\<phi> x" apply (rule kfunc_prefix_enforce)
        by (cut_tac D E, simp add: prefix_concat del: enforce.simps, blast)
      from this have [simp]: "za = []" by simp
      from F show ?thesis by (simp del: enforce.simps)
    qed

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
    by (simp add: Fb_def Prefix_def Fa_def )

  lemma "kfunc \<lparr>\<delta> = \<delta>b, Final = Fb, s\<^sub>0 = k0\<rparr> \<lparr>\<delta> = \<delta>a, Final = Fa, s\<^sub>0 = l0\<rparr> [a]"
    apply (simp add: kfunc_def Fb_def Fa_def, auto)
    by (rule_tac x = "[]" in exI, simp) 
end
