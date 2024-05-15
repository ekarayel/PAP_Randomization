theory Rabin_Closest_Pair 
  imports "HOL-Probability.Probability_Mass_Function" Complex_Main
begin
  
(* We verify Rabin's closest pair algorithm in 2D Euclidean space *)

section "Preliminaries"

type_synonym point = "real * real"

fun dist :: "point => point => real" where 
"dist (x1, y1) (x2, y2) = sqrt ((x1 - x2)^2 + (y1 - y2)^2)"

lemma dist_compact_on_finite: "p \<notin> set (x # xs) \<Longrightarrow> \<exists>q \<in> set (x # xs). \<forall>r \<in> set (x # xs). dist p q \<le> dist p r"
proof (induction xs arbitrary: x)
  case (Cons a xs)
  hence " \<exists>q\<in>set (a # xs). \<forall>r\<in>set (a # xs). dist p q \<le> dist p r"
    by simp 
  then obtain q where "q \<in> set (a # xs)" "\<forall>r\<in>set (a # xs). dist p q \<le> dist p r"
    by blast 
  then show ?case
    by (cases "dist p q \<le> dist p x") auto
qed auto

lemma dist_symm: "dist a b = dist b a" 
  by (metis dist.simps surj_pair power2_commute)


fun brute_force_dist :: "(point * point) list => real" where 
"brute_force_dist [] = -1" |
"brute_force_dist (x#xs) = (
    let dist' = brute_force_dist xs; curr = dist (fst x) (snd x) in 
    (if dist' < curr then dist' 
     else curr)
     )"

theorem brute_force_dist_correct: "(a, b) \<in> set points \<Longrightarrow> dist a b \<ge> brute_force_dist points"
by (induction points) (auto simp del: dist.simps simp add: Let_def) 

fun build_pairs :: "point list => (point * point) list" where 
"build_pairs [] = []" |
"build_pairs (x#xs) = (map (\<lambda>a. (x, a)) xs) @ build_pairs xs"

lemma build_pairs_correct: " a \<in> set xs \<Longrightarrow> b \<in> set xs \<Longrightarrow> a \<noteq> b \<Longrightarrow>  (a, b) \<in> set (build_pairs xs) \<or> (b, a) \<in> set (build_pairs xs)"
by (induction xs) auto

section "Grid Map"


(* Squares in 2D space can be represented with two end points.
   Since grid length is fixed, we simply need the initial point for representation,
   hence we store them in a list of list *)


type_synonym grid = "point list"
type_synonym grid_map = "int \<Rightarrow> int => grid"

(*
a grid is a list that stores all points
a grid map is a function from the index of the left-lower point to the grid
*)


fun build_grid_map :: "point list  => real => grid_map => grid_map" where 
"build_grid_map [] d m = m" |
"build_grid_map (a#as) d m = 
  (let x = \<lfloor>(fst a) / d\<rfloor>; y = \<lfloor>(snd a) / d\<rfloor>;
       m' = build_grid_map as d m
  in 
    (\<lambda>z1 z2. if z1 = x \<and> z2 = y then a # (m' z1 z2) else m' z1 z2)
  )"

lemma build_grid_map_sound:
  assumes "d > 0" "m = build_grid_map xs d (\<lambda>_ _. [])" "p \<in> set xs"
  shows "p \<in> set (m \<lfloor>(fst p)/ d\<rfloor>  \<lfloor>(snd p) / d\<rfloor>)"
  using assms apply (induction xs arbitrary: p m)
  by  (auto simp: Let_def; force)+

lemma build_grid_map_complete:
  assumes  "m = build_grid_map xs d (\<lambda>_ _. [])"
  shows "p \<in> set (m x y) \<Longrightarrow> (x = \<lfloor>(fst p)/ d\<rfloor> \<and> y = \<lfloor>(snd p) / d\<rfloor> \<and> p \<in> set xs)"
using assms proof (induction xs arbitrary: p m x y)
  case (Cons a xs)
  obtain m' where m'_def: "m' = build_grid_map xs d (\<lambda>_ _. [])"
    by blast 
  hence aux1: "m = build_grid_map [a] d m'" 
    by (auto simp: Let_def Cons(3))
  hence aux2: "m x y = a # m' x y \<or> m' x y = m x y" 
    by auto
  then show ?case 
    proof (cases "m' x y")
      case Nil
      hence "m x y = [p]" "m x y = [a]"
        using Cons(2) aux2 by fastforce+
      hence "a = p" 
        by force
      moreover have "x = \<lfloor>fst a / d\<rfloor> \<and> y = \<lfloor>snd a / d\<rfloor>"
        using aux1 \<open>m x y = [a]\<close> Nil not_Cons_self2 by fastforce
      ultimately show ?thesis by force
    next
      case (Cons a list)
      then obtain q where "q \<in> set (m' x y)" 
        by fastforce
      then have "x = \<lfloor>fst q / d\<rfloor> \<and> y = \<lfloor>snd q / d\<rfloor> \<and> q \<in> set xs"
        by (simp add: Cons.IH m'_def assms(1))
      then show ?thesis
        by (smt (verit) Cons.IH Cons.prems(1) assms(1) aux1 build_grid_map.simps(1) 
              build_grid_map.simps(2) list.set_intros(1) list.set_intros(2) m'_def set_ConsD)
    qed
qed simp

thm floor_divide_lower floor_divide_upper

definition "neighbors m x y \<equiv> 
       m x y @ (m (x + 1) y) @ (m (x - 1) y) @ (m x (y + 1)) @ (m x (y - 1)) 
      @ (m (x + 1) (y + 1)) @ (m (x + 1) (y - 1)) @ (m (x - 1) (y + 1)) @ (m (x - 1) (y - 1))"

definition "in_map p m \<equiv> \<exists>x y. p \<in> set (m x y)"

lemma dist_of_non_neighbors :
  assumes "p \<in> set (m x y)" "m = build_grid_map xs d (\<lambda>_ _. [])" "d > 0"
  shows "in_map (a, b) m \<and> (a, b) \<notin> set (neighbors m x y) \<longrightarrow> dist p (a, b) \<ge> d"
proof
    fix  a b
    let ?x' = "\<lfloor>a / d\<rfloor>" let ?y' = "\<lfloor>b / d\<rfloor>"
    let ?x1 = "fst p" let ?y1 = "snd p" 
    have "\<forall>x1 y1. (a, b) \<in> set (m x y)\<longrightarrow> x = ?x' \<and> y = ?y'"
      using assms build_grid_map_complete by force
    moreover assume "in_map (a, b) m \<and> (a, b) \<notin> set (neighbors m x y)"
    ultimately consider "?x' < x - 1" | "?x' > x + 1" | "?y' < y - 1" | "?y' > y + 1"
      unfolding in_map_def neighbors_def apply auto 
      by (smt (verit, ccfv_SIG) assms(2) build_grid_map_complete prod.sel(1) prod.sel(2))
    then show "d \<le> dist p (a, b)"
    proof cases
      case 1
      then have "\<lfloor>a / d\<rfloor> \<le> x - 2"
        by simp
      then have "\<lfloor>a / d \<rfloor> * d \<le> (x - 2) * d"
        using assms(3) by fastforce
      moreover have "a - d \<le> \<lfloor>a / d \<rfloor> * d" 
        by (smt (verit, best) assms(3) divide_diff_eq_iff less_divide_eq_1_pos real_of_int_floor_ge_diff_one)
      ultimately have "a - d \<le> (x - 2) * d"
        by argo  
      hence "a \<le> (x - 2) * d + d" 
        by argo
      hence "a \<le> x * d - d"
        by (simp add: mult.commute right_diff_distrib)
      moreover have "x * d \<le> ?x1"
        using build_grid_map_complete[OF assms(2) assms(1)] floor_divide_lower[OF assms(3)] 
        by fast
      ultimately have "d \<le> ?x1 - a" 
        by argo
      also have "... \<le> sqrt ((?x1 - a)^2 + (?y1 - b)^2)" 
        by auto
      finally show ?thesis
        by (metis dist.simps prod.collapse)
    next
      case 2
      then have "\<lfloor>a / d \<rfloor> * d \<ge> (x + 2) * d"
        using assms(3) by fastforce
      moreover have "a  \<ge> \<lfloor>a / d\<rfloor> * d" 
        using floor_divide_lower assms(3) by blast 
       ultimately have "a \<ge> (x + 2) * d"
        by argo  
      hence "a \<ge> (x + 1) * d + d" 
        by (simp add: distrib_left mult.commute)
      moreover have "(x + 1) * d > ?x1"
        using build_grid_map_complete[OF assms(2) assms(1)] floor_divide_upper[OF assms(3)] 
        by force
      ultimately have "d \<le> a - ?x1" 
        by argo
      also have "... \<le> sqrt ((a - ?x1)^2 + (?y1 - b)^2)" 
        by auto
      also have "... \<le> sqrt ((?x1 - a )^2 + (?y1 - b)^2)"
        by (simp add: power2_commute)
      finally show ?thesis
        by (metis dist.simps prod.collapse)
    next
      case 3
      then have "\<lfloor>b / d\<rfloor> \<le> y - 2"
        by simp
      then have "\<lfloor>b / d \<rfloor> * d \<le> (y - 2) * d"
        using assms(3) by fastforce
      moreover have "b - d \<le> \<lfloor>b / d \<rfloor> * d" 
        by (smt (verit, best) assms(3) divide_diff_eq_iff less_divide_eq_1_pos real_of_int_floor_ge_diff_one)
      ultimately have "b - d \<le> (y - 2) * d"
        by argo  
      hence "b \<le> (y - 2) * d + d" 
        by argo
      hence "b \<le> y * d - d"
        by (simp add: mult.commute right_diff_distrib)
      moreover have "y * d \<le> ?y1"
        using build_grid_map_complete[OF assms(2) assms(1)] floor_divide_lower[OF assms(3)] 
        by fast
      ultimately have "d \<le> ?y1 - b" 
        by argo
      also have "... \<le> sqrt ((?x1 - a)^2 + (?y1 - b)^2)" 
        by auto
      finally show ?thesis
        by (metis dist.simps prod.collapse)
    next
      case 4
      then have "\<lfloor>b / d \<rfloor> * d \<ge> (y + 2) * d"
        using assms(3) by fastforce
      moreover have "b  \<ge> \<lfloor>b / d\<rfloor> * d" 
        using floor_divide_lower assms(3) by blast 
       ultimately have "b \<ge> (y + 2) * d"
        by argo  
      hence "b \<ge> (y + 1) * d + d" 
        by (simp add: distrib_left mult.commute)
      moreover have "(y + 1) * d > ?y1"
        using build_grid_map_complete[OF assms(2) assms(1)] floor_divide_upper[OF assms(3)] 
        by force
      ultimately have "d \<le> b - ?y1" 
        by argo
      also have "... \<le> sqrt ((b - ?y1)^2 + (?x1 - a)^2)" 
        by auto
      also have "... \<le> sqrt ((?x1 - a )^2 + (?y1 - b)^2)"
        by (simp add: power2_commute)
      finally show ?thesis
        by (metis dist.simps prod.collapse)
    qed
  qed


lemma nearest_in_neighbors: 
  assumes "p \<in> set (m x y)" "set (neighbors m x y) - {p} \<noteq> {}" "m = build_grid_map xs d (\<lambda>_ _. [])" "d > 0"
  shows "\<exists>q \<in> set (neighbors m x y). q \<noteq> p \<and> (\<forall>r. in_map r m \<and> r \<noteq> p \<longrightarrow> dist p r \<ge> dist p q \<or> dist p r \<ge> d)"
proof -
  obtain z zs where "set (z # zs) = set (neighbors m x y) - {p}"
    by (metis assms(2) all_not_in_conv insert_absorb list.simps(15) set_removeAll)
  hence "\<exists>q \<in> set (neighbors m x y) - {p}.\<forall> r \<in> set (neighbors m x y)  - {p}. dist p r \<ge> dist p q"
    using dist_compact_on_finite by fast
  then obtain q where "q \<in> set (neighbors m x y) - {p}" "\<forall> r \<in> set (neighbors m x y)  - {p}. dist p r \<ge> dist p q"
    by blast
  then show ?thesis using dist_of_non_neighbors[of p m x y xs d] assms by fastforce
qed 

definition find_in_grid_map :: "int \<Rightarrow> int \<Rightarrow> grid_map \<Rightarrow> real" where 
"find_in_grid_map x y m \<equiv>  brute_force_dist (build_pairs (neighbors m x y ))"

theorem find_in_grid_map_correct:
  fixes p q
  assumes "d > 0" "m = build_grid_map xs d (\<lambda>_ _. [])" "p \<in> set (m x y)" "in_map q m" "q \<noteq> p"
  shows "dist p q \<ge> find_in_grid_map x y m \<or> dist p q \<ge> d"
proof (cases "set (neighbors m x y) - {p} \<noteq> {}")
  case True
  then obtain r where r_def: "r \<in> set (neighbors m x y)" "r \<noteq> p" 
      "(\<forall>s. in_map s m \<and> s \<noteq> p \<longrightarrow> dist p r \<le> dist p s \<or>  d \<le> dist p s)"
    using nearest_in_neighbors assms by blast
  from r_def(3) assms(4, 5) have aux: "dist p r \<le> dist p q \<or> d \<le> dist p q" by fastforce 
  from assms(3) have "p \<in> set (neighbors m x y)"
    unfolding neighbors_def by fastforce
  from this r_def(1) r_def(2) have 
    "(r, p) \<in> set (build_pairs (neighbors m x y)) \<or> (p, r) \<in> set (build_pairs (neighbors m x y))"
    using build_pairs_correct[of r "neighbors m x y" p] by blast
  then consider "(r, p) \<in> set (build_pairs (neighbors m x y))" | "(p, r) \<in> set (build_pairs (neighbors m x y))"
    by blast
  then have "find_in_grid_map x y m \<le> dist p r"  
    unfolding find_in_grid_map_def
    using dist_symm by (cases; metis brute_force_dist_correct)+
  then show ?thesis using aux by argo 
next
  case False
  then show ?thesis using dist_of_non_neighbors[of p m x y xs d "fst q" "snd q"] assms by auto 
qed

section "Introduce Randomization" 

fun traverse_grid_map :: "point list \<Rightarrow> real \<Rightarrow> grid_map \<Rightarrow> real"
	where 
"traverse_grid_map [] d _ = d" | 
"traverse_grid_map (z # zs) d m = (
	let x = \<lfloor>(fst z) / d\<rfloor>; y = \<lfloor>(snd z) / d\<rfloor>; 
	prev =  (traverse_grid_map zs d m); curr = find_in_grid_map x y m in
	if prev > curr then curr else prev
)"

theorem traverse_grid_map_correct:
	assumes "d > 0" "p \<in> set xs" "q \<in> set xs" "p \<noteq> q" "m = build_grid_map xs d (\<lambda>_ _. [])"
	shows "traverse_grid_map xs d m \<le> min d (dist p q)"
proof -
	let ?x1 = "\<lfloor>fst p / d\<rfloor>" let ?y1 = "\<lfloor>snd p / d\<rfloor>"
	let ?x2 = "\<lfloor>fst q / d\<rfloor>" let ?y2 = "\<lfloor>snd q / d\<rfloor>"
	from assms have "p \<in> set (m ?x1 ?y1)" "q \<in> set (m ?x2 ?y2)" 
   	using build_grid_map_sound by blast+ 
  moreover then have "in_map p m" "in_map q m"
		unfolding in_map_def by blast+ 
	ultimately have A: "dist p q \<ge> find_in_grid_map ?x1 ?y1 m \<or> dist p q \<ge> d" and
									"dist q p \<ge> find_in_grid_map ?x2 ?y2 m \<or> dist q p \<ge> d"
		using find_in_grid_map_correct assms(1, 4, 5) by auto
	then have B: "dist p q \<ge> find_in_grid_map ?x2 ?y2 m \<or> dist p q \<ge> d"
		using dist_symm by auto
	from A B assms(1-4) show ?thesis 
	proof (induction xs d m rule: traverse_grid_map.induct)
		case (2 z zs d m)
		have C: "traverse_grid_map zs d m \<le> d" 
			by (induction zs)  (auto simp: Let_def)
		from 2 consider "p = z" | "q = z" | "p \<in> set zs \<and> q \<in> set zs"
  	by force
 		 then show ?case
		proof cases
			case 1
			then show ?thesis using 2 C by (auto simp: Let_def)
		next
			case 2
			then show ?thesis using "local.2.prems" C by (auto simp: Let_def)
		next
			case 3
			with "2" have "traverse_grid_map zs d m \<le> min d (Rabin_Closest_Pair.dist p q)" 
				by blast
			then show ?thesis by (auto simp: Let_def)
		qed
	qed auto
qed 

(*This shows that our traversal indeed finds the closest pair of points*)
	

definition first_phase :: "point list \<Rightarrow> real pmf" where 
"first_phase ps = do {
	xs \<leftarrow> replicate_pmf (nat \<lceil>sqrt (length ps)\<rceil>) (pmf_of_set (set ps));
	return_pmf (brute_force_dist (build_pairs xs))
}"

definition "second_phase ps d \<equiv> (
	let m = build_grid_map ps d (\<lambda>_ _. []) in 
	traverse_grid_map ps d m
)"

definition rabins_closest_pair :: "point list \<Rightarrow> real pmf" where 
"rabins_closest_pair ps = do {
	d \<leftarrow> first_phase ps;
	return_pmf (second_phase ps d)
} "


end 