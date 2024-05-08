theory Rabin_Closest_Pair 
  imports "HOL.Real"
begin
  
(* We verify Rabin's closest pair algorithm in 2D Euclidean space *)

section "Preliminaries"

type_synonym point = "real * real"

fun dist :: "point => point => real" where 
"dist (x1, y1) (x2, y2) = (x1 - x2)^2 + (y1 - y2)^2"

fun brute_force_dist :: "(point * point) list => real" where 
"brute_force_dist [] = -1" |
"brute_force_dist (x#xs) = (
    let dist' = brute_force_dist xs; curr = dist (fst x) (snd x) in 
    (if dist' < curr then dist' 
     else curr)
     )"

theorem brute_force_correct: "\<forall>(a, b) \<in> set points. dist a b \<ge> brute_force_dist points"
by (induction points) (auto simp del: dist.simps simp add: Let_def) 

fun build_pairs :: "point list => (point * point) list" where 
"build_pairs [] = []" |
"build_pairs (x#xs) = (map (\<lambda>a. (x, a)) xs) @ build_pairs xs"

lemma build_pairs_correct: " \<forall> a \<in> set xs. \<forall> b \<in> set xs. a \<noteq> b \<longrightarrow> (a, b) \<in> set (build_pairs xs) \<or> (b, a) \<in> set (build_pairs xs)"
by (induction xs) auto

section "Grids"


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

lemma build_grid_map_correct:
  assumes "d > 0" "m = build_grid_map xs d (\<lambda>_ _. [])" "p \<in> set xs"
  shows "p \<in> set (m \<lfloor>(fst p)/ d\<rfloor>  \<lfloor>(snd p) / d\<rfloor>)"
  using assms apply (induction xs arbitrary: p m)
  by  (auto simp: Let_def; force)+

definition find_in_grid_map :: "int \<Rightarrow> int \<Rightarrow> grid_map \<Rightarrow> real" where 
"find_in_grid_map x y m \<equiv> (
  if length (m x y) > 1 then brute_force_dist ( build_pairs (m x y))
  else brute_force_dist (build_pairs (
      m x y @ (m (x + 1) y) @ (m (x - 1) y) @ (m x (y + 1) @ (m x (y - 1)) @ (m (x + 1) (y + 1)) @
      (m (x + 1) (y - 1)) @ (m (x - 1) (y + 1)) @ (m (x - 1) (y - 1))
  )))
)"


end 