/*
 *  Code for Question1.1
 *  --------------------------------------------
 *  To test please change the value corresponding
 *  to N in the 'in' block of code.
 */
local
   Y = unit('NOT ENOUGH ELEMENTS TO DROP')
   fun {Drop N Xs}
      if N == 0 then
	 Xs
      else
	 if (Xs == nil) then
	    Y
	 else
	    {Drop N-1 Xs.2}
	 end
      end
   end
in
   {Browse {Drop 1 [1 2 3 4 5 6 7 8]}}
end


/*
 *  Code for Question1.2
 *  --------------------------------------------
 *  To test please change the value corresponding
 *  to Xs and Ys in the 'in' block of code.
 */

local
   Zs = {NewCell nil}
   F = {NewCell 1}
   E = unit('LENGTH OF Xs AND Ys DO NOT MATCH')
   fun {Zip Xs Ys}
      if Xs == nil then
	 if Ys == nil then
	    @Zs
	 else
	    E   
	 end
      else
	 if Ys == nil then E else	    
	    local
	       A = Xs.1
	       B = Ys.1
	       C = A#B
	    in
	       Zs := {Append @Zs [C]}
	       {Zip Xs.2 Ys.2}
	    end	 
	 end
      end
   end
in
   {Browse{Zip [1 2 3] [4 5 6]}}
end

/* --------- Code for Question1.3 -------- */

local
   Last = {NewCell 0}
   Zs = {NewCell nil}
   F = {NewCell 1}
   fun {DeDup Xs}
      if Xs == nil then
	 {List.reverse @Zs}
      else
	 if @F == 1 then
	    F := 0
	    Zs := [Xs.1]
	    Last := Xs.1
	    {DeDup Xs.2}
	 else
	    if Xs.1 == @Last then
	       {DeDup Xs.2}
	    else
	       Last := Xs.1
	       Zs := {Append @Zs [Xs.1]}
	       {DeDup Xs.2}
	    end
	 end
      end
   end
in
   {Browse{DeDup [1 1 2 2 2 2 3 3 4 4 4 4 5]}}
end


/* --------- Code for Question1.4 -------- */

local
   fun{Length Xs}
      {FoldR {Map Xs fun{$ X} 1 end} fun{$ X Y} X+Y end 0}
   end
in
   {Browse{Length [1 2 3 4 5]}}
end


/* --------- Code for Question1.5 -------- */

local 
   fun{MapUsingFoldR L F}
      if L == nil then L
      else
	 {FoldR [L.1 0.0] fun{$ A B} {F A} + B end 0}|{MapUsingFoldR L.2 F}
      end
   end
in
{Browse{MapUsingFoldR [2.7 1.4 3.9] FloatToInt}} 
end
{Browse{Map [2.7 1.4 3.9] FloatToInt}}


/* --------- Code for Question1.6 -------- */

local
   K = {NewCell nil}
   proc {MapTree BinTree F}
      case BinTree
      of nil then skip
      else
	 {MapTree BinTree.left F} 
	 K := {F BinTree.root}
	 {Browse @K}
	 {MapTree BinTree.right F}
      end
   end
   T = tree(root:3 
	    left:tree(root:2 
		      left:tree(root:1 
				left:nil right:nil) 
		      right:nil)
	    right:tree(root:4 
		       left:nil 
		       right:tree(root:5 
				  left:nil right:nil)))
in
   {MapTree T fun{$ X} X*X end}
end


/* --------- Code for Question2 ---------- */

local
   fun {Subsets Xs}
      case Xs of nil then [nil]
      [] H|T then
	 local
	    A = {Subsets T}
	 in
	    {Append A {Map A fun {$ K} H|K end}}
	 end
      end
   end
in
   {Browse{Subsets [1 2 3]}}
end


/* --------- Code for Question3.1 -------- */

local
   Zs = {NewCell nil}
   Ks
   fun {LFilter Predicate Xs}
      Ks = {Map Xs fun {$ X} if {Predicate X} then Zs := X|@Zs else Zs := @Zs end end}
      if {Predicate {List.last Xs}} then 
	 {Append {List.reverse {List.reverse Ks}.1} [{List.last Xs}]}
      else
	 {List.reverse {List.reverse Ks}.1}
      end
   end
in
   {Browse{LFilter fun{$ X} X>0 end [1 0 2 3 4 5 0 7]}}
end

/* --------- Code for Question3.2 -------- */

local
   local
      Zs = {NewCell nil}
      Ks
      fun {LFilter Predicate Xs}
	 Ks = {Map Xs fun {$ X} if {Predicate X} then Zs := X|@Zs else Zs := @Zs end end}
	 if {Predicate {List.last Xs}} then 
	    {Append {List.reverse {List.reverse Ks}.1} [{List.last Xs}]}
	 else
	    {List.reverse {List.reverse Ks}.1}
	 end
      end
      fun lazy {InfiniteList Xs N}
	 {InfiniteList Xs|N+1 N+1}
      end
   end
in
   Ys = {InfiniteList [2] 2}
   {Browse{LFilter {fun X} X mod Ys.1 end Ys}
end
