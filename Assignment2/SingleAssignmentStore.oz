declare SingleAssignmentStore CurrIndex
FreeVars = {NewCell nil}
Idents = {Dictionary.new}
proc {RemoveIdents Xs}
   local Ys in
      Ys ={List.flatten Xs}
      case Ys of H|T then
	 case H
	 of ident(X)
	 then 
	    {Dictionary.remove Idents X}
	    {RemoveIdents T}
	 else	    
	    {RemoveIdents T}
	 end
      [] nil then skip
      end
   end
end

proc {FindVarIdents Xs}
   local Ys in
      Ys ={List.flatten Xs}
      case Ys of H|T then
	 case H of var
	 then
	    {Dictionary.remove Idents T.1.1}
	    {FindVarIdents T.2}
	 else
	    {FindVarIdents T}
	 end
      [] nil then skip
      end
   end
end

	    
proc {FindIdents Xs}
   local Ys in
      Ys = {List.flatten Xs}
      case Ys
      of H|T then
	 case H
	 of ident(X)
	 then 
	    {Dictionary.put Idents X equivalence(X)}
	    {FindIdents T}
	 else	    
	    {FindIdents T}
	 end
      [] nil then skip
      end
   end
end

proc{IntersectWithGlobal Env}
   local Xs in
      Xs = {Dictionary.keys Idents}
      local Z in
	 Z = {
	      Map Xs
	      fun {$ X}
		 if {Value.hasFeature Env X} then
		    FreeVars := {Adjoin @FreeVars env(X:Env.X)}
		    X
		 else
		    X%{Browse uDECLAREDVARIABLEUSED}
		 end
	      end
	      }
      end
   end
end	 
		    
proc {DealWithProcs Stat Env}
   case Stat
   of 'proc'|L|S
   then
      {FindIdents S}   
      {FindVarIdents S}   
      {RemoveIdents L}
      {IntersectWithGlobal Env}
   else
      skip
   end
end
SingleAssignmentStore = {Dictionary.new}
CurrIndex = {NewCell 0}

fun {AddKeyToSAS}
  CurrIndex:=@CurrIndex+1
  {Dictionary.put SingleAssignmentStore @CurrIndex equivalence(@CurrIndex)}
  @CurrIndex
end

fun {RetrieveFromSAS Key}
  {Dictionary.get SingleAssignmentStore Key ?} 
end

proc{AuxRecordAssign VarList H Val CurrentList}
   for Item in VarList do
      case Item.2
      of equivalence(New)|nil then 
	 if New == H then
	    CurrentList := {Append @CurrentList [[Item.1 Val]]}
	 else
	    CurrentList := {Append @CurrentList [Item]}
	 end
      [] literal(New)|nil then
	 CurrentList := {Append @CurrentList [Item]}
      [] record | L | Pairs then
	 local NewList in
	    NewList = nil
	    {AuxRecordAssign Pairs.1 H Val NewList}
	    CurrentList := {Append @CurrentList NewList}
	 end
      else
	 CurrentList := {Append @CurrentList Item}
      end
   end
end


proc {BindValueToKeyInSAS Key Val}
   case SingleAssignmentStore.Key
   of equivalence(X) then
      local Z in
	 Z = {Map {Dictionary.entries SingleAssignmentStore}
	      fun {$ Y}
		 case Y.2
		 of equivalence(V) then
		    if V == X then
		       case Val
		       of ['proc' L S] then
			  {DealWithProcs Val @Current.env}
			  {Dictionary.put SingleAssignmentStore Y.1 Val#[@FreeVars] }
		       else
			  {Dictionary.put SingleAssignmentStore Y.1 Val}
		       end
		    end
		    Y   
		 [] record | L | Pairs then
		    local Temp in 
		       Temp = {NewCell nil}
		       {AuxRecordAssign Pairs.1 X Val Temp}
		       {Dictionary.put SingleAssignmentStore Y.1 record|L|[@Temp]}
		    end
		    Y
		 else
		    Y
		 end	 
	      end
	     }
      end
   else 
      if Val == {Dictionary.get SingleAssignmentStore Key} then skip
      else
	 {Exception.'raise' alreadyAssigned(Key Val {Dictionary.get SingleAssignmentStore Key ?})}
      end
   end
end



proc {BindRefToKeyInSAS Key RefKey}
   local Val in
      {Dictionary.get SingleAssignmentStore Key Val}
      case Val
      of equivalence(X) then
	 local Z in
	    Z = {Map {Dictionary.entries SingleAssignmentStore}
		 fun {$ Y}
		    if Y.2 == equivalence(X) then
		       {Dictionary.put SingleAssignmentStore Y.1 SingleAssignmentStore.RefKey}
		    end
		    Y
		 end	 
		}
	 end
      else
	 {Browse {Dictionary.get SingleAssignmentStore RefKey}}
	 {Browse {Dictionary.get SingleAssignmentStore Key}}
	 if Val \= {Dictionary.get SingleAssignmentStore RefKey} then
	    {Exception.'raise' alreadyAssigned2( equivalence(Key) {Dictionary.get SingleAssignmentStore RefKey ?})}
	 else
	    skip
	 end
      end
   end
end

%{Browse {AddKeyToSAS}}
%{Browse {AddKeyToSAS}}
%{Browse {AddKeyToSAS}}
%{Browse SingleAssignmentStore.2}
%{Browse {Dictionary.entries SingleAssignmentStore}.2}
%{BindRefToKeyInSAS 1 3}
%{Browse {Dictionary.entries SingleAssignmentStore}}
%{Browse {RetrieveFromSAS 1}}
%{BindValueToKeyInSAS 2 [record literal(a) [[literal(feature1) literal(c)] [literal(feature) literal(b)] [literal(feature3) literal(c)]]]   }
%{BindValueToKeyInSAS 1 [record literal(a) [[literal(feature1) literal(c)] [literal(feature2) literal(b)] [literal(feature3) literal(c)]]]  }
%{BindValueToKeyInSAS 3 [record literal(a) [[literal(feature1) literal(c)] [literal(feature2) literal(b)] [literal(feature3) literal(c)]]]  }
%{BindValueToKeyInSAS 1 10}
%{BindValueToKeyInSAS 1 10}
%{BindRefToKeyInSAS 1 2}
%{Browse {Dictionary.entries SingleAssignmentStore}}