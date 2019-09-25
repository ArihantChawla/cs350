declare SingleAssignmentStore CurrIndex
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
      %{Browse assignitem2#Item.2}
      case Item.2
      of equivalence(New)|nil then 
	 if New == H then
	       %Item.2.1 = Val %{ValueToBeAssigned Val}}
	    CurrentList := {Append @CurrentList [Item.1 Val]}
	 else
	    CurrentList := {Append @CurrentList Item}
	 end
      [] literal(New)|nil then
	 CurrentList := {Append @CurrentList Item}
      [] record | L | Pairs then
	 local NewList in
	    %{Browse Pairs}
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
		       {Dictionary.put SingleAssignmentStore Y.1 Val}
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
   else {Exception.'raise' alreadyAssigned(Key Val {Dictionary.get SingleAssignmentStore Key ?})}
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
	 if Val == {Dictionary.get SingleAssignmentStore RefKey} then skip
	 else
	    {Exception.'raise' alreadyAssigned2( equivalence(Key) {Dictionary.get SingleAssignmentStore RefKey ?})}
	 end
      end
   end
end


{Browse {AddKeyToSAS}}
{Browse {AddKeyToSAS}}
{Browse {AddKeyToSAS}}
{Browse {Dictionary.entries SingleAssignmentStore}}
%{BindRefToKeyInSAS 1 3}
%{Browse {Dictionary.entries SingleAssignmentStore}}
%{Browse {RetrieveFromSAS 1}}
%{BindValueToKeyInSAS 2 [record literal(a) [[literal(f1) ident(x1)] [literal(f2) ident(x2)]]]}
%{BindValueToKeyInSAS 1 [record literal(a) [[literal(f1) ident(x1)] [literal(f2) ident(x2)]]]}
%{BindValueToKeyInSAS 1 10}
%{BindValueToKeyInSAS 1 10}
%{BindRefToKeyInSAS 1 2}
{Browse {Dictionary.entries SingleAssignmentStore}}
