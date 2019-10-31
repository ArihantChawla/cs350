declare
MST = {NewCell nil}

proc {AddToMST X}
   MST := {Append @MST [X]}
end

proc {SimpleScheduler}
   %{Browse 'SSBefore'}
   %{Browse @SemanticStack}
   local
      Temp = @MST.1.1
   in
      %{Browse Temp.env}
      {Push sepair(statement:Temp.statement env:Temp.env)}
   end
   
   MST := {List.drop @MST 1} 
   %{Browse 'SS'}
   %{Browse @SemanticStack}
   %{Browse 'MST'}
   %{Browse @MST}
   %Current := {Pop}
   %{Browse 'Curr'}
   %{Browse @Current} 
end
