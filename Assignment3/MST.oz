declare
MST = {NewCell nil}

proc {AddToMST X}
   MST := {Append @MST [X]}
end

proc {SimpleScheduler}
   local
      Temp = @MST.1.1 
   in
	if @Current == nil then 
		{Push sepair(statement:Temp.statement env:Temp.env)}
	else
      		{Push sepair(statement:Temp.statement env:{Adj @Current.env Temp.env})}
	end
   end
   MST := {List.drop @MST 1}  
end

proc{IncrementSteps}
   CurrentSteps := @CurrentSteps + 1 
end

proc {SuspendThread}
   local Temp in
      Temp = {Pop}
      if Temp \= nil then 
      {AddToMST [sepair(statement:Temp.statement env:{Adj @Current.env Temp.env})]} end
      {Browse 'Thread Suspended'}
      {SimpleScheduler}
   end
end

proc {RRScheduler}
   {IncrementSteps}
   local X in
      X = @CurrentSteps
      if X == TimeSlice then CurrentSteps := 0 {SuspendThread}
      else skip end
   end
end
 
