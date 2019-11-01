declare
MST = {NewCell nil}

proc {AddToMST X}
   MST := {Append @MST [X]}
end

proc {SimpleScheduler}
   local
      Temp = @MST.1.1
   in
      {Push sepair(statement:Temp.statement env:{Adjoin @Current.env Temp.env})}
   end
   MST := {List.drop @MST 1}  
end

proc{IncrementSteps}
   CurrentSteps := @CurrentSteps + 1 
end

proc {SuspendThread}
   local Temp in
      Temp = {Pop}
      {AddToMST [sepair(statement:Temp.statement env:{Adjoin @Current.env Temp.env})]}
      {Browse "Thread Suspended"}
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
 
