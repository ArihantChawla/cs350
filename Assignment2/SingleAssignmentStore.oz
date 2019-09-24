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

proc {BindValueToKeyInSAS Key Val}
  local Val in
    {Dictionary.get SingleAssignmentStore Key Val}
    case Val
    of equivalence(X) then {Dictionary.put SingleAssignmentStore Key Val}
    else {Exception.'raise' alreadyAssigned(Key Val {Dictionary.get SingleAssignmentStore Key ?})}
    end 
  end
end

proc {BindRefToKeyInSAS Key RefKey}
  local Val in
    {Dictionary.get SingleAssignmentStore Key Val}
    case Val
    of equivalence(X) then {Dictionary.put SingleAssignmentStore Key reference(RefKey)}
    else {Exception.'raise' alreadyAssigned2(Key {Dictionary.get SingleAssignmentStore Key ?})}
    end 
  end
end
