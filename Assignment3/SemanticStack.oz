declare

SemanticStack = {NewCell nil}
proc {Push SEPair}
    SemanticStack := SEPair | @SemanticStack
end

fun {Pop}
    case @SemanticStack
    of nil then nil
    [] SEPair | RemStack then
        SemanticStack := RemStack
        SEPair
    end
end


