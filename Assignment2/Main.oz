functor
import
    Browser(browse: Browse)
define
   \insert 'SemanticStack.oz'
   \insert 'SingleAssignmentStore.oz'
   %\insert 'Unify.oz'
   
   Current = {NewCell nil}

   fun {Ident X Env}
        case X
        of ident(X1) then {Adjoin Env env({AddKeyToSAS})}
        else raise declarationError(X) end
        end
    end
   

   proc {Interpret AST}
        {Push sepair(statement:AST env:nil)}
        local Execute in
            proc {Execute}
                Current := {Pop}
                {Browse @Current}
                if @Current \= nil then
                    case @Current.statement
                    of nil then {Browse 'Complete'}

		    [] [nop] then {Execute}

		    [] [var X S] then
		       {Push sepair(statement:S env:{Ident X @Current.env})}
		       {Execute}

		    %[] [bind X Y] then
		    %   {Unify X Y @Current.env}
		    %   {Execute}
		       
		    [] X|Xr then
		       if Xr \= nil then
 			  {Push sepair(statement:Xr env:@Current.env)}
		       else skip end
		       {Push sepair(statement:X env:@Current.env)}
		       {Execute}
		    end
                else
                    {Browse 'Complete'}
                end
            end
            {Execute}
        end
    end
   % Problem 1
   % {Interpret [[nop] [nop] [nop]]}
   
   % Problem 2
   {Interpret [var ident(x) [var ident(y) [var ident(z) [nop]]]]}

   % Problem 3
   % {Interpret [localvar ident(x) [localvar ident(y) [bind ident(x) ident(y)]]]}




end
