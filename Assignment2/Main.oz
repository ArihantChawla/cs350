declare
Current = {NewCell nil}
\insert 'SemanticStack.oz'
\insert 'SingleAssignmentStore.oz'
\insert 'Unify.oz'



fun {AddToEnv X Env}
   case X
   of ident(X1) then
      local Y in
	 Y = {AddKeyToSAS} 
	 {Adjoin Env env(X1:Y)}
      end
   else raise declarationError(X) end
   end
end

proc {Interpret AST}
   {Push sepair(statement:AST env:nil)}
   local Execute in
      proc {Execute}
	 Current := {Pop}
	 {Browse @Current#{Dictionary.entries SingleAssignmentStore}}
	 if @Current \= nil then
	    case @Current.statement
	    of nil then {Browse 'Complete'}

	    [] [nop] then {Execute}

	    [] [var X S] then
	       {Browse S}
	       {Push sepair(statement:S env:{AddToEnv X @Current.env})}
	       {Execute}
	       
	    [] [bind X Y] then
	       %{Browse 'test'}
	       {Unify X Y @Current.env}
	       {Browse 'test'}
	       {Browse @Current.env}
	       {Browse SingleAssignmentStore.1}
	       %{Browse SingleAssignmentStore.2}
	       local A in
		  A = {Pop}
		  {Browse A}
		  if A \= nil then
		     {Push sepair(statement:A.statement env:{Adjoin A.env @Current.env })}
		  else
		     {Push sepair(statement:nil env:@Current.env)}
		  end
	       end
	       {Execute}
	       
	       
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


%---------Problem 1----------%

% {Interpret [[nop] [nop] [nop]]}
% {Interpret [[[[nop]]]]}

%---------Problem 2

% {Interpret [var ident(x) [var ident(y) [var ident(x) [nop]]]]} 
% {Interpret [ [var ident(x) [nop]] [var ident(y) [nop]] [var ident(z) [nop]] ]} 
 
%{Interpret [[nop] [var ident(x) [nop]] [nop]]}

/*{Interpret  [var ident(x)
                     [var ident(y)
                         [
                             [var ident(x)
                                 [nop]
                             ]
                             [nop]
                         ]
                    ]
                 ]}
*/


% Problem 3

%{Interpret [[var ident(x) [var ident(y) [bind ident(x) ident(y)]]][var ident(z) [nop]]]}


/*      {Interpret  [var ident(x)
                     [var ident(y)
                        [bind ident(x) ident(y)]
                        ]
                 ]
                 }

*/

    % Problem 4a
   /* 
     {Interpret  [var ident(x)
                     [bind ident(x) [record literal(a) [literal(f1) ident(x)]]]
                 ]}
                
   */
     /*
     {Interpret  [var ident(x)
                     [var ident(y)
                         [
                             [bind ident(x) [record literal(a) [[literal(f1) ident(y)]]]]
                             [bind ident(y) literal(100)]
                 
			 ]
                     ]
                 ]}
      */     

   /*   
{Interpret [[var ident(x) [var ident(y)
			   [bind
			    
			    [record literal(a)[[literal(feature1) literal(b)] [literal(feature2) literal(b)] [literal(feature3) literal(c)]]]
			    
			    [record literal(a)[[literal(feature1) ident(x)] [literal(feature) ident(x)] [literal(feature3) literal(c)]]]

					      ]]]]
}*/

      
/*
{Interpret [[var ident(x) [var ident(y)
			   [bind
			    
			    [record literal(a)[[literal(feature1) literal(b)] [literal(feature2) literal(b)] [literal(feature3) literal(c)]]]
			    
			    [record literal(a)[[literal(feature1) ident(x)] [literal(feature2) literal(b)] [literal(feature3) literal(c)]]]

					      ]]]]
} 
*/
    
    % Problem 5a
     /*{Interpret  [var ident(x)
                     [bind ident(x) literal(100)]
                 ]}
     */

%Problem 4b and 5b
/*{Interpret [
	     var ident(x)
	     [[ bind ident(x)
		['proc' [ ident(x1)] [[nop]] ]
	      ]]
	   ]
	    }
*/

/*
{Interpret [
	     var ident(x)
	     [[ bind ident(x)

		['proc'
		 [idents(x1) idents(x2)]
		 [[var ident(x) [[bind ident(x) literal(10)]]]]]
	      ]]
	   ]
}
*/
/*
{Interpret [
	    var ident(x)
	    [[ var ident(y)

	       [[ bind ident(x)


		  ['proc'

		   [idents(x1) idents(x2)]

		   [[bind ident(y) literal(10)]]]]]

		
	     ]]
	    
	   ]
}
*/


