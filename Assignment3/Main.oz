declare
Current = {NewCell nil}
SemanticStack = {NewCell nil}
CurrentSteps = {NewCell 0}
TimeSlice = 1

fun {Adj R1 R2}
   case R1
   of nil then
      case R2
      of nil then nil
      else R2
      end
   else
      case R2
      of nil then R1
      else {Adjoin R1 R2}
      end
   end
end


\insert 'SemanticStack.oz'
\insert 'SingleAssignmentStore.oz'
\insert 'Unify.oz'
\insert 'MST.oz'


fun {AddToEnv X Env}
   case X
   of ident(X1) then
      local Y in
	 Y = {AddKeyToSAS} 
	    {Adj Env env(X1:Y)}
	 
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
	       of nil then
		  if @MST == nil then
		     {Browse 'Complete'}
		  else
		     {Browse 'thread completed'}
		     {SimpleScheduler}
		     {Execute}
		  end
		  
	       [] [nop] then {Execute}
		  
	       [] [var X S] then
	      % {Browse S}
		  {Push sepair(statement:S env:{AddToEnv X @Current.env})}
		  {RRScheduler} {Execute} 
		  
	       [] [bind X Y] then
		  {Unify X Y @Current.env} 
		  local A in
		     A = {Pop}
		     if A \= nil then
			{Push sepair(statement:A.statement env:{Adj A.env @Current.env })}
		     else
			{Push sepair(statement:nil env:@Current.env)}
		     end	       
		  end
		  {RRScheduler} {Execute} 
		  
		  
	       [] conditional|ident(X)| S1|S2|nil then
		  case {RetrieveFromSAS @Current.env.X}
		  of  literal('true') then {Push sepair(statement:S1 env: @Current.env)} {RRScheduler} {Execute} 
		  []  literal('false') then {Push sepair(statement:S2 env: @Current.env)} {RRScheduler} {Execute} 	  
		  else
		
		     local Temp in
			
			if @SemanticStack \= nil then
			   Temp = {Pop}
			   {AddToMST [sepair(statement:Temp.statement env:{Adj @Current.env Temp.env})]}
			end
			{AddToMST [sepair(statement:@Current.statement env:@Current.env )]}
			
		
		     end
		     %{Browse @MST}
		     {SuspendThread} {Execute}
		  end
		  
		  
	       [] [match ident(Z) P1 S1 S2] then
		  
		  
		  local P in P =  {RetrieveFromSAS @Current.env.Z}
		     case P
		     of  record | L | Pairs1 then 
			case P1
			of record|!L|Pairs2 then
			   if 
				 {List.length Pairs1.1} \=  {List.length Pairs2.1} then {Push sepair(statement:S2 env:@Current.env)} {RRScheduler} {Execute} 
			      
			   else
			      
			      Canon1 = {Canonize Pairs2.1}
			      Canon2 = {Canonize Pairs1.1}
			      Aux in 
			      proc {Aux X Y}
				 case X
				 of nil then skip 
				 [] H1|T1 then
				    case Y of H2|T2 then 
				       if H1.1 \= H2.1 then
					  {Push sepair(statement:S2 env:@Current.env)}
					  {RRScheduler} {Execute} 
				       else
					  local  A  in A = H1.2.1
					     
					     case A
				     
					     of ident(B) then
				      
						local D in D =  sepair(statement:@Current.statement env:{Adj @Current.env env(B:{FindinSAS H2.2.1})})
						   
						   Current := D
						end
				      
						{Unify A H2.2.1 @Current.env}
					     [] literal(C) then
						
						{Unify A H2.2.1 @Current.env}
					     end %case ka end      
					     {Aux T1 T2}
					  end %local A
			
				
				       end %ifelse	    
				    end %case	  
				 end    %case
			      end %proc   
			      {Aux Canon1 Canon2}
			      {Push sepair(statement:S1 env:@Current.env)} {RRScheduler} {Execute} 
			   end %main else end
			else     {Push sepair(statement:S2 env:@Current.env)} {RRScheduler} {Execute} 	
			end
		     else     {Push sepair(statement:S2 env:@Current.env)} {RRScheduler} {Execute} 	
		     end
		  end    
		  
	       [] apply|ident(X)|Tail then
		  {Browse {RetrieveFromSAS @Current.env.X}}
		  case {RetrieveFromSAS @Current.env.X}
		  of (['proc' L S]#CE) then
		     if {List.length Tail} \= {List.length L} then
			{Browse 'ERROR - INVALID NO OF ARGS.'}
		     else
		     %{Browse Tail}
		     %{Browse L}
		     %{Browse {Map L fun {$ X} X.1 end }}
		     %{Browse {Map Tail fun {$ X} X.1 end }}
		     %{Browse {List.zip L Tail fun {$ A B} env(B.1:@Current.env.A.1) end}}
		      %fun {$ Z Y} env(Z:@Current.env.Y) end}}
			{Browse {FoldR
				 {List.zip
				  {Map L fun {$ X} X.1 end }
				  {Map Tail fun {$ X} X.1 end }
				  fun {$ A B} env(A:@Current.env.B) end}
				 Adj
				 env()
			     }}
			
			{Push sepair(statement:S env:
						 {Adj
						  CE
						  {FoldR
						   {List.zip
						    {Map L fun {$ X} X.1 end }
						    {Map Tail fun {$ X} X.1 end }
						    fun {$ A B} env(A:@Current.env.B) end}
						   Adj
						   env()
						  }
						 }
				    )
			}
		     end
		  else
		     %{Browse 'ERROR - NOT A PROC'}


		     local Temp in
			
			if @SemanticStack \= nil then
			   Temp = {Pop}

			   
			   {AddToMST [sepair(statement:Temp.statement env:{Adj @Current.env Temp.env})]}
			   
			end
			{AddToMST [sepair(statement:@Current.statement env:@Current.env )]}
			
		
		     end
		     %{Browse @MST}
		     {SuspendThread} {Execute}



		     
	       end
		  {RRScheduler} {Execute} 
		  
		  
	    [] [sum ident(x) ident(y) ident(z)] then      % z = x + y
		  local
		     X = {RetrieveFromSAS @Current.env.x}.1
		     Y = {RetrieveFromSAS @Current.env.y}.1
		  Sum = X + Y
		  in	  
		     {BindValueToKeyInSAS @Current.env.z literal(Sum)}
	       end
		  {RRScheduler} {Execute} 
		  
	       [] [prod ident(x) ident(y) ident(z)] then      % z = x * y
	       local
		  X = {RetrieveFromSAS @Current.env.x}.1
		  Y = {RetrieveFromSAS @Current.env.y}.1
		  Sum = X * Y
	       in	  
		  {BindValueToKeyInSAS @Current.env.z literal(Sum)}
	       end
	       {RRScheduler} {Execute} 
	       
	       [] ['thread' S 'end'] then
	       %{Browse 'CurrBefore'}
	       %{Browse @Current}	       
		  local
		     TempStack = sepair(statement:S env:@Current.env)
	       in
		  %{Browse 'TS'}
		     {AddToMST [TempStack]}
		     Current := {Pop}
		     if @Current \= nil then
			{AddToMST [sepair(statement:@Current.statement env:{Adj @Current.env TempStack.env})]}
		     end
	          %{AddInMST TempStack}
		  %{AddInMST @Current}
%		  
%		  
		  end
		  {SimpleScheduler}
		  {Execute} 
		  
	       
	       [] X|Xr then
		  if Xr \= nil then
		     {Push sepair(statement:Xr env:@Current.env)}
	       else skip end
		  {Push sepair(statement:X env:@Current.env)}
		  {RRScheduler} {Execute} 
	       end
	 else
	    %{Browse @MST}
	    if @MST == nil then
	       
		  {Browse 'Complete'}
	    else
		  {SimpleScheduler}
		  {Execute} 
	       end
	    end
	 end
		{Execute} 
      end
   end
   

{Interpret
 [var ident(s1)
  [[ var ident(s2)
     [[ var ident(a)
	[
	 [bind ident(a) literal(10)]
	 ['thread'
	  [
	   [var ident(b)
	    [[var ident(t)[
	      [bind ident(t) literal(1)]
	      [bind ident(b)  ident(a)]
	      [conditional ident(s1)
	       [nop]
	       [[nop][nop]]
	      ]]
	     ]]
	   ]
	  ]
	  'end'
	 ]
	 ['thread'
	  [
	   [var ident(c)
	    [[var ident(u)[
	      [bind ident(u) literal(2)]
	      [bind ident(c) ident(a)]
	      [conditional ident(s2)
	       [nop]
	       [[nop][nop]]
	      ]
			   [bind ident(s1) literal('true')]
			  ]]]]]
	  'end'
	 ]
	 [var ident(a) [
			[bind ident(a) literal(100)]
			['thread'  [
				    [var ident(d)
				     [[var ident(v)[
						    [bind ident(v) literal(3)]
						    [bind ident(d) ident(a)]
						    [bind ident(s2) literal('false')]
						   ]]]]]
			 'end'
			]]
	 ]]
      ]]]]]
}



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
    
    /* {Interpret  [var ident(x)
                     [bind ident(x) [record literal(a) [literal(f1) ident(x)]]]
                 ]}
                
   */
     
 /*    {Interpret  [var ident(x)
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
}
*/
      
/*
{Interpret [[var ident(x) [var ident(y)
			   [bind
			    
			    [record literal(a)[[literal(feature1) literal(b)] [literal(feature2) literal(b)] [literal(feature3) literal(c)]]]
			    
			    [record literal(a)[[literal(feature1) ident(x)] [literal(feature2) literal(b)] [literal(feature3) literal(c)]]]

					      ]]]]
} */

    
    % Problem 5a
    /* {Interpret  [var ident(x)
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
	       [[var ident(z)
		 [[ bind ident(x)
		    ['proc'
		     [idents(x1) idents(x2)]

		     % [bind ident(x) literal(10)]
                    
		      [[bind ident(y)
		     ['proc' [idents(x3)] [ [bind ident(z) literal(10) ]]]]
		     
		    ]]
		  ]]
		 ]]
	     ]]
	    ]
}
*/
/*

{Interpret [
	    var ident(x)
	    [[ var ident(y)
	       [[ var ident(z)

		  [

		   [ bind ident(x)
		     ['proc'
		      [ident(x1) ident(x2)]
		      [bind ident(x2) ident(x1)]
		     ]   
		   ]
		   
		   [bind ident(y) literal(10)]

		   [apply ident(x) ident(y) ident(z)]

		   [nop]
		   
		  ]
		  
		]]	             

	     ]]
	   ]

}
*/
%%%%%%%%%%%%%%%%%problrm 9%%%%%%%%%%%%%%%%%%
/*
{Interpret [
	    var ident(x)
	    [[ var ident(y)
	       [[ var ident(z)
		  [
		   [bind ident(x) literal(2)]
		   [bind ident(y) literal(5)]
		   [prod ident(x) ident(y) ident(z)]
		  ]
		]]
	     ]]
	   ]
}

*/
/*
{Interpret [
	    var ident(x)
	    [[ var ident(y)
	       [[ var ident(z)
		  [
		   [bind ident(x) literal(2)]
		   [bind ident(y) literal(5)]
		   [sum ident(x) ident(y) ident(z)]
		  ]
		]]
	     ]]
	   ]
}

*/

%%%%problem 6 

/*    {Interpret  [var ident(x)
                   [ [var ident(y)
                         [ [bind ident(x) literal('true')]
                             [conditional ident(x)
                                [ [bind ident(y) literal(42)]]
                                [ [bind ident(y) literal(0)]]
                             ]
                         ]
                     ]
                ] ]}

*/

 /*  {Interpret  [var ident(x)
                   [ [var ident(y)
                         [ [bind ident(x) literal('false')]
                             [conditional ident(x)
                                [ [bind ident(y) literal(42)]]
                                [ [bind ident(y) literal(0)]]
                             ]
                         ]
                     ]
                ] ]}

*/


%%%%%%%problem 7


/*
{Interpret  [var ident(x)
	     [[var ident(y)
                        [[var ident(z)
                             [   [bind ident(y) literal(100)]
                                 [bind ident(x) [record literal(a) [[literal(f1) ident(y)]]]]
                                 [match ident(x) [record literal(a) [[literal(f1) ident(w)]]]
                                    [ [bind ident(z) literal(42)]]
                                    [ [bind ident(z) literal(0)]]]
                                 ]
                            ]
		      ]]]
                   ]
                 }


*/


/*
{Interpret  [var ident(x)
	     [[var ident(y)
                        [[var ident(z)
                             [   
                                 [bind ident(x) [record literal(a) [[literal(f1) ident(y)] [literal(f2) ident(y)]]]]
                                 [match ident(x) [record literal(a) [[literal(f1) ident(w)]]]
                                    [ [bind ident(z) literal(42)]]
                                    [ [bind ident(z) literal(0)]]]
                                 ]
                            ]
		      ]]]
                   ]
                 }


*/
/*
{Interpret  [var ident(x)
	     [[var ident(y)
                        [[var ident(z)
                             [   
                                 [bind ident(x) [record literal(a) [[literal(f1) ident(y)] [literal(f2) ident(z)]]]]
                                 [match ident(x) [record literal(a) [[literal(f1) ident(w)][literal(f2) ident(r)]]]
                                    [ [bind ident(z) literal(42)]]
                                    [ [bind ident(z) literal(0)]]]
                                 ]
                            ]
		      ]]]
                   ]
                 }

*/

  /*   {Interpret  [var ident(x)
                     [var ident(y)
                         [var ident(z)
                             [
                                 [bind ident(x) [record literal(a) [[literal(f1) literal(100)]]]]
                                 [match ident(x) [record literal(b) [[literal(f1) ident(y)]]]
                                     [bind ident(z) literal(42)]
                                     [bind ident(z) literal(0)]
                                 ]
                             ]
                         ]
                    ]
		 ]}
*/

 /*    {Interpret  [var ident(x)
                     [[var ident(y)
                         [[var ident(z)
                             [
                                 [bind ident(x) [record literal(a) [
                                     [literal(f1) ident(y)]
                                     [literal(f2) [record literal(b) [
                                         [literal(f3) ident(z)]
                                     ]]]
                                 ]]]
                                 [match ident(x) [record literal(b) [[literal(f1) ident(y)]]]
                                     [bind ident(z) literal(42)]
                                     [bind ident(z) literal(0)]
                                 ]
                             ]
			  ]
			 ]
		       ]
                     ]
                 ]}
*/
 /*    {Interpret  [var ident(x)
                     [[var ident(y)
                         [[var ident(z)
                             [
                                 [bind ident(y)  [record literal(b) [
                                         [literal(f3) literal(100)] ]]]
                                 [bind ident(x) [record literal(a) [
                                     [literal(f1) ident(y)]]]]
     
                                 [match ident(x) [record literal(a) [
                                                    [literal(f1) ident(m)]]
                                                 ] 
                                     [bind ident(z) literal(42)]
                                     [bind ident(z) literal(0)]]
                                 ]
                             ]
                         ]
                     ]]]
       }
*/
/*    {Interpret  [var ident(x) 
                     [ 
                      [var ident(x)  [[nop]]]
			
                         [bind ident(x) literal(100)]
                          ]
			 
		    ]
                    
                 }

*/

/*
{Interpret [
	    [var ident(x)
			 [['thread' [bind ident(x) literal(100)] 'end']]
	    ]
	    
	    [var ident(y) [bind ident(y) literal(200)]]
	    [var ident(z) [bind ident(z) literal(200)]]
	    [var ident(w) [bind ident(w) literal(200)]]

	   ] 
}
*/
  /* {Interpret [
	    [var ident(x)
	     [
	      ['thread' [
			 [bind ident(x) literal(100)]
			 [var ident(a) [bind ident(a) literal(300)]]

			] 'end']
	     ]
	    ]
	    
	    [var ident(y) [bind ident(y) literal(200)]]
	    [var ident(z) [bind ident(z) literal(200)]]
	    [var ident(w) [bind ident(w) literal(200)]]

	   ] 
}

*/
/*

{Interpret  [var ident(x)
                     [var ident(y)
                         [var ident(z)
                             [
                                 ['thread' [bind ident(z) literal(100)] 'end']
                                 ['thread' [bind ident(y) literal(200)] 'end']
			      ['thread' [bind ident(x) literal(300)] 'end']
			      ]]]]}
							     

		*/				
/*
{Interpret  [var ident(x)
                     [var ident(y)
                         [var ident(z)
                             [
                                 ['thread' [bind ident(z) literal(100)] 'end']
                                 ['thread' [apply ident(x) ident(z)] 'end']
                                 ['thread' [bind ident(x)  ['proc' [ident(p1)]
                                                     
                                                  
                                                         [var ident(u)
                                                             [bind ident(u) ident(p1)]
                                                         ]
						     ]] 'end']
			      ]]]]}
				
*/
/*
{Interpret  [
	     ['thread' [var ident(z) [bind ident(z) literal(100)]] 'end']
	     ['thread' [var ident(y) [bind ident(y) literal(200)]] 'end']
	     ['thread' [var ident(x) [bind ident(x) literal(300)]] 'end']
	    ]
}

*/

/*
{Interpret  [var ident(x)
                   [ var ident(y)
                         [var ident(z)
                             [   ['thread' [[conditional ident(z)
                                              [ [bind ident(y) literal(42)]]
                                              [ [bind ident(y) literal(0)]]
                                           ]]
                                   'end']
                                 ['thread' [bind ident(z) literal('true')] 'end']  
			      
			     ]
			  
			 ]
		
		     ]
            ]	     

}
*/


