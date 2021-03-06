declare
Current = {NewCell nil}
\insert 'SemanticStack.oz'
\insert 'SingleAssignmentStore.oz'
\insert 'Unify.oz'



fun {FindinSAS Value}
       local X in
       X = {List.filter {Dictionary.entries SingleAssignmentStore} fun {$ Y}   Y.2 == Value end}
       X.1.1
      end
     
end

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
	      % {Browse S}
	       {Push sepair(statement:S env:{AddToEnv X @Current.env})}
	       {Execute}
	       
	    [] [bind X Y] then
	       %{Browse 'test'}
	       {Unify X Y @Current.env}
	       %{Browse 'test'}
	       %{Browse @Current.env}
	       %{Browse SingleAssignmentStore.1}
	       %{Browse SingleAssignmentStore.2}
	       local A in
		  A = {Pop}
		  %{Browse A}
		  if A \= nil then
		     {Push sepair(statement:A.statement env:{Adjoin A.env @Current.env })}
		  else
		     {Push sepair(statement:nil env:@Current.env)}
		  end
	       
	       end
	       {Execute}


	    [] conditional|ident(X)| S1|S2|nil then
	          
            case {RetrieveFromSAS @Current.env.X}
		  of  literal('true') then {Push sepair(statement:S1 env: @Current.env)} {Execute}
	          []  literal('false') then {Push sepair(statement:S2 env: @Current.env)} {Execute}	  
		  else {Browse 'Error Condition'}
	       end


            [] [match ident(Z) P1 S1 S2] then
	       
	       
	       local P in P =  {RetrieveFromSAS @Current.env.Z}
		        case P
                        of  record | L | Pairs1 then 
	                case P1
			of record|!L|Pairs2 then
                                if 
				 {List.length Pairs1.1} \=  {List.length Pairs2.1} then {Push sepair(statement:S2 env:@Current.env)} {Execute}

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
			      {Execute}
		                  else
				       local  A  in A = H1.2.1
				
				   case A
				     
				   of ident(B) then
				      
				      local D in D =  sepair(statement:@Current.statement env:{Adjoin @Current.env env(B:{FindinSAS H2.2.1})})
					 
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
			   {Push sepair(statement:S1 env:@Current.env)} {Execute}
			   end %main else end
			else     {Push sepair(statement:S2 env:@Current.env)} {Execute}	
			end
			else     {Push sepair(statement:S2 env:@Current.env)} {Execute}	
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
			      Adjoin
			      env()
			     }}
		     
		     {Push sepair(statement:S env:
						 {Adjoin
						  CE
						  {FoldR
						   {List.zip
						    {Map L fun {$ X} X.1 end }
						    {Map Tail fun {$ X} X.1 end }
						    fun {$ A B} env(A:@Current.env.B) end}
						   Adjoin
						   env()
						  }
						 }
				 )
		     }
		  end
	       else
		  {Browse 'ERROR - NOT A PROC'}
	       end
	       {Execute}


	    [] [sum ident(x) ident(y) ident(z)] then      % z = x + y
	       local
		  X = {RetrieveFromSAS @Current.env.x}.1
		  Y = {RetrieveFromSAS @Current.env.y}.1
		  Sum = X + Y
	       in	  
		{BindValueToKeyInSAS @Current.env.z literal(Sum)}
	       end
	       {Execute}

	    [] [prod ident(x) ident(y) ident(z)] then      % z = x * y
	       local
		  X = {RetrieveFromSAS @Current.env.x}.1
		  Y = {RetrieveFromSAS @Current.env.y}.1
		  Sum = X * Y
	       in	  
		{BindValueToKeyInSAS @Current.env.z literal(Sum)}
	       end
	       {Execute}

	    [] [sq ident(x) ident(y)] then       % y = x*x
	       local
		  X = {RetrieveFromSAS @Current.env.x}.1
		  Sq = X*X
	       in
		  {BindValueToKeyInSAS @Current.env.y literal(Sq)}
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

{Interpret
 [
  var ident(x)
  [[ var ident(y)
     [[ var ident(z)
	[[var ident(a)
	  [[ var ident(b)
	     [
	      [bind ident(x) literal(10)]
	      [sq ident(x) ident(y)]
	      [bind ident(z) literal(20)]
	      [[sq ident(z) ident(a)]]
	      [sum ident(a) ident(y) ident(b)]
	     ]
	   ]]
	 ]]
      ]]
   ]]
  ]
}


/*{Interpret
 [
  var ident(x)
  [[ var ident(y)
     [[ var ident(z)
       [[ var ident(a)
	 [[ var ident(b)
	   [
	    [bind ident(x) literal(1)]
	    [sq ident(x) ident(a)]
	    %[bind ident(y) literal(2)]
	    %[sq ident(y) ident(b)]
	    %[sum ident(a) ident(b) ident(z)]
	   ]
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
	    [[ var ident(z1)
	       [[var ident(z2)
		 [[var ident(z3)
		   [
		    [ bind ident(x)
		      ['proc'
		       [idents(y1) idents(y2) ident(y3)]
		       [var ident(z)
			[
			 [bind ident(y1) literal(20)]
			 [bind ident(y2) ident(y3)]
			 [bind ident(y3) literal(30)]
			 [bind ident(z) ident(y3)]
			]]]
		    ]
		    [apply ident(x) ident(z1) ident(z2) ident(z3)]
		    ]]]]]]]]
}
*/









/*{Interpret  [var ident(x)
	     [[var ident(y)
	       [
		[bind ident(y) literal(20)]
		 [bind ident(x)
		 [record literal(rec)
		  [
		   [literal(a) literal(100)]
		   [literal(b) literal(200)]
		  ]
		 ]
		]
		[match ident(x)
		 [record literal(rec)
		  [
		   [literal(a) ident(w)]
		   [literal(b) ident(z)]
		  ]
		 ]
		 [[bind ident(y) literal(100)]]
		 [[bind ident(y) literal(20)]]]
	       ]]]]
                 }
*/
/*{Interpret
 [var ident(x)
  [[var ident(y)
    [[bind ident(y) literal(20)]
     [bind ident(x) [record literal(rec) [[literal(a) literal(100)]
		                          [literal(b) literal(200)]]]]

     [match ident(x) [record literal(rec)
		      [[literal(a) ident(u)]
		       [literal(b) ident(v)]]]
      
      [[bind ident(y) literal(100)]]

     [[bind ident(y) literal(20)]]]]]]]
                                 
                    
                 }

*/










/*{Interpret
 [var ident(x) [
		[var ident(y) [
			    
			       [conditional ident(x)
				[ [bind ident(y) literal(1)]]
				[ [bind ident(y) literal(2)]]
                             

			       ]
                     ]
	       ] ]]
}*/







/*{Browse "c=200"}
{Interpret
 [var ident(x) [
		 [var ident(y) [
				[var ident(x) [
					       [bind ident(x) literal(200)]
					       [bind ident(y) literal(200)]
					      ]
				]
				[bind ident(y) literal(200)]
			       ]
		 ]
	       ]
 ]
}

{Browse "c=20"}

{Interpret
 [var ident(x) [
		 [var ident(y) [
				[var ident(x) [
					       [bind ident(x) literal(200)]
					       [bind ident(y) literal(200)]
					      ]
				]
				[bind ident(y) literal(20)]
			       ]
		 ]
	       ]
 ]
}

				
*/				
						


/*
{Interpret
 [var ident(x1) [
		 [var ident(x2) [
				 [var ident(x3) [ 
						 [var ident(x) [
								[bind ident(x) [
										[record literal(rec) [
												      [literal(a) ident(x1)]
												      [literal(b) ident(x2)]
												      [literal(c) ident(x3)]
												     ]
										]
									       ]
								]
							       ]
						 ]
						]
				 ]
				]
		 ]
		 ]]
		 
	     }*/


/*{Interpret [var ident(x)
	    [ [var ident(y)
	     [  [var ident(x)
		[bind ident(x) ident(y)]
	       ] 
	     [bind ident(x) ident(y)]
	       ]]]]
 }
{Interpret [var ident(x)
	    [var ident(y)
	     [var ident(x)
	      [var ident(x)
	       [[nop] [nop]
	       ]
	      ]
	     ]
	    ]
	   ]
}*/


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

 /*  {Interpret  [var ident(x)
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



    