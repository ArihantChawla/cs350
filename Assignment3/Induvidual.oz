%%-----------Question 2.3-----------%%

declare

fun{WaitBoth X1 X2}
   {Wait X1}a
   {Wait X2}
   unit
end

declare A B C

thread {Delay 10000} A = 2 {Browse 'A bounded'} end

thread {Delay 100} B = 3 {Browse 'B bounded'} end

{Browse A}
{Browse B}

C = {WaitBoth A B}

{Browse 'Both bounded'}

%%---------Question 2.4------------%%

declare
fun {TriggerMerge Xs Ys Val}
   local Z Trigger in
      
      {List.merge Xs Ys Val Z}

      fun {Trigger Zs}
	 
      case Zs
      of nil then nil
      [] Z|Zr then (fun {$} Z end)|{Trigger Zr}
      end
      end
      
      {Trigger Z}
   end
end

declare 

Ans = {TriggerMerge [0 2 4] [1 3 5] Value.'<'}
{Browse {{List.nth Ans 6}}}

declare A B C X Y Z
%%---------Question 3.1------------%%

thread X  = 5 end
thread Y = {IsDet X} end
thread Z = {IsDet X} end

{Browse Y}
{Browse Z}

%%---------Question 3.1------------%%

thread B = {IsDet A} end
thread A  = 5 end
thread C  = {IsDet A} end



{Browse B}
{Browse C}

%%---------Question 3.2 and 3.3------------%%

declare

fun {NewPortObject2 MsgProc}
 Stream in
 thread for Msg in Stream do {MsgProc Msg} end end
 {NewPort Stream}
end

Client  = {NewPortObject2 proc {$ M} {Browse M} end}


%{Send Server "Hello"}
%{Send Server "Hey"}

Server = {NewPortObject2 proc{$ M}
			    local
			       ReverseMsg
			    in
			       {List.reverse M ReverseMsg}
			       {Send Client ReverseMsg}
			    end
			 end
	 }

{Send Server "HI"}
{Browse {List.toString [72 73]}}