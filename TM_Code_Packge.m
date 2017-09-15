(* ::Package:: *)

(* ::Input:: *)
(*(*Exploring Halting Times for Non-Conventional Halting Schemes*)
(**)
(*This is the code used in context of the paper of the above title. *)*)


(* ::Input:: *)
(*(*  2.1*)
(*	The following functions describe whether and when a 2,2 TM will halt.*)
(**)*)
TM[n_,x_]:=TuringMachine[n,{1,{{},0}},x]              (* A simpler, more convenient way to write the TuringMachine function. *)*)
HEADS2=Permutations[Flatten[Table[{i,j},{i,1,2},{j,0,1}],1]];            (* Creates all possible sets of head states *)*)
pCELLS2=Permutations[Flatten[Table[{i,j,k},{i,1,2},{j,0,1},{k,{-1,1}}],2],{3}];           (* Creates all possible cell states *)*)
RuleMaker2[x_]:=Table[Join[Thread[Rule[Rest[x],pCELLS2[[m]]]],{First[x]->{0,3,0}}],{m,1,Length[pCELLS2]}]            (*Creates all machine rules from a given value of HEADS2*)*)
Halting2=Flatten[Table[Select[RuleMaker2[n],!FreeQ[TM[#,8],{0,_,_}]&],{n,HEADS2}],1];            (* Lists all sets of rules that eventually halt*)*)
NonHalting2 = Flatten[Table[Select[RuleMaker2[n],FreeQ[TM[#,8],{0,_,_}]&],{n, HEADS2}],1];     (* Lists all sets of rules that do not halt*)*)
N[Length[Halting2]/(Plus[Length[Halting2], Length[NonHalting]])] (* Gives approximate halting probability*)*)


(* ::Input:: *)
(*(* 2.2*)
(*	The halting probabilities of 3,2 Turing machines (TMs) could be caluculated in a similar manner, in theory,
but it is computationally unreasonable. A potential set of functions for 3,2 TMs is included for completion.*)
(**)
(*HEADS3=Permutations[Flatten[Table[{i,j},{i,1,3},{j,0,1}],1]];*)
(*pCELLS3=Permutations[Flatten[Table[{i,j,k},{i,1,3},{j,0,1},{k,{-1,1}}],2],{5}];*)
(*RuleMaker3[x_]:=Table[Join[Thread[Rule[Rest[x],pCELLS3[[m]]]],{First[x]\[Rule]{0,3,0}}],{m,1,Length[pCELLS3]}]*)
(*Halting3 = Flatten[Table[Select[RuleMaker3[n],!FreeQ[TM[#,26],{0,_,_}]&],{n,HEADS3}],1];  *)
(* NonHalting3 = Flatten[Table[Select[RuleMaker3[n],FreeQ[TM[#,26],{0,_,_}]&],{n, HEADS3}],1];     *)
(*N[Length[Halting3]/(Plus[Length[Halting3], Length[NonHalting3]])]  *)
(**)
(*Instead, the below functions can be used to randomly select 3,2 TMs, using some of the variables defined above.   *)
(**)*)
RandomHalting3 := Select[{RandomChoice[RuleMaker3[RandomChoice[HEADS3]]]},!FreeQ[TM[#,26],{0,_,_}]&]*)
Count[Table[RandomHalting3,1000],{}]*)


(* ::Input:: *)
(*(* 2.3*)
(*	However, even randomly selecting halting 4,2 TMs is unfeasible, as it is too likely that only nonhalting machnines 
will be selected. Code included regardless.*)
(**)*)
HEADS4=Permutations[Flatten[Table[{i,j},{i,1,4},{j,0,1}],1]];*)
pCELLS4=Permutations[Flatten[Table[{i,j,k},{i,1,4},{j,0,1},{k,{-1,1}}],2],{7}];*)
RuleMaker4[x_]:=Table[Join[Thread[Rule[Rest[x],pCELLS4[[m]]]],{First[x]->{0,3,0}}],{m,1,Length[pCELLS4]}]*)
RandomHalting4 := Select[{RandomChoice[RuleMaker4[RandomChoice[HEADS4]]]},!FreeQ[TM[#,107],{0,_,_}]&]*)
Count[{Table[RandomHalting4,1000]},{}]*)


(* ::Input:: *)
(*(* 2.4*)
(*	Halting 2,3 TMs can be randomly selected with relative ease.*)
(**)*)
HEADS23=Permutations[Flatten[Table[{i,j},{i,1,2},{j,0,2}],1]];*)
pCELLS23=Permutations[Flatten[Table[{i,j,k},{i,1,2},{j,0,2},{k,{-1,1}}],2],{5}];*)
RuleMaker23[x_]:=Table[Join[Thread[Rule[Rest[x],pCELLS23[[m]]]],{First[x]->{0,3,0}}],{m,1,Length[pCELLS23]}]*)
RandomHalting23 := Select[{RandomChoice[RuleMaker23[RandomChoice[HEADS23]]]},!FreeQ[TM[#,38],{0,_,_}]&]*)
Count[Table[RandomHalting23,1000],{}]*)


(* ::Input:: *)
(*(* 3.2*)
(*	Code for determining halting probability per the second definition of halting in this paper. The 
-1 in the HaltWhen function accounts for the fact that some TMs may "halt" from their initial position:
they never changed from their initial state,and halt at step zero. Here n should represent the same n used 
in RepeatingTM,as it might not necessarily work if a smaller value is chosen. Although this function will produce 
a result for a non-halting function,it should not be used for that purpose.
ProbabilityTM was used to create Table 1.*)
(**)*)
RepeatingTM[rule_,n_]:=If[Apply[SameQ,Last/@Part[#,{n-1,n,n+1,n+2,2 n}]&@TM[#,2 n]&@rule],{rule,"Halts"},{rule,"Doesn't Halt"}] *)
(*(*Takes a rule and the number of steps the rule should run and returns whether a given rule halts or not*)*)
HaltWhen[rule_,n_] := First@First@Position[TM[rule,2 n],Last@Part[TM[rule,2 n],2 n]]-1*)
(*(* Shows at what step a function halts.*) *)
ProbabilityTM[s_,k_] := N[Mean[#]/1000]&@Table[Length[Select[Table[RepeatingTM[{RandomInteger[(2 s k)^(s k)-1],s,k},100],1000], !FreeQ[#,{_,"Halts"}]&]],20] (* s represents the total possible head states, k the total possible cell states. For example, a 3,2 TM has s = 3 and k = 2. *)*)


(* ::Input:: *)
(*(* 3.3*)
(*	Evaluating specifically 2,2 TMs. All 4096 were observed to be either halting or nonhalting using RepeatingBoolean.*)
(**)*)
RepeatingBoolean[rule_,n_]:=Apply[SameQ,Last/@Part[#,{n-1,n,n+1,n+2,2 n}]&@TM[#,2 n]&@rule]         (* Returns TRUE if a machine halts and FALSE if it doesn't *)*)
HaltStep22 = KeySort[Counts[Table[If[RepeatingBoolean[x, 100],HaltWhen[x, 100]],{x,0,4095}]] ]*)
Thread[Rule[Keys[Drop[HaltStep22,-1]],Table[N[100 x/Plus@@Values[Drop[HaltStep22,-1]]]"%",{x,Values[Drop[HaltStep22,-1]]}]]]*)


(* ::Input:: *)
(*(* 3.4*)
(*	To evaluate the halting times of the entire range of TMs in the scope of this study, the following function was used. 
The values from ALLHALTING were used in both Tables 2 and 3 for the most common halting times and for the maximum halting times, 
respectively.*)
(**)*)
ALLHALTING = Table[KeySort[Counts[Table[If[RepeatingBoolean[{SeedRandom[i];RandomInteger[(2 k j)^(k j)-1],k,j}, 100],HaltWhen[{SeedRandom[i];RandomInteger[(2 k j)^(k j)-1],k,j}, 100], "NONHALTING"],{i,100000}]]],{k,2,6},{j,2,6}];*)
