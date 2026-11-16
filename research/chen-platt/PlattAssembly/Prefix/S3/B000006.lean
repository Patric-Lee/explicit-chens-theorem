import PlattAssemblyKernel
import PlattCertificates.Count131072.C020192
import PlattCertificates.Count131072.C020193
import PlattCertificates.Count131072.C020194
import PlattCertificates.Count131072.C020195
import PlattCertificates.Count131072.C020196
import PlattCertificates.Count131072.C020197
import PlattCertificates.Count131072.C020198
import PlattCertificates.Count131072.C020199
import PlattCertificates.Count131072.C020200
import PlattCertificates.Count131072.C020201
import PlattCertificates.Count131072.C020202
import PlattCertificates.Count131072.C020203
import PlattCertificates.Count131072.C020204
import PlattCertificates.Count131072.C020205
import PlattCertificates.Count131072.C020206
import PlattCertificates.Count131072.C020207
import PlattCertificates.Count131072.C020208
import PlattCertificates.Count131072.C020209
import PlattCertificates.Count131072.C020210
import PlattCertificates.Count131072.C020211
import PlattCertificates.Count131072.C020212
import PlattCertificates.Count131072.C020213
import PlattCertificates.Count131072.C020214
import PlattCertificates.Count131072.C020215
import PlattCertificates.Count131072.C020216
import PlattCertificates.Count131072.C020217
import PlattCertificates.Count131072.C020218
import PlattCertificates.Count131072.C020219
import PlattCertificates.Count131072.C020220
import PlattCertificates.Count131072.C020221
import PlattCertificates.Count131072.C020222
import PlattCertificates.Count131072.C020223
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000006
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts20192 : List PrefixCut := [⟨60,296387891,296388072⟩,
⟨128,635988394,635988777⟩]
theorem checked20192 : checkPrefixCuts (2^48) 2650537985 9 Manual.Count131072.C020192.packed 128 cuts20192 = true := by
 decide +kernel
def pointBounds20192 : List (Nat × Nat × Nat) := [(2650599424,100144896332010,100145276774554)]
theorem point_links_checked20192 : (cuts20192.take 1).map (fun c => (2650537985-1+2*2^9*c.k,100144599944119+c.lower,100144980386482+c.upper)) = pointBounds20192 := by
 decide +kernel
def cuts20193 : List PrefixCut := [⟨13,69023414,69023455⟩,
⟨94,479227414,479227694⟩,
⟨128,645938775,645939155⟩]
theorem checked20193 : checkPrefixCuts (2^48) 2650669057 9 Manual.Count131072.C020193.packed 128 cuts20193 = true := by
 decide +kernel
def pointBounds20193 : List (Nat × Nat × Nat) := [(2650682368,100145304955927,100145685398714),(2650765312,100145715159927,100146095602953)]
theorem point_links_checked20193 : (cuts20193.take 2).map (fun c => (2650669057-1+2*2^9*c.k,100145235932513+c.lower,100145616375259+c.upper)) = pointBounds20193 := by
 decide +kernel
def cuts20194 : List PrefixCut := [⟨47,235834488,235834628⟩,
⟨128,643464475,643464859⟩]
theorem checked20194 : checkPrefixCuts (2^48) 2650800129 9 Manual.Count131072.C020194.packed 128 cuts20194 = true := by
 decide +kernel
def pointBounds20194 : List (Nat × Nat × Nat) := [(2650848256,100146117705776,100146498149042),(2650931200,100146525335763,100146905779273)]
theorem point_links_checked20194 : (cuts20194.take 2).map (fun c => (2650800129-1+2*2^9*c.k,100145881871288+c.lower,100146262314414+c.upper)) = pointBounds20194 := by
 decide +kernel
def cuts20195 : List PrefixCut := [⟨81,402095989,402096219⟩,
⟨128,638017638,638018001⟩]
theorem checked20195 : checkPrefixCuts (2^48) 2650931201 9 Manual.Count131072.C020195.packed 128 cuts20195 = true := by
 decide +kernel
def pointBounds20195 : List (Nat × Nat × Nat) := [(2651014144,100146927431752,100147307875492)]
theorem point_links_checked20195 : (cuts20195.take 1).map (fun c => (2650931201-1+2*2^9*c.k,100146525335763+c.lower,100146905779273+c.upper)) = pointBounds20195 := by
 decide +kernel
def cuts20196 : List PrefixCut := [⟨34,174655715,174655816⟩,
⟨115,575240102,575240437⟩,
⟨128,637773879,637774250⟩]
theorem checked20196 : checkPrefixCuts (2^48) 2651062273 9 Manual.Count131072.C020196.packed 128 cuts20196 = true := by
 decide +kernel
def pointBounds20196 : List (Nat × Nat × Nat) := [(2651097088,100147338009116,100147718453090),(2651180032,100147738593503,100148119037711)]
theorem point_links_checked20196 : (cuts20196.take 2).map (fun c => (2651062273-1+2*2^9*c.k,100147163353401+c.lower,100147543797274+c.upper)) = pointBounds20196 := by
 decide +kernel
def cuts20197 : List PrefixCut := [⟨68,338462811,338463007⟩,
⟨128,632115488,632115855⟩]
theorem checked20197 : checkPrefixCuts (2^48) 2651193345 9 Manual.Count131072.C020197.packed 128 cuts20197 = true := by
 decide +kernel
def pointBounds20197 : List (Nat × Nat × Nat) := [(2651262976,100148139590091,100148520034531)]
theorem point_links_checked20197 : (cuts20197.take 1).map (fun c => (2651193345-1+2*2^9*c.k,100147801127280+c.lower,100148181571524+c.upper)) = pointBounds20197 := by
 decide +kernel
def cuts20198 : List PrefixCut := [⟨21,101279935,101279995⟩,
⟨102,503419241,503419535⟩,
⟨128,635375091,635375463⟩]
theorem checked20198 : checkPrefixCuts (2^48) 2651324417 9 Manual.Count131072.C020198.packed 128 cuts20198 = true := by
 decide +kernel
def pointBounds20198 : List (Nat × Nat × Nat) := [(2651345920,100148534522703,100148914967374),(2651428864,100148936662009,100149317106914)]
theorem point_links_checked20198 : (cuts20198.take 2).map (fun c => (2651324417-1+2*2^9*c.k,100148433242768+c.lower,100148813687379+c.upper)) = pointBounds20198 := by
 decide +kernel
def cuts20199 : List PrefixCut := [⟨55,276646477,276646638⟩,
⟨128,645747028,645747408⟩]
theorem checked20199 : checkPrefixCuts (2^48) 2651455489 9 Manual.Count131072.C020199.packed 128 cuts20199 = true := by
 decide +kernel
def pointBounds20199 : List (Nat × Nat × Nat) := [(2651511808,100149345264336,100149725709480)]
theorem point_links_checked20199 : (cuts20199.take 1).map (fun c => (2651455489-1+2*2^9*c.k,100149068617859+c.lower,100149449062842+c.upper)) = pointBounds20199 := by
 decide +kernel
def cuts20200 : List PrefixCut := [⟨8,40125918,40125941⟩,
⟨89,448384140,448384408⟩,
⟨128,645927329,645927714⟩]
theorem checked20200 : checkPrefixCuts (2^48) 2651586561 9 Manual.Count131072.C020200.packed 128 cuts20200 = true := by
 decide +kernel
def pointBounds20200 : List (Nat × Nat × Nat) := [(2651594752,100149754490805,100150134936191),(2651677696,100150162749027,100150543194658)]
theorem point_links_checked20200 : (cuts20200.take 2).map (fun c => (2651586561-1+2*2^9*c.k,100149714364887+c.lower,100150094810250+c.upper)) = pointBounds20200 := by
 decide +kernel
def cuts20201 : List PrefixCut := [⟨42,206562602,206562722⟩,
⟨123,606197593,606197953⟩,
⟨128,631778056,631778431⟩]
theorem checked20201 : checkPrefixCuts (2^48) 2651717633 9 Manual.Count131072.C020201.packed 128 cuts20201 = true := by
 decide +kernel
def pointBounds20201 : List (Nat × Nat × Nat) := [(2651760640,100150566854818,100150947300686),(2651843584,100150966489809,100151346935917)]
theorem point_links_checked20201 : (cuts20201.take 2).map (fun c => (2651717633-1+2*2^9*c.k,100150360292216+c.lower,100150740737964+c.upper)) = pointBounds20201 := by
 decide +kernel
def cuts20202 : List PrefixCut := [⟨76,382639576,382639799⟩,
⟨128,638752277,638752649⟩]
theorem checked20202 : checkPrefixCuts (2^48) 2651848705 9 Manual.Count131072.C020202.packed 128 cuts20202 = true := by
 decide +kernel
def pointBounds20202 : List (Nat × Nat × Nat) := [(2651926528,100151374709848,100151755156194)]
theorem point_links_checked20202 : (cuts20202.take 1).map (fun c => (2651848705-1+2*2^9*c.k,100150992070272+c.lower,100151372516395+c.upper)) = pointBounds20202 := by
 decide +kernel
def cuts20203 : List PrefixCut := [⟨29,147318256,147318337⟩,
⟨110,549144732,549145053⟩,
⟨128,638083993,638084365⟩]
theorem checked20203 : checkPrefixCuts (2^48) 2651979777 9 Manual.Count131072.C020203.packed 128 cuts20203 = true := by
 decide +kernel
def pointBounds20203 : List (Nat × Nat × Nat) := [(2652009472,100151778140805,100152158587381),(2652092416,100152179967281,100152560414097)]
theorem point_links_checked20203 : (cuts20203.take 2).map (fun c => (2651979777-1+2*2^9*c.k,100151630822549+c.lower,100152011269044+c.upper)) = pointBounds20203 := by
 decide +kernel
def cuts20204 : List PrefixCut := [⟨63,316058438,316058625⟩,
⟨128,639219691,639220069⟩]
theorem checked20204 : checkPrefixCuts (2^48) 2652110849 9 Manual.Count131072.C020204.packed 128 cuts20204 = true := by
 decide +kernel
def pointBounds20204 : List (Nat × Nat × Nat) := [(2652175360,100152584964980,100152965412034)]
theorem point_links_checked20204 : (cuts20204.take 1).map (fun c => (2652110849-1+2*2^9*c.k,100152268906542+c.lower,100152649353409+c.upper)) = pointBounds20204 := by
 decide +kernel
def cuts20205 : List PrefixCut := [⟨16,79276744,79276793⟩,
⟨97,485628788,485629077⟩,
⟨128,642265659,642266036⟩]
theorem checked20205 : checkPrefixCuts (2^48) 2652241921 9 Manual.Count131072.C020205.packed 128 cuts20205 = true := by
 decide +kernel
def pointBounds20205 : List (Nat × Nat × Nat) := [(2652258304,100152987402977,100153367850271),(2652341248,100153393755021,100153774202555)]
theorem point_links_checked20205 : (cuts20205.take 2).map (fun c => (2652241921-1+2*2^9*c.k,100152908126233+c.lower,100153288573478+c.upper)) = pointBounds20205 := by
 decide +kernel
def cuts20206 : List PrefixCut := [⟨50,252355478,252355624⟩,
⟨128,635866915,635867285⟩]
theorem checked20206 : checkPrefixCuts (2^48) 2652372993 9 Manual.Count131072.C020206.packed 128 cuts20206 = true := by
 decide +kernel
def pointBounds20206 : List (Nat × Nat × Nat) := [(2652424192,100153802747370,100154183195138)]
theorem point_links_checked20206 : (cuts20206.take 1).map (fun c => (2652372993-1+2*2^9*c.k,100153550391892+c.lower,100153930839514+c.upper)) = pointBounds20206 := by
 decide +kernel
def cuts20207 : List PrefixCut := [⟨3,14962441,14962450⟩,
⟨84,425945351,425945598⟩,
⟨128,646446763,646447143⟩]
theorem checked20207 : checkPrefixCuts (2^48) 2652504065 9 Manual.Count131072.C020207.packed 128 cuts20207 = true := by
 decide +kernel
def pointBounds20207 : List (Nat × Nat × Nat) := [(2652507136,100154201221248,100154581669249),(2652590080,100154612204158,100154992652397)]
theorem point_links_checked20207 : (cuts20207.take 2).map (fun c => (2652504065-1+2*2^9*c.k,100154186258807+c.lower,100154566706799+c.upper)) = pointBounds20207 := by
 decide +kernel
def cuts20208 : List PrefixCut := [⟨37,184208136,184208245⟩,
⟨118,594104281,594104626⟩,
⟨128,643974285,643974658⟩]
theorem checked20208 : checkPrefixCuts (2^48) 2652635137 9 Manual.Count131072.C020208.packed 128 cuts20208 = true := by
 decide +kernel
def pointBounds20208 : List (Nat × Nat × Nat) := [(2652673024,100155016913706,100155397362187),(2652755968,100155426809851,100155807258568)]
theorem point_links_checked20208 : (cuts20208.take 2).map (fun c => (2652635137-1+2*2^9*c.k,100154832705570+c.lower,100155213153942+c.upper)) = pointBounds20208 := by
 decide +kernel
def cuts20209 : List PrefixCut := [⟨71,349084608,349084812⟩,
⟨128,631740637,631741005⟩]
theorem checked20209 : checkPrefixCuts (2^48) 2652766209 9 Manual.Count131072.C020209.packed 128 cuts20209 = true := by
 decide +kernel
def pointBounds20209 : List (Nat × Nat × Nat) := [(2652838912,100155825764463,100156206213412)]
theorem point_links_checked20209 : (cuts20209.take 1).map (fun c => (2652766209-1+2*2^9*c.k,100155476679855+c.lower,100155857128600+c.upper)) = pointBounds20209 := by
 decide +kernel
def cuts20210 : List PrefixCut := [⟨24,123500915,123500986⟩,
⟨105,531342786,531343089⟩,
⟨128,642743768,642744135⟩]
theorem checked20210 : checkPrefixCuts (2^48) 2652897281 9 Manual.Count131072.C020210.packed 128 cuts20210 = true := by
 decide +kernel
def pointBounds20210 : List (Nat × Nat × Nat) := [(2652921856,100156231921407,100156612370591),(2653004800,100156639763278,100157020212694)]
theorem point_links_checked20210 : (cuts20210.take 2).map (fun c => (2652897281-1+2*2^9*c.k,100156108420492+c.lower,100156488869605+c.upper)) = pointBounds20210 := by
 decide +kernel
def cuts20211 : List PrefixCut := [⟨58,291123331,291123506⟩,
⟨128,641226505,641226882⟩]
theorem checked20211 : checkPrefixCuts (2^48) 2653028353 9 Manual.Count131072.C020211.packed 128 cuts20211 = true := by
 decide +kernel
def pointBounds20211 : List (Nat × Nat × Nat) := [(2653087744,100157042287591,100157422737246)]
theorem point_links_checked20211 : (cuts20211.take 1).map (fun c => (2653028353-1+2*2^9*c.k,100156751164260+c.lower,100157131613740+c.upper)) = pointBounds20211 := by
 decide +kernel
def cuts20212 : List PrefixCut := [⟨11,56758273,56758306⟩,
⟨92,459575706,459575975⟩,
⟨128,641407038,641407416⟩]
theorem checked20212 : checkPrefixCuts (2^48) 2653159425 9 Manual.Count131072.C020212.packed 128 cuts20212 = true := by
 decide +kernel
def pointBounds20212 : List (Nat × Nat × Nat) := [(2653170688,100157449149038,100157829598928),(2653253632,100157851966471,100158232416597)]
theorem point_links_checked20212 : (cuts20212.take 2).map (fun c => (2653159425-1+2*2^9*c.k,100157392390765+c.lower,100157772840622+c.upper)) = pointBounds20212 := by
 decide +kernel
def cuts20213 : List PrefixCut := [⟨45,225323052,225323187⟩,
⟨126,635222799,635223173⟩,
⟨128,644876081,644876460⟩]
theorem checked20213 : checkPrefixCuts (2^48) 2653290497 9 Manual.Count131072.C020213.packed 128 cuts20213 = true := by
 decide +kernel
def pointBounds20213 : List (Nat × Nat × Nat) := [(2653336576,100158259120855,100158639571225),(2653419520,100158669020602,100159049471211)]
theorem point_links_checked20213 : (cuts20213.take 2).map (fun c => (2653290497-1+2*2^9*c.k,100158033797803+c.lower,100158414248038+c.upper)) = pointBounds20213 := by
 decide +kernel
def cuts20214 : List PrefixCut := [⟨79,397687803,397688037⟩,
⟨128,644101731,644102114⟩]
theorem checked20214 : checkPrefixCuts (2^48) 2653421569 9 Manual.Count131072.C020214.packed 128 cuts20214 = true := by
 decide +kernel
def pointBounds20214 : List (Nat × Nat × Nat) := [(2653502464,100159076361687,100159456812535)]
theorem point_links_checked20214 : (cuts20214.take 1).map (fun c => (2653421569-1+2*2^9*c.k,100158678673884+c.lower,100159059124498+c.upper)) = pointBounds20214 := by
 decide +kernel
def cuts20215 : List PrefixCut := [⟨32,158792898,158792992⟩,
⟨113,569821001,569821336⟩,
⟨128,647676243,647676624⟩]
theorem checked20215 : checkPrefixCuts (2^48) 2653552641 9 Manual.Count131072.C020215.packed 128 cuts20215 = true := by
 decide +kernel
def pointBounds20215 : List (Nat × Nat × Nat) := [(2653585408,100159481568513,100159862019604),(2653668352,100159892596616,100160273047948)]
theorem point_links_checked20215 : (cuts20215.take 2).map (fun c => (2653552641-1+2*2^9*c.k,100159322775615+c.lower,100159703226612+c.upper)) = pointBounds20215 := by
 decide +kernel
def cuts20216 : List PrefixCut := [⟨66,325310974,325311170⟩,
⟨128,632582818,632583194⟩]
theorem checked20216 : checkPrefixCuts (2^48) 2653683713 9 Manual.Count131072.C020216.packed 128 cuts20216 = true := by
 decide +kernel
def pointBounds20216 : List (Nat × Nat × Nat) := [(2653751296,100160295762832,100160676214406)]
theorem point_links_checked20216 : (cuts20216.take 1).map (fun c => (2653683713-1+2*2^9*c.k,100159970451858+c.lower,100160350903236+c.upper)) = pointBounds20216 := by
 decide +kernel
def cuts20217 : List PrefixCut := [⟨19,95139293,95139348⟩,
⟨100,498598422,498598713⟩,
⟨128,639127377,639127750⟩]
theorem checked20217 : checkPrefixCuts (2^48) 2653814785 9 Manual.Count131072.C020217.packed 128 cuts20217 = true := by
 decide +kernel
def pointBounds20217 : List (Nat × Nat × Nat) := [(2653834240,100160698173969,100161078625778),(2653917184,100161101633098,100161482085143)]
theorem point_links_checked20217 : (cuts20217.take 2).map (fun c => (2653814785-1+2*2^9*c.k,100160603034676+c.lower,100160983486430+c.upper)) = pointBounds20217 := by
 decide +kernel
def cuts20218 : List PrefixCut := [⟨53,266841796,266841958⟩,
⟨128,640474734,640475115⟩]
theorem checked20218 : checkPrefixCuts (2^48) 2653945857 9 Manual.Count131072.C020218.packed 128 cuts20218 = true := by
 decide +kernel
def pointBounds20218 : List (Nat × Nat × Nat) := [(2654000128,100161509003849,100161889456138)]
theorem point_links_checked20218 : (cuts20218.take 1).map (fun c => (2653945857-1+2*2^9*c.k,100161242162053+c.lower,100161622614180+c.upper)) = pointBounds20218 := by
 decide +kernel
def cuts20219 : List PrefixCut := [⟨6,30967667,30967687⟩,
⟨87,436297951,436298207⟩,
⟨128,645003136,645003514⟩]
theorem checked20219 : checkPrefixCuts (2^48) 2654076929 9 Manual.Count131072.C020219.packed 128 cuts20219 = true := by
 decide +kernel
def pointBounds20219 : List (Nat × Nat × Nat) := [(2654083072,100161913604454,100162294056982),(2654166016,100162318934738,100162699387502)]
theorem point_links_checked20219 : (cuts20219.take 2).map (fun c => (2654076929-1+2*2^9*c.k,100161882636787+c.lower,100162263089295+c.upper)) = pointBounds20219 := by
 decide +kernel
def cuts20220 : List PrefixCut := [⟨40,194491514,194491628⟩,
⟨122,604568370,604568726⟩,
⟨128,636805573,636805947⟩]
theorem checked20220 : checkPrefixCuts (2^48) 2654208001 9 Manual.Count131072.C020220.packed 128 cuts20220 = true := by
 decide +kernel
def pointBounds20220 : List (Nat × Nat × Nat) := [(2654248960,100162722131437,100163102584437),(2654332928,100163132208293,100163512661535)]
theorem point_links_checked20220 : (cuts20220.take 2).map (fun c => (2654208001-1+2*2^9*c.k,100162527639923+c.lower,100162908092809+c.upper)) = pointBounds20220 := by
 decide +kernel
def cuts20221 : List PrefixCut := [⟨76,380901983,380902207⟩,
⟨128,641334060,641334440⟩]
theorem checked20221 : checkPrefixCuts (2^48) 2654339073 9 Manual.Count131072.C020221.packed 128 cuts20221 = true := by
 decide +kernel
def pointBounds20221 : List (Nat × Nat × Nat) := [(2654416896,100163545347479,100163925800963)]
theorem point_links_checked20221 : (cuts20221.take 1).map (fun c => (2654339073-1+2*2^9*c.k,100163164445496+c.lower,100163544898756+c.upper)) = pointBounds20221 := by
 decide +kernel
def cuts20222 : List PrefixCut := [⟨30,151421495,151421582⟩,
⟨112,562625920,562626251⟩,
⟨128,642362859,642363237⟩]
theorem checked20222 : checkPrefixCuts (2^48) 2654470145 9 Manual.Count131072.C020222.packed 128 cuts20222 = true := by
 decide +kernel
def pointBounds20222 : List (Nat × Nat × Nat) := [(2654500864,100163957201051,100164337654778),(2654584832,100164368405476,100164748859447)]
theorem point_links_checked20222 : (cuts20222.take 2).map (fun c => (2654470145-1+2*2^9*c.k,100163805779556+c.lower,100164186233196+c.upper)) = pointBounds20222 := by
 decide +kernel
def cuts20223 : List PrefixCut := [⟨66,331772469,331772668⟩,
⟨128,650813260,650813638⟩]
theorem checked20223 : checkPrefixCuts (2^48) 2654601217 9 Manual.Count131072.C020223.packed 128 cuts20223 = true := by
 decide +kernel
def pointBounds20223 : List (Nat × Nat × Nat) := [(2654668800,100164779914884,100165160369101)]
theorem point_links_checked20223 : (cuts20223.take 1).map (fun c => (2654601217-1+2*2^9*c.k,100164448142415+c.lower,100164828596433+c.upper)) = pointBounds20223 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000006
