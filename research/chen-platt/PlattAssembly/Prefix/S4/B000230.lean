import PlattAssemblyKernel
import PlattCertificates.Count131072.C037360
import PlattCertificates.Count131072.C037361
import PlattCertificates.Count131072.C037362
import PlattCertificates.Count131072.C037363
import PlattCertificates.Count131072.C037364
import PlattCertificates.Count131072.C037365
import PlattCertificates.Count131072.C037366
import PlattCertificates.Count131072.C037367
import PlattCertificates.Count131072.C037368
import PlattCertificates.Count131072.C037369
import PlattCertificates.Count131072.C037370
import PlattCertificates.Count131072.C037371
import PlattCertificates.Count131072.C037372
import PlattCertificates.Count131072.C037373
import PlattCertificates.Count131072.C037374
import PlattCertificates.Count131072.C037375
import PlattCertificates.Count131072.C037376
import PlattCertificates.Count131072.C037377
import PlattCertificates.Count131072.C037378
import PlattCertificates.Count131072.C037379
import PlattCertificates.Count131072.C037380
import PlattCertificates.Count131072.C037381
import PlattCertificates.Count131072.C037382
import PlattCertificates.Count131072.C037383
import PlattCertificates.Count131072.C037384
import PlattCertificates.Count131072.C037385
import PlattCertificates.Count131072.C037386
import PlattCertificates.Count131072.C037387
import PlattCertificates.Count131072.C037388
import PlattCertificates.Count131072.C037389
import PlattCertificates.Count131072.C037390
import PlattCertificates.Count131072.C037391
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000230
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts37360 : List PrefixCut := [⟨64,336562801,336563003⟩]
theorem checked37360 : checkPrefixCuts (2^48) 4900782081 10 Manual.Count131072.C037360.packed 64 cuts37360 = true := by
 decide +kernel
def cuts37361 : List PrefixCut := [⟨6,30439533,30439552⟩,
⟨64,338161874,338162084⟩]
theorem checked37361 : checkPrefixCuts (2^48) 4900913153 10 Manual.Count131072.C037361.packed 64 cuts37361 = true := by
 decide +kernel
def pointBounds37361 : List (Nat × Nat × Nat) := [(4900925440,108007264683043,108007649672686)]
theorem point_links_checked37361 : (cuts37361.take 1).map (fun c => (4900913153-1+2*2^10*c.k,108007234243510+c.lower,108007619233134+c.upper)) = pointBounds37361 := by
 decide +kernel
def cuts37362 : List PrefixCut := [⟨17,90971357,90971410⟩,
⟨64,337176528,337176734⟩]
theorem checked37362 : checkPrefixCuts (2^48) 4901044225 10 Manual.Count131072.C037362.packed 64 cuts37362 = true := by
 decide +kernel
def pointBounds37362 : List (Nat × Nat × Nat) := [(4901079040,108007663376741,108008048366628)]
theorem point_links_checked37362 : (cuts37362.take 1).map (fun c => (4901044225-1+2*2^10*c.k,108007572405384+c.lower,108007957395218+c.upper)) = pointBounds37362 := by
 decide +kernel
def cuts37363 : List PrefixCut := [⟨28,147479587,147479676⟩,
⟨64,334410901,334411104⟩]
theorem checked37363 : checkPrefixCuts (2^48) 4901175297 10 Manual.Count131072.C037363.packed 64 cuts37363 = true := by
 decide +kernel
def pointBounds37363 : List (Nat × Nat × Nat) := [(4901232640,108008057061499,108008442051628)]
theorem point_links_checked37363 : (cuts37363.take 1).map (fun c => (4901175297-1+2*2^10*c.k,108007909581912+c.lower,108008294571952+c.upper)) = pointBounds37363 := by
 decide +kernel
def cuts37364 : List PrefixCut := [⟨39,203065689,203065813⟩,
⟨64,335837633,335837836⟩]
theorem checked37364 : checkPrefixCuts (2^48) 4901306369 10 Manual.Count131072.C037364.packed 64 cuts37364 = true := by
 decide +kernel
def pointBounds37364 : List (Nat × Nat × Nat) := [(4901386240,108008447058502,108008832048869)]
theorem point_links_checked37364 : (cuts37364.take 1).map (fun c => (4901306369-1+2*2^10*c.k,108008243992813+c.lower,108008628983056+c.upper)) = pointBounds37364 := by
 decide +kernel
def cuts37365 : List PrefixCut := [⟨50,268525874,268526040⟩,
⟨64,343810894,343811105⟩]
theorem checked37365 : checkPrefixCuts (2^48) 4901437441 10 Manual.Count131072.C037365.packed 64 cuts37365 = true := by
 decide +kernel
def pointBounds37365 : List (Nat × Nat × Nat) := [(4901539840,108008848356320,108009233346932)]
theorem point_links_checked37365 : (cuts37365.take 1).map (fun c => (4901437441-1+2*2^10*c.k,108008579830446+c.lower,108008964820892+c.upper)) = pointBounds37365 := by
 decide +kernel
def cuts37366 : List PrefixCut := [⟨61,318190475,318190671⟩,
⟨64,333235557,333235762⟩]
theorem checked37366 : checkPrefixCuts (2^48) 4901568513 10 Manual.Count131072.C037366.packed 64 cuts37366 = true := by
 decide +kernel
def pointBounds37366 : List (Nat × Nat × Nat) := [(4901693440,108009241831815,108009626822668)]
theorem point_links_checked37366 : (cuts37366.take 1).map (fun c => (4901568513-1+2*2^10*c.k,108008923641340+c.lower,108009308631997+c.upper)) = pointBounds37366 := by
 decide +kernel
def cuts37367 : List PrefixCut := [⟨64,337648255,337648460⟩]
theorem checked37367 : checkPrefixCuts (2^48) 4901699585 10 Manual.Count131072.C037367.packed 64 cuts37367 = true := by
 decide +kernel
def cuts37368 : List PrefixCut := [⟨8,41344062,41344087⟩,
⟨64,335859134,335859336⟩]
theorem checked37368 : checkPrefixCuts (2^48) 4901830657 10 Manual.Count131072.C037368.packed 64 cuts37368 = true := by
 decide +kernel
def pointBounds37368 : List (Nat × Nat × Nat) := [(4901847040,108009635869214,108010020860306)]
theorem point_links_checked37368 : (cuts37368.take 1).map (fun c => (4901830657-1+2*2^10*c.k,108009594525152+c.lower,108009979516219+c.upper)) = pointBounds37368 := by
 decide +kernel
def cuts37369 : List PrefixCut := [⟨19,102036473,102036535⟩,
⟨64,336539213,336539415⟩]
theorem checked37369 : checkPrefixCuts (2^48) 4901961729 10 Manual.Count131072.C037369.packed 64 cuts37369 = true := by
 decide +kernel
def pointBounds37369 : List (Nat × Nat × Nat) := [(4902000640,108010032420759,108010417412090)]
theorem point_links_checked37369 : (cuts37369.take 1).map (fun c => (4901961729-1+2*2^10*c.k,108009930384286+c.lower,108010315375555+c.upper)) = pointBounds37369 := by
 decide +kernel
def cuts37370 : List PrefixCut := [⟨30,157787335,157787430⟩,
⟨64,337506309,337506511⟩]
theorem checked37370 : checkPrefixCuts (2^48) 4902092801 10 Manual.Count131072.C037370.packed 64 cuts37370 = true := by
 decide +kernel
def pointBounds37370 : List (Nat × Nat × Nat) := [(4902154240,108010424710834,108010809702400)]
theorem point_links_checked37370 : (cuts37370.take 1).map (fun c => (4902092801-1+2*2^10*c.k,108010266923499+c.lower,108010651914970+c.upper)) = pointBounds37370 := by
 decide +kernel
def cuts37371 : List PrefixCut := [⟨41,214109106,214109237⟩,
⟨64,337037914,337038122⟩]
theorem checked37371 : checkPrefixCuts (2^48) 4902223873 10 Manual.Count131072.C037371.packed 64 cuts37371 = true := by
 decide +kernel
def pointBounds37371 : List (Nat × Nat × Nat) := [(4902307840,108010818538914,108011203530718)]
theorem point_links_checked37371 : (cuts37371.take 1).map (fun c => (4902223873-1+2*2^10*c.k,108010604429808+c.lower,108010989421481+c.upper)) = pointBounds37371 := by
 decide +kernel
def cuts37372 : List PrefixCut := [⟨52,271690786,271690952⟩,
⟨64,335765780,335765984⟩]
theorem checked37372 : checkPrefixCuts (2^48) 4902354945 10 Manual.Count131072.C037372.packed 64 cuts37372 = true := by
 decide +kernel
def pointBounds37372 : List (Nat × Nat × Nat) := [(4902461440,108011213158508,108011598150555)]
theorem point_links_checked37372 : (cuts37372.take 1).map (fun c => (4902354945-1+2*2^10*c.k,108010941467722+c.lower,108011326459603+c.upper)) = pointBounds37372 := by
 decide +kernel
def cuts37373 : List PrefixCut := [⟨63,330359996,330360199⟩,
⟨64,335642011,335642217⟩]
theorem checked37373 : checkPrefixCuts (2^48) 4902486017 10 Manual.Count131072.C037373.packed 64 cuts37373 = true := by
 decide +kernel
def pointBounds37373 : List (Nat × Nat × Nat) := [(4902615040,108011607593498,108011992585786)]
theorem point_links_checked37373 : (cuts37373.take 1).map (fun c => (4902486017-1+2*2^10*c.k,108011277233502+c.lower,108011662225587+c.upper)) = pointBounds37373 := by
 decide +kernel
def cuts37374 : List PrefixCut := [⟨64,339938958,339939166⟩]
theorem checked37374 : checkPrefixCuts (2^48) 4902617089 10 Manual.Count131072.C037374.packed 64 cuts37374 = true := by
 decide +kernel
def cuts37375 : List PrefixCut := [⟨10,53392727,53392759⟩,
⟨64,337116776,337116982⟩]
theorem checked37375 : checkPrefixCuts (2^48) 4902748161 10 Manual.Count131072.C037375.packed 64 cuts37375 = true := by
 decide +kernel
def pointBounds37375 : List (Nat × Nat × Nat) := [(4902768640,108012006207198,108012391199729)]
theorem point_links_checked37375 : (cuts37375.take 1).map (fun c => (4902748161-1+2*2^10*c.k,108011952814471+c.lower,108012337806970+c.upper)) = pointBounds37375 := by
 decide +kernel
def cuts37376 : List PrefixCut := [⟨21,107873146,107873209⟩,
⟨64,332687197,332687399⟩]
theorem checked37376 : checkPrefixCuts (2^48) 4902879233 10 Manual.Count131072.C037376.packed 64 cuts37376 = true := by
 decide +kernel
def pointBounds37376 : List (Nat × Nat × Nat) := [(4902922240,108012397804393,108012782797161)]
theorem point_links_checked37376 : (cuts37376.take 1).map (fun c => (4902879233-1+2*2^10*c.k,108012289931247+c.lower,108012674923952+c.upper)) = pointBounds37376 := by
 decide +kernel
def cuts37377 : List PrefixCut := [⟨32,168493098,168493205⟩,
⟨64,338706129,338706339⟩]
theorem checked37377 : checkPrefixCuts (2^48) 4903010305 10 Manual.Count131072.C037377.packed 64 cuts37377 = true := by
 decide +kernel
def pointBounds37377 : List (Nat × Nat × Nat) := [(4903075840,108012791111542,108013176104556)]
theorem point_links_checked37377 : (cuts37377.take 1).map (fun c => (4903010305-1+2*2^10*c.k,108012622618444+c.lower,108013007611351+c.upper)) = pointBounds37377 := by
 decide +kernel
def cuts37378 : List PrefixCut := [⟨43,225033611,225033754⟩,
⟨64,335597122,335597332⟩]
theorem checked37378 : checkPrefixCuts (2^48) 4903141377 10 Manual.Count131072.C037378.packed 64 cuts37378 = true := by
 decide +kernel
def pointBounds37378 : List (Nat × Nat × Nat) := [(4903229440,108013186358184,108013571351444)]
theorem point_links_checked37378 : (cuts37378.take 1).map (fun c => (4903141377-1+2*2^10*c.k,108012961324573+c.lower,108013346317690+c.upper)) = pointBounds37378 := by
 decide +kernel
def cuts37379 : List PrefixCut := [⟨54,288000257,288000436⟩,
⟨64,341902709,341902919⟩]
theorem checked37379 : checkPrefixCuts (2^48) 4903272449 10 Manual.Count131072.C037379.packed 64 cuts37379 = true := by
 decide +kernel
def pointBounds37379 : List (Nat × Nat × Nat) := [(4903383040,108013584921952,108013969915458)]
theorem point_links_checked37379 : (cuts37379.take 1).map (fun c => (4903272449-1+2*2^10*c.k,108013296921695+c.lower,108013681915022+c.upper)) = pointBounds37379 := by
 decide +kernel
def cuts37380 : List PrefixCut := [⟨64,338908573,338908778⟩]
theorem checked37380 : checkPrefixCuts (2^48) 4903403521 10 Manual.Count131072.C037380.packed 64 cuts37380 = true := by
 decide +kernel
def cuts37381 : List PrefixCut := [⟨1,5855049,5855052⟩,
⟨64,333331568,333331770⟩]
theorem checked37381 : checkPrefixCuts (2^48) 4903534593 10 Manual.Count131072.C037381.packed 64 cuts37381 = true := by
 decide +kernel
def pointBounds37381 : List (Nat × Nat × Nat) := [(4903536640,108013983588026,108014368581771)]
theorem point_links_checked37381 : (cuts37381.take 1).map (fun c => (4903534593-1+2*2^10*c.k,108013977732977+c.lower,108014362726719+c.upper)) = pointBounds37381 := by
 decide +kernel
def cuts37382 : List PrefixCut := [⟨12,64059258,64059296⟩,
⟨64,335446478,335446680⟩]
theorem checked37382 : checkPrefixCuts (2^48) 4903665665 10 Manual.Count131072.C037382.packed 64 cuts37382 = true := by
 decide +kernel
def pointBounds37382 : List (Nat × Nat × Nat) := [(4903690240,108014375123803,108014760117785)]
theorem point_links_checked37382 : (cuts37382.take 1).map (fun c => (4903665665-1+2*2^10*c.k,108014311064545+c.lower,108014696058489+c.upper)) = pointBounds37382 := by
 decide +kernel
def cuts37383 : List PrefixCut := [⟨23,119045733,119045806⟩,
⟨64,336470623,336470832⟩]
theorem checked37383 : checkPrefixCuts (2^48) 4903796737 10 Manual.Count131072.C037383.packed 64 cuts37383 = true := by
 decide +kernel
def pointBounds37383 : List (Nat × Nat × Nat) := [(4903843840,108014765556756,108015150550975)]
theorem point_links_checked37383 : (cuts37383.take 1).map (fun c => (4903796737-1+2*2^10*c.k,108014646511023+c.lower,108015031505169+c.upper)) = pointBounds37383 := by
 decide +kernel
def cuts37384 : List PrefixCut := [⟨34,181433312,181433425⟩,
⟨64,338068830,338069039⟩]
theorem checked37384 : checkPrefixCuts (2^48) 4903927809 10 Manual.Count131072.C037384.packed 64 cuts37384 = true := by
 decide +kernel
def pointBounds37384 : List (Nat × Nat × Nat) := [(4903997440,108015164414958,108015549409426)]
theorem point_links_checked37384 : (cuts37384.take 1).map (fun c => (4903927809-1+2*2^10*c.k,108014982981646+c.lower,108015367976001+c.upper)) = pointBounds37384 := by
 decide +kernel
def cuts37385 : List PrefixCut := [⟨45,238651635,238651778⟩,
⟨64,337600625,337600828⟩]
theorem checked37385 : checkPrefixCuts (2^48) 4904058881 10 Manual.Count131072.C037385.packed 64 cuts37385 = true := by
 decide +kernel
def pointBounds37385 : List (Nat × Nat × Nat) := [(4904151040,108015559702111,108015944696818)]
theorem point_links_checked37385 : (cuts37385.take 1).map (fun c => (4904058881-1+2*2^10*c.k,108015321050476+c.lower,108015706045040+c.upper)) = pointBounds37385 := by
 decide +kernel
def cuts37386 : List PrefixCut := [⟨56,294776154,294776334⟩,
⟨64,339141204,339141410⟩]
theorem checked37386 : checkPrefixCuts (2^48) 4904189953 10 Manual.Count131072.C037386.packed 64 cuts37386 = true := by
 decide +kernel
def pointBounds37386 : List (Nat × Nat × Nat) := [(4904304640,108015953427255,108016338422202)]
theorem point_links_checked37386 : (cuts37386.take 1).map (fun c => (4904189953-1+2*2^10*c.k,108015658651101+c.lower,108016043645868+c.upper)) = pointBounds37386 := by
 decide +kernel
def cuts37387 : List PrefixCut := [⟨64,339533883,339534085⟩]
theorem checked37387 : checkPrefixCuts (2^48) 4904321025 10 Manual.Count131072.C037387.packed 64 cuts37387 = true := by
 decide +kernel
def cuts37388 : List PrefixCut := [⟨3,15323577,15323586⟩,
⟨64,336138719,336138922⟩]
theorem checked37388 : checkPrefixCuts (2^48) 4904452097 10 Manual.Count131072.C037388.packed 64 cuts37388 = true := by
 decide +kernel
def pointBounds37388 : List (Nat × Nat × Nat) := [(4904458240,108016352649765,108016737644949)]
theorem point_links_checked37388 : (cuts37388.take 1).map (fun c => (4904452097-1+2*2^10*c.k,108016337326188+c.lower,108016722321363+c.upper)) = pointBounds37388 := by
 decide +kernel
def cuts37389 : List PrefixCut := [⟨14,73803550,73803593⟩,
⟨64,336072369,336072574⟩]
theorem checked37389 : checkPrefixCuts (2^48) 4904583169 10 Manual.Count131072.C037389.packed 64 cuts37389 = true := by
 decide +kernel
def pointBounds37389 : List (Nat × Nat × Nat) := [(4904611840,108016747268457,108017132263878)]
theorem point_links_checked37389 : (cuts37389.take 1).map (fun c => (4904583169-1+2*2^10*c.k,108016673464907+c.lower,108017058460285+c.upper)) = pointBounds37389 := by
 decide +kernel
def cuts37390 : List PrefixCut := [⟨25,132394913,132394993⟩,
⟨64,336752077,336752283⟩]
theorem checked37390 : checkPrefixCuts (2^48) 4904714241 10 Manual.Count131072.C037390.packed 64 cuts37390 = true := by
 decide +kernel
def pointBounds37390 : List (Nat × Nat × Nat) := [(4904765440,108017141932189,108017526927852)]
theorem point_links_checked37390 : (cuts37390.take 1).map (fun c => (4904714241-1+2*2^10*c.k,108017009537276+c.lower,108017394532859+c.upper)) = pointBounds37390 := by
 decide +kernel
def cuts37391 : List PrefixCut := [⟨36,189720362,189720478⟩,
⟨64,333644220,333644421⟩]
theorem checked37391 : checkPrefixCuts (2^48) 4904845313 10 Manual.Count131072.C037391.packed 64 cuts37391 = true := by
 decide +kernel
def pointBounds37391 : List (Nat × Nat × Nat) := [(4904919040,108017536009715,108017921005620)]
theorem point_links_checked37391 : (cuts37391.take 1).map (fun c => (4904845313-1+2*2^10*c.k,108017346289353+c.lower,108017731285142+c.upper)) = pointBounds37391 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000230
