import PlattAssemblyKernel
import PlattCertificates.Count131072.C038320
import PlattCertificates.Count131072.C038321
import PlattCertificates.Count131072.C038322
import PlattCertificates.Count131072.C038323
import PlattCertificates.Count131072.C038324
import PlattCertificates.Count131072.C038325
import PlattCertificates.Count131072.C038326
import PlattCertificates.Count131072.C038327
import PlattCertificates.Count131072.C038328
import PlattCertificates.Count131072.C038329
import PlattCertificates.Count131072.C038330
import PlattCertificates.Count131072.C038331
import PlattCertificates.Count131072.C038332
import PlattCertificates.Count131072.C038333
import PlattCertificates.Count131072.C038334
import PlattCertificates.Count131072.C038335
import PlattCertificates.Count131072.C038336
import PlattCertificates.Count131072.C038337
import PlattCertificates.Count131072.C038338
import PlattCertificates.Count131072.C038339
import PlattCertificates.Count131072.C038340
import PlattCertificates.Count131072.C038341
import PlattCertificates.Count131072.C038342
import PlattCertificates.Count131072.C038343
import PlattCertificates.Count131072.C038344
import PlattCertificates.Count131072.C038345
import PlattCertificates.Count131072.C038346
import PlattCertificates.Count131072.C038347
import PlattCertificates.Count131072.C038348
import PlattCertificates.Count131072.C038349
import PlattCertificates.Count131072.C038350
import PlattCertificates.Count131072.C038351
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000260
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts38320 : List PrefixCut := [⟨6,30910278,30910296⟩,
⟨64,333737456,333737655⟩]
theorem checked38320 : checkPrefixCuts (2^48) 5026611201 10 Manual.Count131072.C038320.packed 64 cuts38320 = true := by
 decide +kernel
def pointBounds38320 : List (Nat × Nat × Nat) := [(5026623488,108326563875844,108326949058744)]
theorem point_links_checked38320 : (cuts38320.take 1).map (fun c => (5026611201-1+2*2^10*c.k,108326532965566+c.lower,108326918148448+c.upper)) = pointBounds38320 := by
 decide +kernel
def cuts38321 : List PrefixCut := [⟨19,99671587,99671646⟩,
⟨64,326393492,326393688⟩]
theorem checked38321 : checkPrefixCuts (2^48) 5026742273 10 Manual.Count131072.C038321.packed 64 cuts38321 = true := by
 decide +kernel
def pointBounds38321 : List (Nat × Nat × Nat) := [(5026781184,108326966374609,108327351557749)]
theorem point_links_checked38321 : (cuts38321.take 1).map (fun c => (5026742273-1+2*2^10*c.k,108326866703022+c.lower,108327251886103+c.upper)) = pointBounds38321 := by
 decide +kernel
def cuts38322 : List PrefixCut := [⟨32,164341419,164341520⟩,
⟨64,325489065,325489265⟩]
theorem checked38322 : checkPrefixCuts (2^48) 5026873345 10 Manual.Count131072.C038322.packed 64 cuts38322 = true := by
 decide +kernel
def pointBounds38322 : List (Nat × Nat × Nat) := [(5026938880,108327357437933,108327742621311)]
theorem point_links_checked38322 : (cuts38322.take 1).map (fun c => (5026873345-1+2*2^10*c.k,108327193096514+c.lower,108327578279791+c.upper)) = pointBounds38322 := by
 decide +kernel
def cuts38323 : List PrefixCut := [⟨45,227551727,227551864⟩,
⟨64,323688827,323689020⟩]
theorem checked38323 : checkPrefixCuts (2^48) 5027004417 10 Manual.Count131072.C038323.packed 64 cuts38323 = true := by
 decide +kernel
def pointBounds38323 : List (Nat × Nat × Nat) := [(5027096576,108327746137306,108328131320920)]
theorem point_links_checked38323 : (cuts38323.take 1).map (fun c => (5027004417-1+2*2^10*c.k,108327518585579+c.lower,108327903769056+c.upper)) = pointBounds38323 := by
 decide +kernel
def cuts38324 : List PrefixCut := [⟨58,300948650,300948831⟩,
⟨64,333478677,333478877⟩]
theorem checked38324 : checkPrefixCuts (2^48) 5027135489 10 Manual.Count131072.C038324.packed 64 cuts38324 = true := by
 decide +kernel
def pointBounds38324 : List (Nat × Nat × Nat) := [(5027254272,108328143223056,108328528406907)]
theorem point_links_checked38324 : (cuts38324.take 1).map (fun c => (5027135489-1+2*2^10*c.k,108327842274406+c.lower,108328227458076+c.upper)) = pointBounds38324 := by
 decide +kernel
def cuts38325 : List PrefixCut := [⟨64,326975268,326975466⟩]
theorem checked38325 : checkPrefixCuts (2^48) 5027266561 10 Manual.Count131072.C038325.packed 64 cuts38325 = true := by
 decide +kernel
def cuts38326 : List PrefixCut := [⟨7,36616223,36616245⟩,
⟨64,328814376,328814578⟩]
theorem checked38326 : checkPrefixCuts (2^48) 5027397633 10 Manual.Count131072.C038326.packed 64 cuts38326 = true := by
 decide +kernel
def pointBounds38326 : List (Nat × Nat × Nat) := [(5027411968,108328539344574,108328924528664)]
theorem point_links_checked38326 : (cuts38326.take 1).map (fun c => (5027397633-1+2*2^10*c.k,108328502728351+c.lower,108328887912419+c.upper)) = pointBounds38326 := by
 decide +kernel
def cuts38327 : List PrefixCut := [⟨20,103351081,103351145⟩,
⟨64,325726543,325726738⟩]
theorem checked38327 : checkPrefixCuts (2^48) 5027528705 10 Manual.Count131072.C038327.packed 64 cuts38327 = true := by
 decide +kernel
def pointBounds38327 : List (Nat × Nat × Nat) := [(5027569664,108328934893808,108329320078142)]
theorem point_links_checked38327 : (cuts38327.take 1).map (fun c => (5027528705-1+2*2^10*c.k,108328831542727+c.lower,108329216726997+c.upper)) = pointBounds38327 := by
 decide +kernel
def cuts38328 : List PrefixCut := [⟨33,169858157,169858260⟩,
⟨64,329301054,329301255⟩]
theorem checked38328 : checkPrefixCuts (2^48) 5027659777 10 Manual.Count131072.C038328.packed 64 cuts38328 = true := by
 decide +kernel
def pointBounds38328 : List (Nat × Nat × Nat) := [(5027727360,108329327127427,108329712311995)]
theorem point_links_checked38328 : (cuts38328.take 1).map (fun c => (5027659777-1+2*2^10*c.k,108329157269270+c.lower,108329542453735+c.upper)) = pointBounds38328 := by
 decide +kernel
def cuts38329 : List PrefixCut := [⟨46,235017800,235017943⟩,
⟨64,325877488,325877688⟩]
theorem checked38329 : checkPrefixCuts (2^48) 5027790849 10 Manual.Count131072.C038329.packed 64 cuts38329 = true := by
 decide +kernel
def pointBounds38329 : List (Nat × Nat × Nat) := [(5027885056,108329721588124,108330106772933)]
theorem point_links_checked38329 : (cuts38329.take 1).map (fun c => (5027790849-1+2*2^10*c.k,108329486570324+c.lower,108329871754990+c.upper)) = pointBounds38329 := by
 decide +kernel
def cuts38330 : List PrefixCut := [⟨59,304428401,304428585⟩,
⟨64,332082989,332083190⟩]
theorem checked38330 : checkPrefixCuts (2^48) 5027921921 10 Manual.Count131072.C038330.packed 64 cuts38330 = true := by
 decide +kernel
def pointBounds38330 : List (Nat × Nat × Nat) := [(5028042752,108330116876213,108330502061263)]
theorem point_links_checked38330 : (cuts38330.take 1).map (fun c => (5027921921-1+2*2^10*c.k,108329812447812+c.lower,108330197632678+c.upper)) = pointBounds38330 := by
 decide +kernel
def cuts38331 : List PrefixCut := [⟨64,327483957,327484153⟩]
theorem checked38331 : checkPrefixCuts (2^48) 5028052993 10 Manual.Count131072.C038331.packed 64 cuts38331 = true := by
 decide +kernel
def cuts38332 : List PrefixCut := [⟨8,40641001,40641026⟩,
⟨64,327531376,327531573⟩]
theorem checked38332 : checkPrefixCuts (2^48) 5028184065 10 Manual.Count131072.C038332.packed 64 cuts38332 = true := by
 decide +kernel
def pointBounds38332 : List (Nat × Nat × Nat) := [(5028200448,108330512655759,108330897841047)]
theorem point_links_checked38332 : (cuts38332.take 1).map (fun c => (5028184065-1+2*2^10*c.k,108330472014758+c.lower,108330857200021+c.upper)) = pointBounds38332 := by
 decide +kernel
def cuts38333 : List PrefixCut := [⟨21,109100599,109100661⟩,
⟨64,327914701,327914895⟩]
theorem checked38333 : checkPrefixCuts (2^48) 5028315137 10 Manual.Count131072.C038333.packed 64 cuts38333 = true := by
 decide +kernel
def pointBounds38333 : List (Nat × Nat × Nat) := [(5028358144,108330908646733,108331293832255)]
theorem point_links_checked38333 : (cuts38333.take 1).map (fun c => (5028315137-1+2*2^10*c.k,108330799546134+c.lower,108331184731594+c.upper)) = pointBounds38333 := by
 decide +kernel
def cuts38334 : List PrefixCut := [⟨34,174589529,174589635⟩,
⟨64,327234440,327234638⟩]
theorem checked38334 : checkPrefixCuts (2^48) 5028446209 10 Manual.Count131072.C038334.packed 64 cuts38334 = true := by
 decide +kernel
def pointBounds38334 : List (Nat × Nat × Nat) := [(5028515840,108331302050364,108331687236124)]
theorem point_links_checked38334 : (cuts38334.take 1).map (fun c => (5028446209-1+2*2^10*c.k,108331127460835+c.lower,108331512646489+c.upper)) = pointBounds38334 := by
 decide +kernel
def cuts38335 : List PrefixCut := [⟨47,241026306,241026447⟩,
⟨64,328625287,328625480⟩]
theorem checked38335 : checkPrefixCuts (2^48) 5028577281 10 Manual.Count131072.C038335.packed 64 cuts38335 = true := by
 decide +kernel
def pointBounds38335 : List (Nat × Nat × Nat) := [(5028673536,108331695721581,108332080907574)]
theorem point_links_checked38335 : (cuts38335.take 1).map (fun c => (5028577281-1+2*2^10*c.k,108331454695275+c.lower,108331839881127+c.upper)) = pointBounds38335 := by
 decide +kernel
def cuts38336 : List PrefixCut := [⟨60,307459226,307459414⟩,
⟨64,327273378,327273579⟩]
theorem checked38336 : checkPrefixCuts (2^48) 5028708353 10 Manual.Count131072.C038336.packed 64 cuts38336 = true := by
 decide +kernel
def pointBounds38336 : List (Nat × Nat × Nat) := [(5028831232,108332090779788,108332475966021)]
theorem point_links_checked38336 : (cuts38336.take 1).map (fun c => (5028708353-1+2*2^10*c.k,108331783320562+c.lower,108332168506607+c.upper)) = pointBounds38336 := by
 decide +kernel
def cuts38337 : List PrefixCut := [⟨64,328272308,328272510⟩]
theorem checked38337 : checkPrefixCuts (2^48) 5028839425 10 Manual.Count131072.C038337.packed 64 cuts38337 = true := by
 decide +kernel
def cuts38338 : List PrefixCut := [⟨9,44216755,44216781⟩,
⟨64,327088378,327088575⟩]
theorem checked38338 : checkPrefixCuts (2^48) 5028970497 10 Manual.Count131072.C038338.packed 64 cuts38338 = true := by
 decide +kernel
def pointBounds38338 : List (Nat × Nat × Nat) := [(5028988928,108332483083003,108332868269477)]
theorem point_links_checked38338 : (cuts38338.take 1).map (fun c => (5028970497-1+2*2^10*c.k,108332438866248+c.lower,108332824052696+c.upper)) = pointBounds38338 := by
 decide +kernel
def cuts38339 : List PrefixCut := [⟨22,114288638,114288706⟩,
⟨64,332956559,332956752⟩]
theorem checked38339 : checkPrefixCuts (2^48) 5029101569 10 Manual.Count131072.C038339.packed 64 cuts38339 = true := by
 decide +kernel
def pointBounds38339 : List (Nat × Nat × Nat) := [(5029146624,108332880243264,108333265429977)]
theorem point_links_checked38339 : (cuts38339.take 1).map (fun c => (5029101569-1+2*2^10*c.k,108332765954626+c.lower,108333151141271+c.upper)) = pointBounds38339 := by
 decide +kernel
def cuts38340 : List PrefixCut := [⟨35,178759755,178759863⟩,
⟨64,327127304,327127504⟩]
theorem checked38340 : checkPrefixCuts (2^48) 5029232641 10 Manual.Count131072.C038340.packed 64 cuts38340 = true := by
 decide +kernel
def pointBounds38340 : List (Nat × Nat × Nat) := [(5029304320,108333277670940,108333662857886)]
theorem point_links_checked38340 : (cuts38340.take 1).map (fun c => (5029232641-1+2*2^10*c.k,108333098911185+c.lower,108333484098023+c.upper)) = pointBounds38340 := by
 decide +kernel
def cuts38341 : List PrefixCut := [⟨48,241492258,241492407⟩,
⟨64,325327875,325328074⟩]
theorem checked38341 : checkPrefixCuts (2^48) 5029363713 10 Manual.Count131072.C038341.packed 64 cuts38341 = true := by
 decide +kernel
def pointBounds38341 : List (Nat × Nat × Nat) := [(5029462016,108333667530747,108334052717934)]
theorem point_links_checked38341 : (cuts38341.take 1).map (fun c => (5029363713-1+2*2^10*c.k,108333426038489+c.lower,108333811225527+c.upper)) = pointBounds38341 := by
 decide +kernel
def cuts38342 : List PrefixCut := [⟨61,313790973,313791167⟩,
⟨64,328789171,328789373⟩]
theorem checked38342 : checkPrefixCuts (2^48) 5029494785 10 Manual.Count131072.C038342.packed 64 cuts38342 = true := by
 decide +kernel
def pointBounds38342 : List (Nat × Nat × Nat) := [(5029619712,108334065157337,108334450344768)]
theorem point_links_checked38342 : (cuts38342.take 1).map (fun c => (5029494785-1+2*2^10*c.k,108333751366364+c.lower,108334136553601+c.upper)) = pointBounds38342 := by
 decide +kernel
def cuts38343 : List PrefixCut := [⟨64,327941181,327941380⟩]
theorem checked38343 : checkPrefixCuts (2^48) 5029625857 10 Manual.Count131072.C038343.packed 64 cuts38343 = true := by
 decide +kernel
def cuts38344 : List PrefixCut := [⟨10,53723339,53723374⟩,
⟨64,328828013,328828213⟩]
theorem checked38344 : checkPrefixCuts (2^48) 5029756929 10 Manual.Count131072.C038344.packed 64 cuts38344 = true := by
 decide +kernel
def pointBounds38344 : List (Nat × Nat × Nat) := [(5029777408,108334461820055,108334847007728)]
theorem point_links_checked38344 : (cuts38344.take 1).map (fun c => (5029756929-1+2*2^10*c.k,108334408096716+c.lower,108334793284354+c.upper)) = pointBounds38344 := by
 decide +kernel
def cuts38345 : List PrefixCut := [⟨23,120146564,120146634⟩,
⟨64,329211177,329211371⟩]
theorem checked38345 : checkPrefixCuts (2^48) 5029888001 10 Manual.Count131072.C038345.packed 64 cuts38345 = true := by
 decide +kernel
def pointBounds38345 : List (Nat × Nat × Nat) := [(5029935104,108334857071293,108335242259201)]
theorem point_links_checked38345 : (cuts38345.take 1).map (fun c => (5029888001-1+2*2^10*c.k,108334736924729+c.lower,108335122112567+c.upper)) = pointBounds38345 := by
 decide +kernel
def cuts38346 : List PrefixCut := [⟨36,185278937,185279048⟩,
⟨64,328139391,328139590⟩]
theorem checked38346 : checkPrefixCuts (2^48) 5030019073 10 Manual.Count131072.C038346.packed 64 cuts38346 = true := by
 decide +kernel
def pointBounds38346 : List (Nat × Nat × Nat) := [(5030092800,108335251414843,108335636602986)]
theorem point_links_checked38346 : (cuts38346.take 1).map (fun c => (5030019073-1+2*2^10*c.k,108335066135906+c.lower,108335451323938+c.upper)) = pointBounds38346 := by
 decide +kernel
def cuts38347 : List PrefixCut := [⟨49,250407551,250407703⟩,
⟨64,327067635,327067833⟩]
theorem checked38347 : checkPrefixCuts (2^48) 5030150145 10 Manual.Count131072.C038347.packed 64 cuts38347 = true := by
 decide +kernel
def pointBounds38347 : List (Nat × Nat × Nat) := [(5030250496,108335644682848,108336029871231)]
theorem point_links_checked38347 : (cuts38347.take 1).map (fun c => (5030150145-1+2*2^10*c.k,108335394275297+c.lower,108335779463528+c.upper)) = pointBounds38347 := by
 decide +kernel
def cuts38348 : List PrefixCut := [⟨62,315140738,315140931⟩,
⟨64,324764939,324765138⟩]
theorem checked38348 : checkPrefixCuts (2^48) 5030281217 10 Manual.Count131072.C038348.packed 64 cuts38348 = true := by
 decide +kernel
def pointBounds38348 : List (Nat × Nat × Nat) := [(5030408192,108336036483670,108336421672292)]
theorem point_links_checked38348 : (cuts38348.take 1).map (fun c => (5030281217-1+2*2^10*c.k,108335721342932+c.lower,108336106531361+c.upper)) = pointBounds38348 := by
 decide +kernel
def cuts38349 : List PrefixCut := [⟨64,329120884,329121082⟩]
theorem checked38349 : checkPrefixCuts (2^48) 5030412289 10 Manual.Count131072.C038349.packed 64 cuts38349 = true := by
 decide +kernel
def cuts38350 : List PrefixCut := [⟨11,57799504,57799539⟩,
⟨64,331574253,331574457⟩]
theorem checked38350 : checkPrefixCuts (2^48) 5030543361 10 Manual.Count131072.C038350.packed 64 cuts38350 = true := by
 decide +kernel
def pointBounds38350 : List (Nat × Nat × Nat) := [(5030565888,108336433028259,108336818217120)]
theorem point_links_checked38350 : (cuts38350.take 1).map (fun c => (5030543361-1+2*2^10*c.k,108336375228755+c.lower,108336760417581+c.upper)) = pointBounds38350 := by
 decide +kernel
def cuts38351 : List PrefixCut := [⟨24,120127760,120127833⟩,
⟨64,324347874,324348067⟩]
theorem checked38351 : checkPrefixCuts (2^48) 5030674433 10 Manual.Count131072.C038351.packed 64 cuts38351 = true := by
 decide +kernel
def pointBounds38351 : List (Nat × Nat × Nat) := [(5030723584,108336826930768,108337212119871)]
theorem point_links_checked38351 : (cuts38351.take 1).map (fun c => (5030674433-1+2*2^10*c.k,108336706803008+c.lower,108337091992038+c.upper)) = pointBounds38351 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000260
