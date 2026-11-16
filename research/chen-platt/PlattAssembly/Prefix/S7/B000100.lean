import PlattAssemblyKernel
import PlattCertificates.Count131072.C063200
import PlattCertificates.Count131072.C063201
import PlattCertificates.Count131072.C063202
import PlattCertificates.Count131072.C063203
import PlattCertificates.Count131072.C063204
import PlattCertificates.Count131072.C063205
import PlattCertificates.Count131072.C063206
import PlattCertificates.Count131072.C063207
import PlattCertificates.Count131072.C063208
import PlattCertificates.Count131072.C063209
import PlattCertificates.Count131072.C063210
import PlattCertificates.Count131072.C063211
import PlattCertificates.Count131072.C063212
import PlattCertificates.Count131072.C063213
import PlattCertificates.Count131072.C063214
import PlattCertificates.Count131072.C063215
import PlattCertificates.Count131072.C063216
import PlattCertificates.Count131072.C063217
import PlattCertificates.Count131072.C063218
import PlattCertificates.Count131072.C063219
import PlattCertificates.Count131072.C063220
import PlattCertificates.Count131072.C063221
import PlattCertificates.Count131072.C063222
import PlattCertificates.Count131072.C063223
import PlattCertificates.Count131072.C063224
import PlattCertificates.Count131072.C063225
import PlattCertificates.Count131072.C063226
import PlattCertificates.Count131072.C063227
import PlattCertificates.Count131072.C063228
import PlattCertificates.Count131072.C063229
import PlattCertificates.Count131072.C063230
import PlattCertificates.Count131072.C063231
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000100
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts63200 : List PrefixCut := [⟨56,171783868,171783969⟩,
⟨64,196474631,196474746⟩]
theorem checked63200 : checkPrefixCuts (2^48) 8287682561 10 Manual.Count131072.C063200.packed 64 cuts63200 = true := by
 decide +kernel
def pointBounds63200 : List (Nat × Nat × Nat) := [(8287797248,114557863387089,114558252161784)]
theorem point_links_checked63200 : (cuts63200.take 1).map (fun c => (8287682561-1+2*2^10*c.k,114557691603221+c.lower,114558080377815+c.upper)) = pointBounds63200 := by
 decide +kernel
def cuts63201 : List PrefixCut := [⟨64,195350781,195350893⟩]
theorem checked63201 : checkPrefixCuts (2^48) 8287813633 10 Manual.Count131072.C063201.packed 64 cuts63201 = true := by
 decide +kernel
def cuts63202 : List PrefixCut := [⟨55,163220100,163220192⟩,
⟨64,190253427,190253536⟩]
theorem checked63202 : checkPrefixCuts (2^48) 8287944705 10 Manual.Count131072.C063202.packed 64 cuts63202 = true := by
 decide +kernel
def pointBounds63202 : List (Nat × Nat × Nat) := [(8288057344,114558246648733,114558635423646)]
theorem point_links_checked63202 : (cuts63202.take 1).map (fun c => (8287944705-1+2*2^10*c.k,114558083428633+c.lower,114558472203454+c.upper)) = pointBounds63202 := by
 decide +kernel
def cuts63203 : List PrefixCut := [⟨64,193137117,193137231⟩]
theorem checked63203 : checkPrefixCuts (2^48) 8288075777 10 Manual.Count131072.C063203.packed 64 cuts63203 = true := by
 decide +kernel
def cuts63204 : List PrefixCut := [⟨54,166848754,166848846⟩,
⟨64,196462219,196462329⟩]
theorem checked63204 : checkPrefixCuts (2^48) 8288206849 10 Manual.Count131072.C063204.packed 64 cuts63204 = true := by
 decide +kernel
def pointBounds63204 : List (Nat × Nat × Nat) := [(8288317440,114558633667931,114559022443067)]
theorem point_links_checked63204 : (cuts63204.take 1).map (fun c => (8288206849-1+2*2^10*c.k,114558466819177+c.lower,114558855594221+c.upper)) = pointBounds63204 := by
 decide +kernel
def cuts63205 : List PrefixCut := [⟨64,192655564,192655673⟩]
theorem checked63205 : checkPrefixCuts (2^48) 8288337921 10 Manual.Count131072.C063205.packed 64 cuts63205 = true := by
 decide +kernel
def cuts63206 : List PrefixCut := [⟨53,163515455,163515545⟩,
⟨64,197814375,197814487⟩]
theorem checked63206 : checkPrefixCuts (2^48) 8288468993 10 Manual.Count131072.C063206.packed 64 cuts63206 = true := by
 decide +kernel
def pointBounds63206 : List (Nat × Nat × Nat) := [(8288577536,114559019452415,114559408227768)]
theorem point_links_checked63206 : (cuts63206.take 1).map (fun c => (8288468993-1+2*2^10*c.k,114558855936960+c.lower,114559244712223+c.upper)) = pointBounds63206 := by
 decide +kernel
def cuts63207 : List PrefixCut := [⟨64,193192828,193192940⟩]
theorem checked63207 : checkPrefixCuts (2^48) 8288600065 10 Manual.Count131072.C063207.packed 64 cuts63207 = true := by
 decide +kernel
def cuts63208 : List PrefixCut := [⟨52,156616719,156616810⟩,
⟨64,193902886,193902998⟩]
theorem checked63208 : checkPrefixCuts (2^48) 8288731137 10 Manual.Count131072.C063208.packed 64 cuts63208 = true := by
 decide +kernel
def pointBounds63208 : List (Nat × Nat × Nat) := [(8288837632,114559403560882,114559792336460)]
theorem point_links_checked63208 : (cuts63208.take 1).map (fun c => (8288731137-1+2*2^10*c.k,114559246944163+c.lower,114559635719650+c.upper)) = pointBounds63208 := by
 decide +kernel
def cuts63209 : List PrefixCut := [⟨64,195326055,195326168⟩]
theorem checked63209 : checkPrefixCuts (2^48) 8288862209 10 Manual.Count131072.C063209.packed 64 cuts63209 = true := by
 decide +kernel
def cuts63210 : List PrefixCut := [⟨51,156204290,156204384⟩,
⟨64,195424841,195424957⟩]
theorem checked63210 : checkPrefixCuts (2^48) 8288993281 10 Manual.Count131072.C063210.packed 64 cuts63210 = true := by
 decide +kernel
def pointBounds63210 : List (Nat × Nat × Nat) := [(8289097728,114559792377394,114560181153200)]
theorem point_links_checked63210 : (cuts63210.take 1).map (fun c => (8288993281-1+2*2^10*c.k,114559636173104+c.lower,114560024948816+c.upper)) = pointBounds63210 := by
 decide +kernel
def cuts63211 : List PrefixCut := [⟨64,196066923,196067038⟩]
theorem checked63211 : checkPrefixCuts (2^48) 8289124353 10 Manual.Count131072.C063211.packed 64 cuts63211 = true := by
 decide +kernel
def cuts63212 : List PrefixCut := [⟨50,152260436,152260525⟩,
⟨64,194569757,194569873⟩]
theorem checked63212 : checkPrefixCuts (2^48) 8289255425 10 Manual.Count131072.C063212.packed 64 cuts63212 = true := by
 decide +kernel
def pointBounds63212 : List (Nat × Nat × Nat) := [(8289357824,114560179925304,114560568701336)]
theorem point_links_checked63212 : (cuts63212.take 1).map (fun c => (8289255425-1+2*2^10*c.k,114560027664868+c.lower,114560416440811+c.upper)) = pointBounds63212 := by
 decide +kernel
def cuts63213 : List PrefixCut := [⟨64,195721179,195721294⟩]
theorem checked63213 : checkPrefixCuts (2^48) 8289386497 10 Manual.Count131072.C063213.packed 64 cuts63213 = true := by
 decide +kernel
def cuts63214 : List PrefixCut := [⟨49,149165710,149165795⟩,
⟨64,194224060,194224172⟩]
theorem checked63214 : checkPrefixCuts (2^48) 8289517569 10 Manual.Count131072.C063214.packed 64 cuts63214 = true := by
 decide +kernel
def pointBounds63214 : List (Nat × Nat × Nat) := [(8289617920,114560567121514,114560955897773)]
theorem point_links_checked63214 : (cuts63214.take 1).map (fun c => (8289517569-1+2*2^10*c.k,114560417955804+c.lower,114560806731978+c.upper)) = pointBounds63214 := by
 decide +kernel
def cuts63215 : List PrefixCut := [⟨64,191606453,191606569⟩]
theorem checked63215 : checkPrefixCuts (2^48) 8289648641 10 Manual.Count131072.C063215.packed 64 cuts63215 = true := by
 decide +kernel
def cuts63216 : List PrefixCut := [⟨48,147497246,147497326⟩,
⟨64,196051435,196051544⟩]
theorem checked63216 : checkPrefixCuts (2^48) 8289779713 10 Manual.Count131072.C063216.packed 64 cuts63216 = true := by
 decide +kernel
def pointBounds63216 : List (Nat × Nat × Nat) := [(8289878016,114560951283563,114561340060045)]
theorem point_links_checked63216 : (cuts63216.take 1).map (fun c => (8289779713-1+2*2^10*c.k,114560803786317+c.lower,114561192562719+c.upper)) = pointBounds63216 := by
 decide +kernel
def cuts63217 : List PrefixCut := [⟨64,195810670,195810772⟩]
theorem checked63217 : checkPrefixCuts (2^48) 8289910785 10 Manual.Count131072.C063217.packed 64 cuts63217 = true := by
 decide +kernel
def cuts63218 : List PrefixCut := [⟨47,143689845,143689929⟩,
⟨64,192921559,192921676⟩]
theorem checked63218 : checkPrefixCuts (2^48) 8290041857 10 Manual.Count131072.C063218.packed 64 cuts63218 = true := by
 decide +kernel
def pointBounds63218 : List (Nat × Nat × Nat) := [(8290138112,114561339338267,114561728114964)]
theorem point_links_checked63218 : (cuts63218.take 1).map (fun c => (8290041857-1+2*2^10*c.k,114561195648422+c.lower,114561584425035+c.upper)) = pointBounds63218 := by
 decide +kernel
def cuts63219 : List PrefixCut := [⟨64,194038935,194039047⟩]
theorem checked63219 : checkPrefixCuts (2^48) 8290172929 10 Manual.Count131072.C063219.packed 64 cuts63219 = true := by
 decide +kernel
def cuts63220 : List PrefixCut := [⟨46,141817960,141818044⟩,
⟨64,199128666,199128783⟩]
theorem checked63220 : checkPrefixCuts (2^48) 8290304001 10 Manual.Count131072.C063220.packed 64 cuts63220 = true := by
 decide +kernel
def pointBounds63220 : List (Nat × Nat × Nat) := [(8290398208,114561724426876,114562113203802)]
theorem point_links_checked63220 : (cuts63220.take 1).map (fun c => (8290304001-1+2*2^10*c.k,114561582608916+c.lower,114561971385758+c.upper)) = pointBounds63220 := by
 decide +kernel
def cuts63221 : List PrefixCut := [⟨64,194372306,194372416⟩]
theorem checked63221 : checkPrefixCuts (2^48) 8290435073 10 Manual.Count131072.C063221.packed 64 cuts63221 = true := by
 decide +kernel
def cuts63222 : List PrefixCut := [⟨45,135430696,135430777⟩,
⟨64,190295142,190295253⟩]
theorem checked63222 : checkPrefixCuts (2^48) 8290566145 10 Manual.Count131072.C063222.packed 64 cuts63222 = true := by
 decide +kernel
def pointBounds63222 : List (Nat × Nat × Nat) := [(8290658304,114562111540584,114562500317734)]
theorem point_links_checked63222 : (cuts63222.take 1).map (fun c => (8290566145-1+2*2^10*c.k,114561976109888+c.lower,114562364886957+c.upper)) = pointBounds63222 := by
 decide +kernel
def cuts63223 : List PrefixCut := [⟨64,195826043,195826152⟩]
theorem checked63223 : checkPrefixCuts (2^48) 8290697217 10 Manual.Count131072.C063223.packed 64 cuts63223 = true := by
 decide +kernel
def cuts63224 : List PrefixCut := [⟨44,136682576,136682652⟩,
⟨64,198606830,198606944⟩]
theorem checked63224 : checkPrefixCuts (2^48) 8290828289 10 Manual.Count131072.C063224.packed 64 cuts63224 = true := by
 decide +kernel
def pointBounds63224 : List (Nat × Nat × Nat) := [(8290918400,114562498913649,114562887691014)]
theorem point_links_checked63224 : (cuts63224.take 1).map (fun c => (8290828289-1+2*2^10*c.k,114562362231073+c.lower,114562751008362+c.upper)) = pointBounds63224 := by
 decide +kernel
def cuts63225 : List PrefixCut := [⟨64,192628603,192628714⟩]
theorem checked63225 : checkPrefixCuts (2^48) 8290959361 10 Manual.Count131072.C063225.packed 64 cuts63225 = true := by
 decide +kernel
def cuts63226 : List PrefixCut := [⟨43,131416189,131416262⟩,
⟨64,195748849,195748957⟩]
theorem checked63226 : checkPrefixCuts (2^48) 8291090433 10 Manual.Count131072.C063226.packed 64 cuts63226 = true := by
 decide +kernel
def pointBounds63226 : List (Nat × Nat × Nat) := [(8291178496,114562884882695,114563273660282)]
theorem point_links_checked63226 : (cuts63226.take 1).map (fun c => (8291090433-1+2*2^10*c.k,114562753466506+c.lower,114563142244020+c.upper)) = pointBounds63226 := by
 decide +kernel
def cuts63227 : List PrefixCut := [⟨64,196322869,196322982⟩]
theorem checked63227 : checkPrefixCuts (2^48) 8291221505 10 Manual.Count131072.C063227.packed 64 cuts63227 = true := by
 decide +kernel
def cuts63228 : List PrefixCut := [⟨42,124826175,124826250⟩,
⟨64,190989975,190990091⟩]
theorem checked63228 : checkPrefixCuts (2^48) 8291352577 10 Manual.Count131072.C063228.packed 64 cuts63228 = true := by
 decide +kernel
def pointBounds63228 : List (Nat × Nat × Nat) := [(8291438592,114563270364399,114563659142209)]
theorem point_links_checked63228 : (cuts63228.take 1).map (fun c => (8291352577-1+2*2^10*c.k,114563145538224+c.lower,114563534315959+c.upper)) = pointBounds63228 := by
 decide +kernel
def cuts63229 : List PrefixCut := [⟨64,194517463,194517574⟩]
theorem checked63229 : checkPrefixCuts (2^48) 8291483649 10 Manual.Count131072.C063229.packed 64 cuts63229 = true := by
 decide +kernel
def cuts63230 : List PrefixCut := [⟨41,124245148,124245221⟩,
⟨64,193631782,193631896⟩]
theorem checked63230 : checkPrefixCuts (2^48) 8291614721 10 Manual.Count131072.C063230.packed 64 cuts63230 = true := by
 decide +kernel
def pointBounds63230 : List (Nat × Nat × Nat) := [(8291698688,114563655290810,114564044068845)]
theorem point_links_checked63230 : (cuts63230.take 1).map (fun c => (8291614721-1+2*2^10*c.k,114563531045662+c.lower,114563919823624+c.upper)) = pointBounds63230 := by
 decide +kernel
def cuts63231 : List PrefixCut := [⟨64,194681064,194681173⟩]
theorem checked63231 : checkPrefixCuts (2^48) 8291745793 10 Manual.Count131072.C063231.packed 64 cuts63231 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000100
